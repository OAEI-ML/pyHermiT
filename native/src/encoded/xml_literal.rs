//! Bounded XML C14N 2.0 subset used by the scalar `rdf:XMLLiteral` contract.
//!
//! The input is wrapped in a private element so XML fragments may contain text and
//! multiple top-level nodes. DTDs and entity declarations are rejected before the
//! event reader runs; only predefined and numeric character references are decoded.
//! The serializer intentionally mirrors `xml.etree.ElementTree.canonicalize` with
//! comments enabled and prefix rewriting disabled.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::cmp::Ordering;
use std::mem::size_of;
use std::str;

use quick_xml::events::{BytesStart, Event};
use quick_xml::Reader;

use super::named_classes::PhaseBudget;
use super::{EncodedResult, EncodedValidationError};

const WRAPPER: &str = "pyhermit-xml-literal-wrapper";
const XML_NAMESPACE: &str = "http://www.w3.org/XML/1998/namespace";
const XMLNS_NAMESPACE: &str = "http://www.w3.org/2000/xmlns/";

const PREFERRED_NAMESPACES: &[(&str, &str)] = &[
    (XML_NAMESPACE, "xml"),
    ("http://www.w3.org/1999/xhtml", "html"),
    ("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf"),
    ("http://schemas.xmlsoap.org/wsdl/", "wsdl"),
    ("http://www.w3.org/2001/XMLSchema", "xs"),
    ("http://www.w3.org/2001/XMLSchema-instance", "xsi"),
    ("http://purl.org/dc/elements/1.1/", "dc"),
];

#[derive(Clone, Debug, Eq, PartialEq)]
struct NamespaceBinding {
    uri: String,
    prefix: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ExpandedName {
    uri: String,
    local: String,
    clark: String,
    namespace_sort: String,
}

impl Ord for ExpandedName {
    fn cmp(&self, other: &Self) -> Ordering {
        self.clark.cmp(&other.clark)
    }
}

impl PartialOrd for ExpandedName {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CanonicalAttribute {
    name: ExpandedName,
    value: String,
}

type RawAttributes = Vec<(String, String)>;

struct Canonicalizer<'a> {
    budget: &'a mut PhaseBudget,
    output: String,
    scope_stack: Vec<Vec<NamespaceBinding>>,
    source_namespace_stack: Vec<Vec<NamespaceBinding>>,
    declared_namespace_stack: Vec<Vec<NamespaceBinding>>,
    elements: Vec<ExpandedName>,
    nodes: usize,
    saw_wrapper: bool,
}

/// Validate and canonicalize one RDF XML literal fragment.
pub(super) fn canonicalize(lexical: &str, budget: &mut PhaseBudget) -> EncodedResult<String> {
    if contains_forbidden_declaration(lexical) {
        return invalid_xml();
    }
    budget.claim_work(lexical.len())?;
    let wrapper_overhead = WRAPPER
        .len()
        .checked_mul(2)
        .and_then(|value| value.checked_add(5))
        .ok_or_else(|| EncodedValidationError::resource("XML wrapper length overflowed"))?;
    let enclosed_len = lexical
        .len()
        .checked_add(wrapper_overhead)
        .ok_or_else(|| EncodedValidationError::resource("XML literal length overflowed"))?;
    budget.claim_owned(enclosed_len)?;
    let mut enclosed = String::new();
    enclosed
        .try_reserve_exact(enclosed_len)
        .map_err(|_| EncodedValidationError::resource("XML wrapper allocation failed"))?;
    enclosed.push('<');
    enclosed.push_str(WRAPPER);
    enclosed.push('>');
    enclosed.push_str(lexical);
    enclosed.push_str("</");
    enclosed.push_str(WRAPPER);
    enclosed.push('>');

    let mut canonicalizer = Canonicalizer::new(budget)?;
    let mut reader = Reader::from_str(&enclosed);
    reader.config_mut().check_comments = true;
    reader.config_mut().expand_empty_elements = true;
    loop {
        let event = reader.read_event().map_err(|_| invalid_xml_error())?;
        match event {
            Event::Start(start) => canonicalizer.start(&start)?,
            Event::Empty(start) => {
                canonicalizer.start(&start)?;
                canonicalizer.end()?;
            }
            Event::End(_) => canonicalizer.end()?,
            Event::Text(text) => {
                let value = decode_xml_value(text.as_ref(), false, canonicalizer.budget)?;
                canonicalizer.text(&value)?;
            }
            Event::CData(data) => {
                let value = normalize_markup_data(data.as_ref(), canonicalizer.budget)?;
                canonicalizer.text(&value)?;
            }
            Event::Comment(comment) => {
                let value = normalize_markup_data(comment.as_ref(), canonicalizer.budget)?;
                canonicalizer.comment(&value)?;
            }
            Event::PI(instruction) => {
                let target =
                    str::from_utf8(instruction.target()).map_err(|_| invalid_xml_error())?;
                let content = normalize_markup_data(instruction.content(), canonicalizer.budget)?;
                canonicalizer.processing_instruction(target, &content)?;
            }
            Event::Decl(_) | Event::DocType(_) => return invalid_xml(),
            Event::Eof => break,
        }
    }
    canonicalizer.finish()
}

impl<'a> Canonicalizer<'a> {
    fn new(budget: &'a mut PhaseBudget) -> EncodedResult<Self> {
        let mut preferred = Vec::new();
        preferred
            .try_reserve_exact(PREFERRED_NAMESPACES.len())
            .map_err(|_| {
                EncodedValidationError::resource("XML preferred-namespace allocation failed")
            })?;
        for (uri, prefix) in PREFERRED_NAMESPACES {
            preferred.push(namespace_binding(uri, prefix, budget)?);
        }
        let xml = namespace_binding(XML_NAMESPACE, "xml", budget)?;
        budget.claim_owned(
            5_usize
                .checked_mul(size_of::<Vec<NamespaceBinding>>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("XML namespace stack size overflowed")
                })?,
        )?;
        Ok(Self {
            budget,
            output: String::new(),
            scope_stack: vec![vec![xml.clone()]],
            source_namespace_stack: vec![preferred, Vec::new()],
            declared_namespace_stack: vec![vec![xml]],
            elements: Vec::new(),
            nodes: 0,
            saw_wrapper: false,
        })
    }

    fn start(&mut self, start: &BytesStart<'_>) -> EncodedResult<()> {
        let fragment_depth = self.elements.len();
        if fragment_depth > self.budget.max_xml_depth() {
            return Err(EncodedValidationError::resource(
                "XML literal exceeds the configured nesting-depth limit",
            ));
        }
        if fragment_depth != 0 {
            self.claim_node()?;
        } else if self.saw_wrapper {
            return invalid_xml();
        }

        let (declarations, raw_attributes) = self.attributes(start)?;
        Self::validate_namespace_declarations(&declarations)?;
        self.budget
            .claim_owned(size_of::<Vec<NamespaceBinding>>())?;
        self.scope_stack.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("XML namespace-scope allocation failed")
        })?;
        self.scope_stack.push(declarations.clone());
        let qualified_name = start.name();
        let raw_name = str::from_utf8(qualified_name.as_ref()).map_err(|_| invalid_xml_error())?;
        let name = self.expand_name(raw_name, true)?;

        if fragment_depth == 0 {
            if name.uri.is_empty() && name.local == WRAPPER && raw_attributes.is_empty() {
                self.saw_wrapper = true;
            } else {
                return invalid_xml();
            }
        }

        let mut attributes = Vec::new();
        self.budget.claim_owned(
            raw_attributes
                .len()
                .checked_mul(size_of::<CanonicalAttribute>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("XML attribute allocation overflowed")
                })?,
        )?;
        attributes
            .try_reserve_exact(raw_attributes.len())
            .map_err(|_| EncodedValidationError::resource("XML attribute allocation failed"))?;
        for (raw_attribute_name, value) in raw_attributes {
            let expanded = self.expand_name(&raw_attribute_name, false)?;
            attributes.push(CanonicalAttribute {
                name: expanded,
                value,
            });
        }
        self.budget.claim_work(attributes.len())?;
        attributes.sort_by(|left, right| left.name.cmp(&right.name));
        if attributes
            .windows(2)
            .any(|pair| pair[0].name == pair[1].name)
        {
            return invalid_xml();
        }

        let source_frame = self
            .source_namespace_stack
            .last_mut()
            .ok_or_else(|| EncodedValidationError::invariant("XML source namespace stack empty"))?;
        source_frame.try_reserve(declarations.len()).map_err(|_| {
            EncodedValidationError::resource("XML source namespace allocation failed")
        })?;
        source_frame.extend(declarations);

        self.budget
            .claim_owned(size_of::<Vec<NamespaceBinding>>())?;
        self.declared_namespace_stack.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("XML declared-namespace stack allocation failed")
        })?;
        self.declared_namespace_stack.push(Vec::new());

        let mut used_names = Vec::new();
        let used_count = attributes
            .len()
            .checked_add(1)
            .ok_or_else(|| EncodedValidationError::resource("XML used-name count overflowed"))?;
        self.budget.claim_owned(
            used_count
                .checked_mul(size_of::<ExpandedName>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("XML name allocation overflowed")
                })?,
        )?;
        used_names
            .try_reserve_exact(used_count)
            .map_err(|_| EncodedValidationError::resource("XML name allocation failed"))?;
        used_names.push(name.clone());
        used_names.extend(attributes.iter().map(|attribute| attribute.name.clone()));
        self.budget.claim_work(used_names.len())?;
        used_names.sort_by(compare_namespace_names);
        used_names.dedup();

        let mut resolved = Vec::new();
        self.budget.claim_owned(
            used_names
                .len()
                .checked_mul(size_of::<(ExpandedName, String)>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("XML resolved-name allocation overflowed")
                })?,
        )?;
        resolved
            .try_reserve_exact(used_names.len())
            .map_err(|_| EncodedValidationError::resource("XML resolved-name allocation failed"))?;
        for used in used_names {
            let qualified = self.qualified_name(&used)?;
            resolved.push((used, qualified));
        }

        let element_name = resolved_name(&resolved, &name)?;
        self.push_output("<")?;
        self.push_output(element_name)?;
        let mut namespace_attributes = self
            .declared_namespace_stack
            .last()
            .ok_or_else(|| EncodedValidationError::invariant("XML declared namespace missing"))?
            .iter()
            .map(|binding| {
                let key = if binding.prefix.is_empty() {
                    "xmlns".to_owned()
                } else {
                    format!("xmlns:{}", binding.prefix)
                };
                (key, binding.uri.clone())
            })
            .collect::<Vec<_>>();
        self.budget.claim_work(namespace_attributes.len())?;
        namespace_attributes.sort();
        for (attribute_name, value) in namespace_attributes {
            self.write_attribute(&attribute_name, &value)?;
        }
        for attribute in &attributes {
            let attribute_name = if attribute.name.uri.is_empty() {
                attribute.name.local.as_str()
            } else {
                resolved_name(&resolved, &attribute.name)?
            };
            self.write_attribute(attribute_name, &attribute.value)?;
        }
        self.push_output(">")?;

        self.budget.claim_owned(size_of::<ExpandedName>())?;
        self.elements
            .try_reserve(1)
            .map_err(|_| EncodedValidationError::resource("XML element-stack allocation failed"))?;
        self.elements.push(name);
        self.budget
            .claim_owned(size_of::<Vec<NamespaceBinding>>())?;
        self.source_namespace_stack.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("XML source namespace stack allocation failed")
        })?;
        self.source_namespace_stack.push(Vec::new());
        Ok(())
    }

    fn end(&mut self) -> EncodedResult<()> {
        let name = self.elements.pop().ok_or_else(invalid_xml_error)?;
        let qualified = self.qualified_name(&name)?;
        self.push_output("</")?;
        self.push_output(&qualified)?;
        self.push_output(">")?;
        self.scope_stack.pop().ok_or_else(invalid_xml_error)?;
        self.source_namespace_stack
            .pop()
            .ok_or_else(invalid_xml_error)?;
        self.declared_namespace_stack
            .pop()
            .ok_or_else(invalid_xml_error)?;
        Ok(())
    }

    fn text(&mut self, value: &str) -> EncodedResult<()> {
        if self.elements.is_empty() {
            if value.chars().all(char::is_whitespace) {
                return Ok(());
            }
            return invalid_xml();
        }
        self.write_canonical_text(value)
    }

    fn comment(&mut self, value: &str) -> EncodedResult<()> {
        if self.elements.is_empty() {
            return invalid_xml();
        }
        self.claim_node()?;
        self.push_output("<!--")?;
        self.write_canonical_text(value)?;
        self.push_output("-->")
    }

    fn processing_instruction(&mut self, target: &str, content: &str) -> EncodedResult<()> {
        if self.elements.is_empty() || !valid_ncname(target) || target.eq_ignore_ascii_case("xml") {
            return invalid_xml();
        }
        self.claim_node()?;
        let data = content.trim_start_matches(is_xml_space);
        self.push_output("<?")?;
        self.push_output(target)?;
        if !data.is_empty() {
            self.push_output(" ")?;
            self.write_canonical_text(data)?;
        }
        self.push_output("?>")
    }

    fn finish(self) -> EncodedResult<String> {
        if !self.saw_wrapper || !self.elements.is_empty() {
            return invalid_xml();
        }
        let prefix = format!("<{WRAPPER}>");
        let suffix = format!("</{WRAPPER}>");
        let Some(without_prefix) = self.output.strip_prefix(&prefix) else {
            return invalid_xml();
        };
        let Some(fragment) = without_prefix.strip_suffix(&suffix) else {
            return invalid_xml();
        };
        self.budget.claim_owned(fragment.len())?;
        let mut canonical = String::new();
        canonical.try_reserve_exact(fragment.len()).map_err(|_| {
            EncodedValidationError::resource("XML canonical fragment allocation failed")
        })?;
        canonical.push_str(fragment);
        Ok(canonical)
    }

    fn attributes(
        &mut self,
        start: &BytesStart<'_>,
    ) -> EncodedResult<(Vec<NamespaceBinding>, RawAttributes)> {
        let mut declarations = Vec::new();
        let mut attributes = Vec::new();
        for attribute in start.attributes() {
            let attribute = attribute.map_err(|_| invalid_xml_error())?;
            let raw_name =
                str::from_utf8(attribute.key.as_ref()).map_err(|_| invalid_xml_error())?;
            let value = decode_xml_value(attribute.value.as_ref(), true, self.budget)?;
            if raw_name == "xmlns" {
                declarations.push(namespace_binding(&value, "", self.budget)?);
            } else if let Some(prefix) = raw_name.strip_prefix("xmlns:") {
                if !valid_ncname(prefix) {
                    return invalid_xml();
                }
                declarations.push(namespace_binding(&value, prefix, self.budget)?);
            } else {
                if !valid_qname(raw_name) {
                    return invalid_xml();
                }
                self.budget.claim_owned(raw_name.len())?;
                attributes.push((raw_name.to_owned(), value));
            }
        }
        Ok((declarations, attributes))
    }

    fn validate_namespace_declarations(declarations: &[NamespaceBinding]) -> EncodedResult<()> {
        for (index, declaration) in declarations.iter().enumerate() {
            if declarations[..index]
                .iter()
                .any(|prior| prior.prefix == declaration.prefix)
            {
                return invalid_xml();
            }
            if declaration.prefix == "xmlns"
                || declaration.uri == XMLNS_NAMESPACE
                || (declaration.prefix == "xml" && declaration.uri != XML_NAMESPACE)
                || (declaration.prefix != "xml" && declaration.uri == XML_NAMESPACE)
                || (!declaration.prefix.is_empty() && declaration.uri.is_empty())
            {
                return invalid_xml();
            }
        }
        Ok(())
    }

    fn expand_name(&mut self, raw: &str, use_default: bool) -> EncodedResult<ExpandedName> {
        if !valid_qname(raw) {
            return invalid_xml();
        }
        let (prefix, local) = raw
            .split_once(':')
            .map_or((None, raw), |(prefix, local)| (Some(prefix), local));
        let uri = match prefix {
            Some(prefix) => self
                .lookup_scope_prefix(prefix)
                .ok_or_else(invalid_xml_error)?,
            None if use_default => self.lookup_scope_prefix("").unwrap_or_default(),
            None => String::new(),
        };
        expanded_name(&uri, local, self.budget)
    }

    fn lookup_scope_prefix(&self, prefix: &str) -> Option<String> {
        self.scope_stack
            .iter()
            .rev()
            .flat_map(|frame| frame.iter().rev())
            .find(|binding| binding.prefix == prefix)
            .and_then(|binding| (!binding.uri.is_empty()).then(|| binding.uri.clone()))
    }

    fn qualified_name(&mut self, name: &ExpandedName) -> EncodedResult<String> {
        let mut seen_prefixes = Vec::<String>::new();
        for frame in self.declared_namespace_stack.iter().rev() {
            for binding in frame {
                let seen = seen_prefixes.iter().any(|prefix| prefix == &binding.prefix);
                if binding.uri == name.uri && !seen {
                    return qualified(&binding.prefix, &name.local, self.budget);
                }
                if !seen {
                    seen_prefixes.push(binding.prefix.clone());
                }
            }
        }
        if name.uri.is_empty() && !seen_prefixes.iter().any(String::is_empty) {
            return qualified("", &name.local, self.budget);
        }
        for frame in self.source_namespace_stack.iter().rev() {
            for binding in frame {
                if binding.uri == name.uri {
                    let selected = binding.clone();
                    let declared = self.declared_namespace_stack.last_mut().ok_or_else(|| {
                        EncodedValidationError::invariant("XML declared namespace stack empty")
                    })?;
                    self.budget.claim_owned(size_of::<NamespaceBinding>())?;
                    declared.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "XML namespace declaration allocation failed",
                        )
                    })?;
                    declared.push(selected.clone());
                    return qualified(&selected.prefix, &name.local, self.budget);
                }
            }
        }
        if name.uri.is_empty() {
            qualified("", &name.local, self.budget)
        } else {
            invalid_xml()
        }
    }

    fn write_attribute(&mut self, name: &str, value: &str) -> EncodedResult<()> {
        self.push_output(" ")?;
        self.push_output(name)?;
        self.push_output("=\"")?;
        for character in value.chars() {
            match character {
                '&' => self.push_output("&amp;")?,
                '<' => self.push_output("&lt;")?,
                '"' => self.push_output("&quot;")?,
                '\t' => self.push_output("&#x9;")?,
                '\n' => self.push_output("&#xA;")?,
                '\r' => self.push_output("&#xD;")?,
                value => self.push_character(value)?,
            }
        }
        self.push_output("\"")
    }

    fn write_canonical_text(&mut self, value: &str) -> EncodedResult<()> {
        for character in value.chars() {
            match character {
                '&' => self.push_output("&amp;")?,
                '<' => self.push_output("&lt;")?,
                '>' => self.push_output("&gt;")?,
                '\r' => self.push_output("&#xD;")?,
                value => self.push_character(value)?,
            }
        }
        Ok(())
    }

    fn push_character(&mut self, value: char) -> EncodedResult<()> {
        let mut encoded = [0_u8; 4];
        self.push_output(value.encode_utf8(&mut encoded))
    }

    fn push_output(&mut self, value: &str) -> EncodedResult<()> {
        self.budget.claim_owned(value.len())?;
        self.output.try_reserve(value.len()).map_err(|_| {
            EncodedValidationError::resource("XML canonical output allocation failed")
        })?;
        self.output.push_str(value);
        Ok(())
    }

    fn claim_node(&mut self) -> EncodedResult<()> {
        self.nodes = self
            .nodes
            .checked_add(1)
            .ok_or_else(|| EncodedValidationError::resource("XML node count overflowed"))?;
        if self.nodes > self.budget.max_xml_nodes() {
            return Err(EncodedValidationError::resource(
                "XML literal exceeds the configured node limit",
            ));
        }
        self.budget.claim_work(1)
    }
}

fn namespace_binding(
    uri: &str,
    prefix: &str,
    budget: &mut PhaseBudget,
) -> EncodedResult<NamespaceBinding> {
    let bytes = uri
        .len()
        .checked_add(prefix.len())
        .and_then(|value| value.checked_add(size_of::<NamespaceBinding>()))
        .ok_or_else(|| EncodedValidationError::resource("XML namespace size overflowed"))?;
    budget.claim_owned(bytes)?;
    Ok(NamespaceBinding {
        uri: uri.to_owned(),
        prefix: prefix.to_owned(),
    })
}

fn expanded_name(uri: &str, local: &str, budget: &mut PhaseBudget) -> EncodedResult<ExpandedName> {
    let clark = if uri.is_empty() {
        local.to_owned()
    } else {
        format!("{{{uri}}}{local}")
    };
    let namespace_sort = if uri.is_empty() {
        local.to_owned()
    } else {
        format!("{{{uri}")
    };
    let bytes = uri
        .len()
        .checked_add(local.len())
        .and_then(|value| value.checked_add(clark.len()))
        .and_then(|value| value.checked_add(namespace_sort.len()))
        .and_then(|value| value.checked_add(size_of::<ExpandedName>()))
        .ok_or_else(|| EncodedValidationError::resource("XML expanded-name size overflowed"))?;
    budget.claim_owned(bytes)?;
    Ok(ExpandedName {
        uri: uri.to_owned(),
        local: local.to_owned(),
        clark,
        namespace_sort,
    })
}

fn qualified(prefix: &str, local: &str, budget: &mut PhaseBudget) -> EncodedResult<String> {
    let length = prefix
        .len()
        .checked_add(local.len())
        .and_then(|value| value.checked_add(usize::from(!prefix.is_empty())))
        .ok_or_else(|| EncodedValidationError::resource("XML qualified-name size overflowed"))?;
    budget.claim_owned(length)?;
    let mut value = String::new();
    value
        .try_reserve_exact(length)
        .map_err(|_| EncodedValidationError::resource("XML qualified-name allocation failed"))?;
    if !prefix.is_empty() {
        value.push_str(prefix);
        value.push(':');
    }
    value.push_str(local);
    Ok(value)
}

fn compare_namespace_names(left: &ExpandedName, right: &ExpandedName) -> Ordering {
    left.namespace_sort
        .cmp(&right.namespace_sort)
        .then_with(|| left.local.cmp(&right.local))
}

fn resolved_name<'a>(
    names: &'a [(ExpandedName, String)],
    target: &ExpandedName,
) -> EncodedResult<&'a str> {
    names
        .iter()
        .find(|(name, _)| name == target)
        .map(|(_, value)| value.as_str())
        .ok_or_else(|| EncodedValidationError::invariant("XML qualified name disappeared"))
}

fn decode_xml_value(
    raw: &[u8],
    attribute: bool,
    budget: &mut PhaseBudget,
) -> EncodedResult<String> {
    let raw = str::from_utf8(raw).map_err(|_| invalid_xml_error())?;
    budget.claim_work(raw.len())?;
    budget.claim_owned(raw.len())?;
    let mut decoded = String::new();
    decoded
        .try_reserve_exact(raw.len())
        .map_err(|_| EncodedValidationError::resource("XML value allocation failed"))?;
    let bytes = raw.as_bytes();
    let mut index = 0_usize;
    while index < bytes.len() {
        if bytes[index] == b'&' {
            let Some(relative_end) = bytes[index + 1..].iter().position(|value| *value == b';')
            else {
                return invalid_xml();
            };
            let end = index
                .checked_add(relative_end)
                .and_then(|value| value.checked_add(1))
                .ok_or_else(|| EncodedValidationError::resource("XML reference overflowed"))?;
            let body = &raw[index + 1..end];
            decoded.push(decode_reference(body)?);
            index = end
                .checked_add(1)
                .ok_or_else(|| EncodedValidationError::resource("XML reference overflowed"))?;
            continue;
        }
        let tail = &raw[index..];
        let character = tail.chars().next().ok_or_else(invalid_xml_error)?;
        let width = character.len_utf8();
        if character == '\r' {
            let following = index.checked_add(width).ok_or_else(|| {
                EncodedValidationError::resource("XML line-ending index overflowed")
            })?;
            index = if bytes.get(following) == Some(&b'\n') {
                following.checked_add(1).ok_or_else(|| {
                    EncodedValidationError::resource("XML line-ending index overflowed")
                })?
            } else {
                following
            };
            decoded.push(if attribute { ' ' } else { '\n' });
            continue;
        }
        if !is_xml_character(character) || character == '<' {
            return invalid_xml();
        }
        decoded.push(if attribute && matches!(character, '\t' | '\n') {
            ' '
        } else {
            character
        });
        index = index
            .checked_add(width)
            .ok_or_else(|| EncodedValidationError::resource("XML value index overflowed"))?;
    }
    Ok(decoded)
}

fn normalize_markup_data(raw: &[u8], budget: &mut PhaseBudget) -> EncodedResult<String> {
    let raw = str::from_utf8(raw).map_err(|_| invalid_xml_error())?;
    budget.claim_work(raw.len())?;
    budget.claim_owned(raw.len())?;
    let mut normalized = String::new();
    normalized
        .try_reserve_exact(raw.len())
        .map_err(|_| EncodedValidationError::resource("XML markup allocation failed"))?;
    let mut characters = raw.chars().peekable();
    while let Some(character) = characters.next() {
        if character == '\r' {
            if characters.peek() == Some(&'\n') {
                characters.next();
            }
            normalized.push('\n');
        } else if is_xml_character(character) {
            normalized.push(character);
        } else {
            return invalid_xml();
        }
    }
    Ok(normalized)
}

fn decode_reference(value: &str) -> EncodedResult<char> {
    let character = match value {
        "amp" => '&',
        "lt" => '<',
        "gt" => '>',
        "apos" => '\'',
        "quot" => '"',
        value => {
            let codepoint = if let Some(hexadecimal) = value.strip_prefix("#x") {
                if hexadecimal.is_empty()
                    || !hexadecimal.bytes().all(|value| value.is_ascii_hexdigit())
                {
                    return invalid_xml();
                }
                u32::from_str_radix(hexadecimal, 16).map_err(|_| invalid_xml_error())?
            } else if let Some(decimal) = value.strip_prefix('#') {
                if decimal.is_empty() || !decimal.bytes().all(|value| value.is_ascii_digit()) {
                    return invalid_xml();
                }
                decimal.parse::<u32>().map_err(|_| invalid_xml_error())?
            } else {
                return invalid_xml();
            };
            char::from_u32(codepoint).ok_or_else(invalid_xml_error)?
        }
    };
    if is_xml_character(character) {
        Ok(character)
    } else {
        invalid_xml()
    }
}

pub(super) fn contains_forbidden_declaration(value: &str) -> bool {
    let bytes = value.as_bytes();
    let mut index = 0_usize;
    while index + 2 <= bytes.len() {
        if bytes[index] == b'<' && bytes.get(index + 1) == Some(&b'!') {
            let mut cursor = index + 2;
            while bytes.get(cursor).is_some_and(u8::is_ascii_whitespace) {
                cursor += 1;
            }
            for keyword in [b"DOCTYPE".as_slice(), b"ENTITY".as_slice()] {
                let Some(end) = cursor.checked_add(keyword.len()) else {
                    return true;
                };
                if bytes.get(cursor..end).is_some_and(|candidate| {
                    candidate.eq_ignore_ascii_case(keyword)
                        && bytes
                            .get(end)
                            .is_none_or(|next| !next.is_ascii_alphanumeric() && *next != b'_')
                }) {
                    return true;
                }
            }
        }
        index += 1;
    }
    false
}

fn valid_qname(value: &str) -> bool {
    let mut parts = value.split(':');
    let Some(first) = parts.next() else {
        return false;
    };
    let second = parts.next();
    parts.next().is_none() && valid_ncname(first) && second.is_none_or(valid_ncname)
}

fn valid_ncname(value: &str) -> bool {
    let mut characters = value.chars();
    characters.next().is_some_and(is_name_start) && characters.all(is_name_character)
}

const fn is_name_start(value: char) -> bool {
    let codepoint = value as u32;
    value == '_'
        || (codepoint >= 0x41 && codepoint <= 0x5a)
        || (codepoint >= 0x61 && codepoint <= 0x7a)
        || (codepoint >= 0xc0 && codepoint <= 0xd6)
        || (codepoint >= 0xd8 && codepoint <= 0xf6)
        || (codepoint >= 0xf8 && codepoint <= 0x2ff)
        || (codepoint >= 0x370 && codepoint <= 0x37d)
        || (codepoint >= 0x37f && codepoint <= 0x1fff)
        || (codepoint >= 0x200c && codepoint <= 0x200d)
        || (codepoint >= 0x2070 && codepoint <= 0x218f)
        || (codepoint >= 0x2c00 && codepoint <= 0x2fef)
        || (codepoint >= 0x3001 && codepoint <= 0xd7ff)
        || (codepoint >= 0xf900 && codepoint <= 0xfdcf)
        || (codepoint >= 0xfdf0 && codepoint <= 0xfffd)
        || (codepoint >= 0x1_0000 && codepoint <= 0xe_ffff)
}

const fn is_name_character(value: char) -> bool {
    let codepoint = value as u32;
    is_name_start(value)
        || matches!(value, '-' | '.')
        || (codepoint >= 0x30 && codepoint <= 0x39)
        || codepoint == 0xb7
        || (codepoint >= 0x300 && codepoint <= 0x36f)
        || (codepoint >= 0x203f && codepoint <= 0x2040)
}

const fn is_xml_character(value: char) -> bool {
    let codepoint = value as u32;
    matches!(codepoint, 0x9 | 0xa | 0xd)
        || (codepoint >= 0x20 && codepoint <= 0xd7ff)
        || (codepoint >= 0xe000 && codepoint <= 0xfffd)
        || (codepoint >= 0x1_0000 && codepoint <= 0x10_ffff)
}

const fn is_xml_space(value: char) -> bool {
    matches!(value, ' ' | '\t' | '\n' | '\r')
}

fn invalid_xml<T>() -> EncodedResult<T> {
    Err(invalid_xml_error())
}

fn invalid_xml_error() -> EncodedValidationError {
    EncodedValidationError::invariant("rdf:XMLLiteral is not a well-formed XML fragment")
}

#[cfg(test)]
mod tests {
    use super::super::named_classes::{NamedClassPhaseLimits, PhaseBudget};
    use super::canonicalize;
    use crate::encoded::EncodedResult;

    fn canonical(value: &str) -> EncodedResult<String> {
        canonicalize(
            value,
            &mut PhaseBudget::new(NamedClassPhaseLimits::default()),
        )
    }

    #[test]
    fn canonicalizes_attributes_namespaces_and_fragment_nodes() -> EncodedResult<()> {
        let cases = [
            ("", ""),
            ("text", "text"),
            ("<a/>", "<a></a>"),
            ("<a y=\"2\" x=\"1\"/>", "<a x=\"1\" y=\"2\"></a>"),
            (
                "<a xmlns:p=\"urn:x\"><p:b/><p:c/></a>",
                "<a><p:b xmlns:p=\"urn:x\"></p:b><p:c xmlns:p=\"urn:x\"></p:c></a>",
            ),
            (
                "<!--top--><a><![CDATA[x<y&z]]></a><?pi data?>",
                "<!--top--><a>x&lt;y&amp;z</a><?pi data?>",
            ),
            (
                "<a xmlns:q=\"urn:x\" xmlns:p=\"urn:y\" q:z=\"1\" p:a=\"2\" b=\"3\"/>",
                "<a xmlns:p=\"urn:y\" xmlns:q=\"urn:x\" b=\"3\" q:z=\"1\" p:a=\"2\"></a>",
            ),
            (
                "<a x=\"a&#x9;b&#xA;c&#xD;d&quot;e&amp;f&lt;g&gt;h\"/>",
                "<a x=\"a&#x9;b&#xA;c&#xD;d&quot;e&amp;f&lt;g>h\"></a>",
            ),
            (
                "<a><p:b xmlns:p=\"u1\"/><q:c xmlns:q=\"u1\"/></a>",
                "<a><p:b xmlns:p=\"u1\"></p:b><p:c xmlns:p=\"u1\"></p:c></a>",
            ),
            (
                "<a xmlns:p=\"urn:x\"><b xmlns:q=\"urn:x\"><p:c q:d=\"1\"/></b></a>",
                "<a><b><q:c xmlns:q=\"urn:x\" q:d=\"1\"></q:c></b></a>",
            ),
        ];
        for (source, expected) in cases {
            assert_eq!(canonical(source)?, expected);
        }
        Ok(())
    }

    #[test]
    fn rejects_declarations_and_honours_xml_limits() {
        assert!(canonical("<!DOCTYPE a><a/>").is_err());
        assert!(canonical("<a>&unknown;</a>").is_err());
        let limits = NamedClassPhaseLimits {
            max_xml_depth: 1,
            ..NamedClassPhaseLimits::default()
        };
        assert!(canonicalize("<a><b/></a>", &mut PhaseBudget::new(limits)).is_err());
    }
}
