package org.oaeiml.pyhermit.reference;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.semanticweb.HermiT.structural.OWLAxioms;
import org.semanticweb.HermiT.structural.OWLNormalization;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLAnonymousIndividual;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataAllValuesFrom;
import org.semanticweb.owlapi.model.OWLDataComplementOf;
import org.semanticweb.owlapi.model.OWLDataExactCardinality;
import org.semanticweb.owlapi.model.OWLDataHasValue;
import org.semanticweb.owlapi.model.OWLDataIntersectionOf;
import org.semanticweb.owlapi.model.OWLDataMaxCardinality;
import org.semanticweb.owlapi.model.OWLDataMinCardinality;
import org.semanticweb.owlapi.model.OWLDataOneOf;
import org.semanticweb.owlapi.model.OWLDataPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyExpression;
import org.semanticweb.owlapi.model.OWLDataRange;
import org.semanticweb.owlapi.model.OWLDataSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLDataUnionOf;
import org.semanticweb.owlapi.model.OWLDatatype;
import org.semanticweb.owlapi.model.OWLDatatypeRestriction;
import org.semanticweb.owlapi.model.OWLDifferentIndividualsAxiom;
import org.semanticweb.owlapi.model.OWLFacetRestriction;
import org.semanticweb.owlapi.model.OWLHasKeyAxiom;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLIndividualAxiom;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLNegativeDataPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLNegativeObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectExactCardinality;
import org.semanticweb.owlapi.model.OWLObjectHasSelf;
import org.semanticweb.owlapi.model.OWLObjectHasValue;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectOneOf;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLSameIndividualAxiom;
import org.semanticweb.owlapi.model.parameters.Imports;

import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.ObjectMapper;

/** Deterministic, language-neutral projection of HermiT's structural normalization holder. */
final class NormalizationSerializer {
    private static final ObjectMapper JSON = new ObjectMapper();

    private NormalizationSerializer() {
    }

    static Map<String, Object> normalize(OWLOntology rootOntology) {
        OWLAxioms axioms = new OWLAxioms();
        OWLNormalization normalization = new OWLNormalization(
            rootOntology.getOWLOntologyManager().getOWLDataFactory(), axioms, 0
        );
        List<OWLOntology> closure = new ArrayList<>(rootOntology.getImportsClosure());
        Collections.sort(closure, new Comparator<OWLOntology>() {
            @Override
            public int compare(OWLOntology first, OWLOntology second) {
                return first.getOntologyID().toString().compareTo(second.getOntologyID().toString());
            }
        });
        for (OWLOntology ontology : closure) {
            axioms.m_classes.addAll(ontology.getClassesInSignature(Imports.EXCLUDED));
            axioms.m_objectProperties.addAll(
                ontology.getObjectPropertiesInSignature(Imports.EXCLUDED)
            );
            axioms.m_dataProperties.addAll(ontology.getDataPropertiesInSignature(Imports.EXCLUDED));
            axioms.m_namedIndividuals.addAll(
                ontology.getIndividualsInSignature(Imports.EXCLUDED)
            );
            List<OWLAxiom> logicalAxioms = new ArrayList<>(ontology.getLogicalAxioms());
            Collections.sort(logicalAxioms, new Comparator<OWLAxiom>() {
                @Override
                public int compare(OWLAxiom first, OWLAxiom second) {
                    return first.toString().compareTo(second.toString());
                }
            });
            normalization.processAxioms(logicalAxioms);
        }
        if (!axioms.m_rules.isEmpty()) {
            throw new IllegalArgumentException(
                "SWRL rules are outside the OWL 2 structural-normalization oracle contract"
            );
        }

        Map<String, Object> value = object("raw_structural_normalization");
        value.put("families", families(axioms));
        return value;
    }

    private static Map<String, Object> families(OWLAxioms axioms) {
        Map<String, Object> families = new LinkedHashMap<>();
        families.put("concept_inclusions", conceptInclusions(axioms.m_conceptInclusions));
        families.put("data_range_inclusions", dataRangeInclusions(axioms.m_dataRangeInclusions));
        families.put(
            "simple_object_property_inclusions",
            objectPropertyPairs(axioms.m_simpleObjectPropertyInclusions)
        );
        families.put(
            "complex_object_property_inclusions",
            complexObjectPropertyInclusions(axioms.m_complexObjectPropertyInclusions)
        );
        families.put(
            "disjoint_object_properties",
            objectPropertyGroups(axioms.m_disjointObjectProperties)
        );
        families.put(
            "reflexive_object_properties",
            objectProperties(axioms.m_reflexiveObjectProperties)
        );
        families.put(
            "irreflexive_object_properties",
            objectProperties(axioms.m_irreflexiveObjectProperties)
        );
        families.put(
            "asymmetric_object_properties",
            objectProperties(axioms.m_asymmetricObjectProperties)
        );
        families.put(
            "data_property_inclusions", dataPropertyPairs(axioms.m_dataPropertyInclusions)
        );
        families.put(
            "disjoint_data_properties", dataPropertyGroups(axioms.m_disjointDataProperties)
        );
        families.put("facts", facts(axioms.m_facts));
        families.put("has_keys", hasKeys(axioms.m_hasKeys));
        List<Object> datatypes = new ArrayList<>();
        for (String iri : axioms.m_definedDatatypesIRIs) {
            datatypes.add(entity("datatype", iri));
        }
        sortJson(datatypes);
        families.put("defined_datatypes", datatypes);
        return families;
    }

    private static List<Object> conceptInclusions(
        Collection<OWLClassExpression[]> inclusions
    ) {
        List<Object> result = new ArrayList<>();
        for (OWLClassExpression[] inclusion : inclusions) {
            List<Object> expressions = new ArrayList<>();
            for (OWLClassExpression expression : inclusion) {
                expressions.add(classExpression(expression));
            }
            sortJson(expressions);
            result.add(expressions);
        }
        sortJson(result);
        return result;
    }

    private static List<Object> dataRangeInclusions(Collection<OWLDataRange[]> inclusions) {
        List<Object> result = new ArrayList<>();
        for (OWLDataRange[] inclusion : inclusions) {
            List<Object> ranges = new ArrayList<>();
            for (OWLDataRange range : inclusion) {
                ranges.add(dataRange(range));
            }
            sortJson(ranges);
            result.add(ranges);
        }
        sortJson(result);
        return result;
    }

    private static List<Object> objectPropertyPairs(
        Collection<OWLObjectPropertyExpression[]> inclusions
    ) {
        List<Object> result = new ArrayList<>();
        for (OWLObjectPropertyExpression[] inclusion : inclusions) {
            if (inclusion.length != 2) {
                throw new IllegalArgumentException(
                    "simple object-property inclusion must contain two properties"
                );
            }
            List<Object> pair = new ArrayList<>();
            pair.add(objectProperty(inclusion[0]));
            pair.add(objectProperty(inclusion[1]));
            result.add(pair);
        }
        sortJson(result);
        return result;
    }

    private static List<Object> complexObjectPropertyInclusions(
        Collection<OWLAxioms.ComplexObjectPropertyInclusion> inclusions
    ) {
        List<Object> result = new ArrayList<>();
        for (OWLAxioms.ComplexObjectPropertyInclusion inclusion : inclusions) {
            Map<String, Object> record = new LinkedHashMap<>();
            List<Object> chain = new ArrayList<>();
            for (OWLObjectPropertyExpression property : inclusion.m_subObjectProperties) {
                chain.add(objectProperty(property));
            }
            record.put("chain", chain);
            record.put("super_property", objectProperty(inclusion.m_superObjectProperty));
            result.add(record);
        }
        sortJson(result);
        return result;
    }

    private static List<Object> objectPropertyGroups(
        Collection<OWLObjectPropertyExpression[]> groups
    ) {
        List<Object> result = new ArrayList<>();
        for (OWLObjectPropertyExpression[] group : groups) {
            List<Object> properties = new ArrayList<>();
            for (OWLObjectPropertyExpression property : group) {
                properties.add(objectProperty(property));
            }
            sortJson(properties);
            result.add(properties);
        }
        sortJson(result);
        return result;
    }

    private static List<Object> objectProperties(
        Collection<OWLObjectPropertyExpression> properties
    ) {
        List<Object> result = new ArrayList<>();
        for (OWLObjectPropertyExpression property : properties) {
            result.add(objectProperty(property));
        }
        sortJson(result);
        return result;
    }

    private static List<Object> dataPropertyPairs(
        Collection<OWLDataPropertyExpression[]> inclusions
    ) {
        List<Object> result = new ArrayList<>();
        for (OWLDataPropertyExpression[] inclusion : inclusions) {
            if (inclusion.length != 2) {
                throw new IllegalArgumentException(
                    "data-property inclusion must contain two properties"
                );
            }
            List<Object> pair = new ArrayList<>();
            pair.add(dataProperty(inclusion[0]));
            pair.add(dataProperty(inclusion[1]));
            result.add(pair);
        }
        sortJson(result);
        return result;
    }

    private static List<Object> dataPropertyGroups(
        Collection<OWLDataPropertyExpression[]> groups
    ) {
        List<Object> result = new ArrayList<>();
        for (OWLDataPropertyExpression[] group : groups) {
            List<Object> properties = new ArrayList<>();
            for (OWLDataPropertyExpression property : group) {
                properties.add(dataProperty(property));
            }
            sortJson(properties);
            result.add(properties);
        }
        sortJson(result);
        return result;
    }

    private static List<Object> facts(Collection<OWLIndividualAxiom> facts) {
        List<Object> result = new ArrayList<>();
        for (OWLIndividualAxiom fact : facts) {
            result.add(fact(fact));
        }
        sortJson(result);
        return result;
    }

    private static Map<String, Object> fact(OWLIndividualAxiom fact) {
        if (fact instanceof OWLClassAssertionAxiom) {
            OWLClassAssertionAxiom assertion = (OWLClassAssertionAxiom) fact;
            Map<String, Object> result = object("class_assertion");
            result.put("class_expression", classExpression(assertion.getClassExpression()));
            result.put("individual", individual(assertion.getIndividual()));
            return result;
        }
        if (fact instanceof OWLNegativeObjectPropertyAssertionAxiom) {
            OWLNegativeObjectPropertyAssertionAxiom assertion =
                (OWLNegativeObjectPropertyAssertionAxiom) fact;
            return objectPropertyAssertion(
                "negative_object_property_assertion",
                assertion.getProperty(),
                assertion.getSubject(),
                assertion.getObject()
            );
        }
        if (fact instanceof OWLObjectPropertyAssertionAxiom) {
            OWLObjectPropertyAssertionAxiom assertion = (OWLObjectPropertyAssertionAxiom) fact;
            return objectPropertyAssertion(
                "object_property_assertion",
                assertion.getProperty(),
                assertion.getSubject(),
                assertion.getObject()
            );
        }
        if (fact instanceof OWLNegativeDataPropertyAssertionAxiom) {
            OWLNegativeDataPropertyAssertionAxiom assertion =
                (OWLNegativeDataPropertyAssertionAxiom) fact;
            return dataPropertyAssertion(
                "negative_data_property_assertion",
                assertion.getProperty(),
                assertion.getSubject(),
                assertion.getObject()
            );
        }
        if (fact instanceof OWLDataPropertyAssertionAxiom) {
            OWLDataPropertyAssertionAxiom assertion = (OWLDataPropertyAssertionAxiom) fact;
            return dataPropertyAssertion(
                "data_property_assertion",
                assertion.getProperty(),
                assertion.getSubject(),
                assertion.getObject()
            );
        }
        if (fact instanceof OWLSameIndividualAxiom) {
            return individualGroup(
                "same_individual", ((OWLSameIndividualAxiom) fact).getIndividuals()
            );
        }
        if (fact instanceof OWLDifferentIndividualsAxiom) {
            return individualGroup(
                "different_individuals",
                ((OWLDifferentIndividualsAxiom) fact).getIndividuals()
            );
        }
        throw new IllegalArgumentException(
            "unsupported normalized fact type: " + fact.getClass().getName()
        );
    }

    private static Map<String, Object> objectPropertyAssertion(
        String kind,
        OWLObjectPropertyExpression property,
        OWLIndividual subject,
        OWLIndividual object
    ) {
        Map<String, Object> result = object(kind);
        result.put("property", objectProperty(property));
        result.put("subject", individual(subject));
        result.put("object", individual(object));
        return result;
    }

    private static Map<String, Object> dataPropertyAssertion(
        String kind,
        OWLDataPropertyExpression property,
        OWLIndividual subject,
        OWLLiteral value
    ) {
        Map<String, Object> result = object(kind);
        result.put("property", dataProperty(property));
        result.put("subject", individual(subject));
        result.put("value", literal(value));
        return result;
    }

    private static Map<String, Object> individualGroup(
        String kind, Collection<OWLIndividual> individuals
    ) {
        Map<String, Object> result = object(kind);
        List<Object> values = new ArrayList<>();
        for (OWLIndividual individual : individuals) {
            values.add(individual(individual));
        }
        sortJson(values);
        result.put("individuals", values);
        return result;
    }

    private static List<Object> hasKeys(Collection<OWLHasKeyAxiom> keys) {
        List<Object> result = new ArrayList<>();
        for (OWLHasKeyAxiom key : keys) {
            Map<String, Object> record = new LinkedHashMap<>();
            record.put("class_expression", classExpression(key.getClassExpression()));
            record.put("object_properties", objectProperties(key.getObjectPropertyExpressions()));
            List<Object> dataProperties = new ArrayList<>();
            for (OWLDataPropertyExpression property : key.getDataPropertyExpressions()) {
                dataProperties.add(dataProperty(property));
            }
            sortJson(dataProperties);
            record.put("data_properties", dataProperties);
            result.add(record);
        }
        sortJson(result);
        return result;
    }

    private static Map<String, Object> classExpression(OWLClassExpression expression) {
        if (expression instanceof OWLClass) {
            return entity("class", ((OWLClass) expression).getIRI().toString());
        }
        if (expression instanceof OWLObjectComplementOf) {
            Map<String, Object> result = object("object_complement");
            result.put(
                "operand", classExpression(((OWLObjectComplementOf) expression).getOperand())
            );
            return result;
        }
        if (expression instanceof OWLObjectIntersectionOf) {
            return classOperands(
                "object_intersection", ((OWLObjectIntersectionOf) expression).getOperands()
            );
        }
        if (expression instanceof OWLObjectUnionOf) {
            return classOperands("object_union", ((OWLObjectUnionOf) expression).getOperands());
        }
        if (expression instanceof OWLObjectOneOf) {
            Map<String, Object> result = object("object_one_of");
            List<Object> individuals = new ArrayList<>();
            for (OWLIndividual individual : ((OWLObjectOneOf) expression).getIndividuals()) {
                individuals.add(individual(individual));
            }
            sortJson(individuals);
            result.put("individuals", individuals);
            return result;
        }
        if (expression instanceof OWLObjectSomeValuesFrom) {
            OWLObjectSomeValuesFrom restriction = (OWLObjectSomeValuesFrom) expression;
            return objectRestriction(
                "object_some", restriction.getProperty(), restriction.getFiller()
            );
        }
        if (expression instanceof OWLObjectAllValuesFrom) {
            OWLObjectAllValuesFrom restriction = (OWLObjectAllValuesFrom) expression;
            return objectRestriction(
                "object_all", restriction.getProperty(), restriction.getFiller()
            );
        }
        if (expression instanceof OWLObjectMinCardinality) {
            OWLObjectMinCardinality restriction = (OWLObjectMinCardinality) expression;
            return objectCardinality(
                "object_min",
                restriction.getCardinality(),
                restriction.getProperty(),
                restriction.getFiller()
            );
        }
        if (expression instanceof OWLObjectMaxCardinality) {
            OWLObjectMaxCardinality restriction = (OWLObjectMaxCardinality) expression;
            return objectCardinality(
                "object_max",
                restriction.getCardinality(),
                restriction.getProperty(),
                restriction.getFiller()
            );
        }
        if (expression instanceof OWLObjectExactCardinality) {
            OWLObjectExactCardinality restriction = (OWLObjectExactCardinality) expression;
            return objectCardinality(
                "object_exact",
                restriction.getCardinality(),
                restriction.getProperty(),
                restriction.getFiller()
            );
        }
        if (expression instanceof OWLObjectHasSelf) {
            Map<String, Object> result = object("object_has_self");
            result.put(
                "property", objectProperty(((OWLObjectHasSelf) expression).getProperty())
            );
            return result;
        }
        if (expression instanceof OWLObjectHasValue) {
            OWLObjectHasValue restriction = (OWLObjectHasValue) expression;
            Map<String, Object> result = object("object_has_value");
            result.put("property", objectProperty(restriction.getProperty()));
            result.put("value", individual(restriction.getFiller()));
            return result;
        }
        if (expression instanceof OWLDataSomeValuesFrom) {
            OWLDataSomeValuesFrom restriction = (OWLDataSomeValuesFrom) expression;
            return dataRestriction("data_some", restriction.getProperty(), restriction.getFiller());
        }
        if (expression instanceof OWLDataAllValuesFrom) {
            OWLDataAllValuesFrom restriction = (OWLDataAllValuesFrom) expression;
            return dataRestriction("data_all", restriction.getProperty(), restriction.getFiller());
        }
        if (expression instanceof OWLDataMinCardinality) {
            OWLDataMinCardinality restriction = (OWLDataMinCardinality) expression;
            return dataCardinality(
                "data_min",
                restriction.getCardinality(),
                restriction.getProperty(),
                restriction.getFiller()
            );
        }
        if (expression instanceof OWLDataMaxCardinality) {
            OWLDataMaxCardinality restriction = (OWLDataMaxCardinality) expression;
            return dataCardinality(
                "data_max",
                restriction.getCardinality(),
                restriction.getProperty(),
                restriction.getFiller()
            );
        }
        if (expression instanceof OWLDataExactCardinality) {
            OWLDataExactCardinality restriction = (OWLDataExactCardinality) expression;
            return dataCardinality(
                "data_exact",
                restriction.getCardinality(),
                restriction.getProperty(),
                restriction.getFiller()
            );
        }
        if (expression instanceof OWLDataHasValue) {
            OWLDataHasValue restriction = (OWLDataHasValue) expression;
            Map<String, Object> result = object("data_has_value");
            result.put("property", dataProperty(restriction.getProperty()));
            result.put("value", literal(restriction.getFiller()));
            return result;
        }
        throw new IllegalArgumentException(
            "unsupported normalized class expression: " + expression.getClass().getName()
        );
    }

    private static Map<String, Object> classOperands(
        String kind, Collection<OWLClassExpression> operands
    ) {
        Map<String, Object> result = object(kind);
        List<Object> values = new ArrayList<>();
        for (OWLClassExpression operand : operands) {
            values.add(classExpression(operand));
        }
        sortJson(values);
        result.put("operands", values);
        return result;
    }

    private static Map<String, Object> objectRestriction(
        String kind, OWLObjectPropertyExpression property, OWLClassExpression filler
    ) {
        Map<String, Object> result = object(kind);
        result.put("property", objectProperty(property));
        result.put("filler", classExpression(filler));
        return result;
    }

    private static Map<String, Object> objectCardinality(
        String kind,
        int cardinality,
        OWLObjectPropertyExpression property,
        OWLClassExpression filler
    ) {
        Map<String, Object> result = objectRestriction(kind, property, filler);
        result.put("cardinality", cardinality);
        return ordered(result, "kind", "cardinality", "property", "filler");
    }

    private static Map<String, Object> dataRestriction(
        String kind, OWLDataPropertyExpression property, OWLDataRange filler
    ) {
        Map<String, Object> result = object(kind);
        result.put("property", dataProperty(property));
        result.put("filler", dataRange(filler));
        return result;
    }

    private static Map<String, Object> dataCardinality(
        String kind, int cardinality, OWLDataPropertyExpression property, OWLDataRange filler
    ) {
        Map<String, Object> result = dataRestriction(kind, property, filler);
        result.put("cardinality", cardinality);
        return ordered(result, "kind", "cardinality", "property", "filler");
    }

    private static Map<String, Object> dataRange(OWLDataRange range) {
        if (range instanceof OWLDatatype) {
            return entity("datatype", ((OWLDatatype) range).getIRI().toString());
        }
        if (range instanceof OWLDataComplementOf) {
            Map<String, Object> result = object("data_complement");
            result.put("operand", dataRange(((OWLDataComplementOf) range).getDataRange()));
            return result;
        }
        if (range instanceof OWLDataIntersectionOf) {
            return dataOperands(
                "data_intersection", ((OWLDataIntersectionOf) range).getOperands()
            );
        }
        if (range instanceof OWLDataUnionOf) {
            return dataOperands("data_union", ((OWLDataUnionOf) range).getOperands());
        }
        if (range instanceof OWLDataOneOf) {
            Map<String, Object> result = object("data_one_of");
            List<Object> values = new ArrayList<>();
            for (OWLLiteral value : ((OWLDataOneOf) range).getValues()) {
                values.add(literal(value));
            }
            sortJson(values);
            result.put("values", values);
            return result;
        }
        if (range instanceof OWLDatatypeRestriction) {
            OWLDatatypeRestriction restriction = (OWLDatatypeRestriction) range;
            Map<String, Object> result = object("datatype_restriction");
            result.put("datatype", dataRange(restriction.getDatatype()));
            List<Object> facets = new ArrayList<>();
            for (OWLFacetRestriction facet : restriction.getFacetRestrictions()) {
                Map<String, Object> record = new LinkedHashMap<>();
                record.put("facet", facet.getFacet().getIRI().toString());
                record.put("value", literal(facet.getFacetValue()));
                facets.add(record);
            }
            sortJson(facets);
            result.put("facets", facets);
            return result;
        }
        throw new IllegalArgumentException(
            "unsupported normalized data range: " + range.getClass().getName()
        );
    }

    private static Map<String, Object> dataOperands(
        String kind, Collection<OWLDataRange> operands
    ) {
        Map<String, Object> result = object(kind);
        List<Object> values = new ArrayList<>();
        for (OWLDataRange operand : operands) {
            values.add(dataRange(operand));
        }
        sortJson(values);
        result.put("operands", values);
        return result;
    }

    private static Map<String, Object> objectProperty(
        OWLObjectPropertyExpression property
    ) {
        if (!property.isAnonymous()) {
            return entity("object_property", property.asOWLObjectProperty().getIRI().toString());
        }
        Map<String, Object> result = object("inverse_object_property");
        result.put(
            "property", entity("object_property", property.getNamedProperty().getIRI().toString())
        );
        return result;
    }

    private static Map<String, Object> dataProperty(OWLDataPropertyExpression property) {
        return entity("data_property", property.asOWLDataProperty().getIRI().toString());
    }

    private static Map<String, Object> individual(OWLIndividual individual) {
        if (individual.isNamed()) {
            OWLNamedIndividual named = individual.asOWLNamedIndividual();
            return entity("named_individual", named.getIRI().toString());
        }
        OWLAnonymousIndividual anonymous = individual.asOWLAnonymousIndividual();
        Map<String, Object> result = object("anonymous_individual");
        result.put("id", anonymous.getID().getID());
        return result;
    }

    private static Map<String, Object> literal(OWLLiteral literal) {
        Map<String, Object> result = object("literal");
        result.put("lexical", literal.getLiteral());
        result.put("datatype", literal.getDatatype().getIRI().toString());
        result.put("language", literal.getLang());
        return result;
    }

    private static Map<String, Object> entity(String kind, String iri) {
        Map<String, Object> result = object(kind);
        result.put("iri", iri);
        return result;
    }

    private static Map<String, Object> object(String kind) {
        Map<String, Object> result = new LinkedHashMap<>();
        result.put("kind", kind);
        return result;
    }

    private static Map<String, Object> ordered(
        Map<String, Object> source, String first, String second, String third, String fourth
    ) {
        Map<String, Object> result = new LinkedHashMap<>();
        result.put(first, source.get(first));
        result.put(second, source.get(second));
        result.put(third, source.get(third));
        result.put(fourth, source.get(fourth));
        return result;
    }

    private static void sortJson(List<Object> values) {
        Collections.sort(values, new Comparator<Object>() {
            @Override
            public int compare(Object first, Object second) {
                return json(first).compareTo(json(second));
            }
        });
    }

    private static String json(Object value) {
        try {
            return JSON.writeValueAsString(value);
        }
        catch (JsonProcessingException error) {
            throw new IllegalStateException("normalization value cannot be serialized", error);
        }
    }
}
