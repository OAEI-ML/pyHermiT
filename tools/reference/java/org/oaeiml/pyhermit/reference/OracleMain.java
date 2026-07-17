package org.oaeiml.pyhermit.reference;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;
import java.net.SocketPermission;
import java.security.Permission;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.TreeSet;

import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.util.SimpleIRIMapper;

import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.ObjectMapper;

/** Development-only, one-request-per-line HermiT oracle adapter. */
public final class OracleMain {
    private static final ObjectMapper JSON = new ObjectMapper();

    private OracleMain() {
    }

    public static void main(String[] args) throws Exception {
        installNetworkDenyPolicy();
        BufferedReader reader = new BufferedReader(new InputStreamReader(System.in, "UTF-8"));
        String line;
        while ((line = reader.readLine()) != null) {
            if (line.trim().isEmpty()) {
                continue;
            }
            Map<String, Object> request = JSON.readValue(
                line, new TypeReference<Map<String, Object>>() { }
            );
            Map<String, Object> response;
            try {
                response = execute(request);
            }
            catch (OutOfMemoryError error) {
                response = errorResponse(request, "RESOURCE_LIMIT", error);
            }
            catch (Throwable error) {
                response = errorResponse(request, "ERROR", error);
            }
            System.out.println(JSON.writeValueAsString(response));
            System.out.flush();
        }
    }

    private static void installNetworkDenyPolicy() {
        System.setSecurityManager(new SecurityManager() {
            @Override
            public void checkPermission(Permission permission) {
                // The oracle is a disposable subprocess.  File/class access is constrained by
                // the Python driver; only network socket permissions are denied here.
                if (permission instanceof SocketPermission) {
                    throw new SecurityException("network access is disabled in the reference oracle");
                }
            }

            @Override
            public void checkConnect(String host, int port) {
                throw new SecurityException("network access is disabled in the reference oracle");
            }

            @Override
            public void checkConnect(String host, int port, Object context) {
                throw new SecurityException("network access is disabled in the reference oracle");
            }
        });
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> execute(Map<String, Object> request) throws Exception {
        String requestId = String.valueOf(request.get("request_id"));
        String operation = String.valueOf(request.get("operation"));
        Map<String, Object> response = baseResponse(requestId);
        if ("identity".equals(operation)) {
            response.put("status", "LOGICAL");
            response.put("value", identity());
            return response;
        }

        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        List<Map<String, Object>> imports =
            (List<Map<String, Object>>) request.get("_resolved_imports");
        for (Map<String, Object> imported : imports) {
            manager.getIRIMappers().add(new SimpleIRIMapper(
                IRI.create(String.valueOf(imported.get("logical_iri"))),
                IRI.create(new File(String.valueOf(imported.get("path"))))
            ));
        }
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(
            new File(String.valueOf(request.get("_resolved_document")))
        );
        if ("normalization".equals(operation)) {
            response.put("status", "LOGICAL");
            response.put("value", NormalizationSerializer.normalize(ontology));
            return response;
        }
        Map<String, Object> configValue = (Map<String, Object>) request.get("config");
        Configuration configuration = new Configuration();
        configuration.ignoreUnsupportedDatatypes = Boolean.TRUE.equals(
            configValue.get("ignore_unsupported_datatypes")
        );
        OWLReasoner reasoner = new Reasoner(configuration, ontology);
        try {
            if ("consistency".equals(operation)) {
                boolean consistent = reasoner.isConsistent();
                response.put("status", "LOGICAL");
                response.put("outcome", consistent ? "SAT" : "UNSAT");
                response.put("value", Boolean.valueOf(consistent));
            }
            else if ("class_hierarchy".equals(operation)) {
                response.put("status", "LOGICAL");
                response.put("value", classHierarchy(reasoner));
            }
            else {
                throw new IllegalArgumentException("unsupported operation: " + operation);
            }
        }
        finally {
            reasoner.dispose();
        }
        return response;
    }

    private static Map<String, Object> classHierarchy(OWLReasoner reasoner) {
        Map<String, List<Map<String, String>>> nodes = new LinkedHashMap<>();
        List<List<List<Map<String, String>>>> edges = new ArrayList<>();
        Queue<Node<OWLClass>> queue = new ArrayDeque<>();
        Set<String> expanded = new TreeSet<>();
        queue.add(reasoner.getTopClassNode());
        addNode(nodes, reasoner.getBottomClassNode());
        while (!queue.isEmpty()) {
            Node<OWLClass> parent = queue.remove();
            String parentKey = addNode(nodes, parent);
            if (!expanded.add(parentKey)) {
                continue;
            }
            NodeSet<OWLClass> children = reasoner.getSubClasses(parent.getRepresentativeElement(), true);
            for (Node<OWLClass> child : children.getNodes()) {
                String childKey = addNode(nodes, child);
                List<List<Map<String, String>>> edge = new ArrayList<>();
                edge.add(nodes.get(parentKey));
                edge.add(nodes.get(childKey));
                edges.add(edge);
                if (!expanded.contains(childKey)) {
                    queue.add(child);
                }
            }
        }
        List<List<Map<String, String>>> nodeList = new ArrayList<>(nodes.values());
        Map<String, Object> value = new LinkedHashMap<>();
        value.put("kind", "raw_hierarchy");
        value.put("nodes", nodeList);
        value.put("edges", edges);
        return value;
    }

    private static String addNode(
        Map<String, List<Map<String, String>>> nodes, Node<OWLClass> node
    ) {
        TreeSet<String> iris = new TreeSet<>();
        for (OWLClass owlClass : node.getEntities()) {
            iris.add(owlClass.getIRI().toString());
        }
        String key = String.join("\u0000", iris);
        if (!nodes.containsKey(key)) {
            List<Map<String, String>> members = new ArrayList<>();
            for (String iri : iris) {
                Map<String, String> term = new LinkedHashMap<>();
                term.put("kind", "iri");
                term.put("value", iri);
                members.add(term);
            }
            nodes.put(key, members);
        }
        return key;
    }

    private static Map<String, Object> baseResponse(String requestId) {
        Map<String, Object> response = new LinkedHashMap<>();
        response.put("request_id", requestId);
        response.put("jvm", identity());
        return response;
    }

    private static Map<String, Object> identity() {
        Map<String, Object> value = new LinkedHashMap<>();
        value.put("java_version", System.getProperty("java.version"));
        value.put("java_vendor", System.getProperty("java.vendor"));
        value.put("vm_name", System.getProperty("java.vm.name"));
        value.put("os_name", System.getProperty("os.name"));
        value.put("os_arch", System.getProperty("os.arch"));
        value.put("hermit_version", "1.4.0.0-SNAPSHOT");
        value.put("owlapi_version", "4.2.8");
        return value;
    }

    private static Map<String, Object> errorResponse(
        Map<String, Object> request, String status, Throwable error
    ) {
        Map<String, Object> response = baseResponse(String.valueOf(request.get("request_id")));
        response.put("status", status);
        response.put("error_type", error.getClass().getName());
        response.put("message", error.getMessage() == null ? error.toString() : error.getMessage());
        return response;
    }
}
