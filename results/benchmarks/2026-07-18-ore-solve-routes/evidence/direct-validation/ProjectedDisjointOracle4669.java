import java.io.BufferedWriter;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.zip.GZIPOutputStream;

import org.semanticweb.HermiT.ReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

/**
 * Complete base-to-negative cross-edge oracle for the positive 4669 projection.
 *
 * For N_i == not P_i, A <= N_i iff A and P_i are disjoint. HermiT is loaded on
 * the complement-free projected ontology once, then getDisjointClasses(P_i) is
 * queried for every fresh proxy. Full IRIs are written to a gzip TSV.
 *
 * Usage:
 *   java ProjectedDisjointOracle4669 PROJECTED.ofn MAPPING.tsv CROSS.tsv.gz SUMMARY.json
 */
public final class ProjectedDisjointOracle4669 {
    private static final String PROXY_PREFIX = "urn:km:oracle:4669:positive-proxy:";

    private static final class Mirror {
        final String negative;
        final String proxy;

        Mirror(String negative, String proxy) {
            this.negative = negative;
            this.proxy = proxy;
        }
    }

    private static final class Witness {
        final OWLClass base;
        final OWLClass proxy;
        final String negative;

        Witness(OWLClass base, OWLClass proxy, String negative) {
            this.base = base;
            this.proxy = proxy;
            this.negative = negative;
        }
    }

    private ProjectedDisjointOracle4669() {}

    public static void main(String[] args) throws Exception {
        if (args.length != 4) {
            System.err.println(
                    "Usage: ProjectedDisjointOracle4669 PROJECTED.ofn MAPPING.tsv CROSS.tsv.gz SUMMARY.json");
            System.exit(2);
        }
        Path projectedPath = Paths.get(args[0]).toAbsolutePath().normalize();
        Path mappingPath = Paths.get(args[1]).toAbsolutePath().normalize();
        Path crossPath = Paths.get(args[2]).toAbsolutePath().normalize();
        Path summaryPath = Paths.get(args[3]).toAbsolutePath().normalize();
        Files.createDirectories(crossPath.getParent());
        Files.createDirectories(summaryPath.getParent());

        List<Mirror> mirrors = readMapping(mappingPath);
        Set<String> proxyIris = new HashSet<>();
        Set<String> negativeIris = new HashSet<>();
        for (Mirror mirror : mirrors) {
            require(proxyIris.add(mirror.proxy), "duplicate proxy IRI: " + mirror.proxy);
            require(negativeIris.add(mirror.negative),
                    "duplicate negative IRI: " + mirror.negative);
        }

        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory factory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(projectedPath.toFile());
        Set<OWLClass> base = new HashSet<>();
        for (OWLClass name : ontology.getClassesInSignature(Imports.EXCLUDED)) {
            String iri = name.getIRI().toString();
            require(!negativeIris.contains(iri),
                    "negative source class leaked into positive projection: " + iri);
            if (!proxyIris.contains(iri) && !name.isOWLThing() && !name.isOWLNothing()) {
                base.add(name);
            }
        }
        for (String proxy : proxyIris) {
            require(ontology.containsClassInSignature(IRI.create(proxy), Imports.EXCLUDED),
                    "mapped proxy missing from projection: " + proxy);
        }

        long started = System.nanoTime();
        OWLReasoner reasoner = new ReasonerFactory().createReasoner(ontology);
        boolean consistent = reasoner.isConsistent();
        require(consistent, "positive projection is inconsistent");
        reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
        Node<OWLClass> bottomNode = reasoner.getUnsatisfiableClasses();
        Node<OWLClass> topNode = reasoner.getTopClassNode();
        long classified = System.nanoTime();

        long crossCount = 0;
        int proxiesWithCross = 0;
        int proxyUnsat = 0;
        int proxyTop = 0;
        List<String> sample = new ArrayList<>();
        List<Witness> witnesses = new ArrayList<>();
        try (OutputStream raw = Files.newOutputStream(crossPath);
                GZIPOutputStream gzip = new GZIPOutputStream(raw, 1 << 20);
                BufferedWriter output = new BufferedWriter(
                        new OutputStreamWriter(gzip, StandardCharsets.UTF_8), 1 << 20)) {
            output.write("# km-4669-hermit-projected-disjoint-v1\n");
            for (int index = 0; index < mirrors.size(); index++) {
                Mirror mirror = mirrors.get(index);
                OWLClass proxy = factory.getOWLClass(IRI.create(mirror.proxy));
                if (bottomNode.contains(proxy)) {
                    proxyUnsat++;
                }
                if (topNode.contains(proxy)) {
                    proxyTop++;
                }
                NodeSet<OWLClass> disjoint = reasoner.getDisjointClasses(proxy);
                TreeSet<String> disjointBase = new TreeSet<>();
                Map<String, OWLClass> byIri = new HashMap<>();
                for (Node<OWLClass> node : disjoint) {
                    for (OWLClass candidate : node.getEntities()) {
                        if (base.contains(candidate)) {
                            String iri = candidate.getIRI().toString();
                            disjointBase.add(iri);
                            byIri.put(iri, candidate);
                        }
                    }
                }
                if (!disjointBase.isEmpty()) {
                    proxiesWithCross++;
                }
                for (String baseIri : disjointBase) {
                    output.write("BASE_TO_NEGATIVE\t");
                    output.write(baseIri);
                    output.write('\t');
                    output.write(mirror.negative);
                    output.write('\n');
                    crossCount++;
                    if (sample.size() < 20) {
                        sample.add(baseIri + "\t" + mirror.negative);
                    }
                    if (witnesses.size() < 32) {
                        witnesses.add(new Witness(byIri.get(baseIri), proxy, mirror.negative));
                    }
                }
                if ((index + 1) % 250 == 0 || index + 1 == mirrors.size()) {
                    double elapsed = (System.nanoTime() - classified) / 1.0e9;
                    System.err.println(
                            "disjoint progress=" + (index + 1) + "/" + mirrors.size()
                                    + " cross=" + crossCount + " query_s=" + elapsed);
                }
            }
        }

        int witnessFailures = 0;
        for (Witness witness : witnesses) {
            OWLObjectIntersectionOf intersection = factory.getOWLObjectIntersectionOf(
                    witness.base, witness.proxy);
            if (reasoner.isSatisfiable(intersection)) {
                witnessFailures++;
            }
        }
        require(witnessFailures == 0,
                "getDisjointClasses witness was satisfiable: failures=" + witnessFailures);
        reasoner.dispose();
        long finished = System.nanoTime();

        String summary = "{\n"
                + "  \"schema_version\": 1,\n"
                + "  \"oracle\": \"km-4669-hermit-projected-disjoint-v1\",\n"
                + "  \"consistent\": true,\n"
                + "  \"projected\": " + jstr(projectedPath.toString()) + ",\n"
                + "  \"projected_sha256\": " + jstr(sha256File(projectedPath)) + ",\n"
                + "  \"mapping\": " + jstr(mappingPath.toString()) + ",\n"
                + "  \"mapping_sha256\": " + jstr(sha256File(mappingPath)) + ",\n"
                + "  \"cross_edges\": " + crossCount + ",\n"
                + "  \"proxies\": " + mirrors.size() + ",\n"
                + "  \"base_classes\": " + base.size() + ",\n"
                + "  \"proxies_with_cross_edges\": " + proxiesWithCross + ",\n"
                + "  \"proxy_unsatisfiable\": " + proxyUnsat + ",\n"
                + "  \"proxy_equivalent_top\": " + proxyTop + ",\n"
                + "  \"witness_rechecks\": " + witnesses.size() + ",\n"
                + "  \"witness_failures\": 0,\n"
                + "  \"classify_seconds\": "
                + String.format(Locale.ROOT, "%.6f", (classified - started) / 1.0e9) + ",\n"
                + "  \"total_seconds\": "
                + String.format(Locale.ROOT, "%.6f", (finished - started) / 1.0e9) + ",\n"
                + "  \"cross_tsv\": " + jstr(crossPath.toString()) + ",\n"
                + "  \"cross_tsv_sha256\": " + jstr(sha256File(crossPath)) + ",\n"
                + "  \"sample\": " + jsonStrings(sample) + "\n"
                + "}\n";
        Files.write(summaryPath, summary.getBytes(StandardCharsets.UTF_8));
        System.out.print(summary);
    }

    private static List<Mirror> readMapping(Path path) throws Exception {
        List<String> lines = Files.readAllLines(path, StandardCharsets.UTF_8);
        require(!lines.isEmpty()
                        && lines.get(0).equals(
                                "negative_iri\tproxy_iri\trole_iri\tfiller_iri"),
                "unexpected mapping header");
        List<Mirror> mirrors = new ArrayList<>();
        for (int index = 1; index < lines.size(); index++) {
            String[] fields = lines.get(index).split("\\t", -1);
            require(fields.length == 4, "invalid mapping row " + (index + 1));
            require(fields[1].startsWith(PROXY_PREFIX),
                    "proxy outside reserved namespace: " + fields[1]);
            mirrors.add(new Mirror(fields[0], fields[1]));
        }
        return mirrors;
    }

    private static String sha256File(Path path) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        try (InputStream input = Files.newInputStream(path)) {
            byte[] buffer = new byte[1 << 20];
            int length;
            while ((length = input.read(buffer)) >= 0) {
                if (length != 0) {
                    digest.update(buffer, 0, length);
                }
            }
        }
        StringBuilder result = new StringBuilder();
        for (byte value : digest.digest()) {
            result.append(String.format("%02x", value & 0xff));
        }
        return result.toString();
    }

    private static String jsonStrings(List<String> strings) {
        StringBuilder result = new StringBuilder("[");
        for (int index = 0; index < strings.size(); index++) {
            if (index != 0) {
                result.append(", ");
            }
            result.append(jstr(strings.get(index)));
        }
        return result.append(']').toString();
    }

    private static String jstr(String value) {
        StringBuilder result = new StringBuilder("\"");
        for (int index = 0; index < value.length(); index++) {
            char c = value.charAt(index);
            switch (c) {
                case '\"': result.append("\\\""); break;
                case '\\': result.append("\\\\"); break;
                case '\n': result.append("\\n"); break;
                case '\r': result.append("\\r"); break;
                case '\t': result.append("\\t"); break;
                default:
                    if (c < 0x20) {
                        result.append(String.format("\\u%04x", (int) c));
                    } else {
                        result.append(c);
                    }
            }
        }
        return result.append('\"').toString();
    }

    private static void require(boolean condition, String message) {
        if (!condition) {
            throw new IllegalArgumentException(message);
        }
    }
}
