import java.io.BufferedWriter;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;

/**
 * Enumerate every named base/proxy pair that can gain a disjoint-root type only
 * by jointly satisfying an explicit projected-ontology conjunction.
 *
 * <p>The output is a candidate superset. A separate conservative-extension
 * batch classifies fresh names equivalent to each candidate intersection and
 * keeps exactly the names equivalent to bottom.</p>
 */
public final class ElkCandidatePairs4669 {
    private static final String PROXY_PREFIX = "urn:km:oracle:4669:positive-proxy:";

    private static final class Gci {
        final OWLObjectIntersectionOf left;
        final OWLClassExpression right;

        Gci(OWLObjectIntersectionOf left, OWLClassExpression right) {
            this.left = left;
            this.right = right;
        }
    }

    private ElkCandidatePairs4669() {}

    public static void main(String[] args) throws Exception {
        if (args.length < 3 || args.length > 4) {
            System.err.println(
                    "Usage: ElkCandidatePairs4669 PROJECTED.ofn CANDIDATES.tsv SUMMARY.json "
                            + "[--roots-only|--emit-augmented=PATH]");
            System.exit(2);
        }
        Path projected = Paths.get(args[0]).toAbsolutePath().normalize();
        Path outputPath = Paths.get(args[1]).toAbsolutePath().normalize();
        Path summaryPath = Paths.get(args[2]).toAbsolutePath().normalize();
        Files.createDirectories(outputPath.getParent());
        Files.createDirectories(summaryPath.getParent());

        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory factory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(projected.toFile());
        Set<OWLClass> base = new HashSet<>();
        Set<OWLClass> proxies = new HashSet<>();
        for (OWLClass cls : ontology.getClassesInSignature(Imports.EXCLUDED)) {
            if (cls.isOWLThing() || cls.isOWLNothing()) {
                continue;
            }
            if (cls.getIRI().toString().startsWith(PROXY_PREFIX)) {
                proxies.add(cls);
            } else {
                base.add(cls);
            }
        }
        require(proxies.size() == 36_495, "unexpected proxy count: " + proxies.size());

        List<OWLClass> disjointRoots = new ArrayList<>();
        int disjointAxioms = 0;
        for (OWLDisjointClassesAxiom axiom : ontology.getAxioms(
                AxiomType.DISJOINT_CLASSES, Imports.EXCLUDED)) {
            disjointAxioms++;
            List<OWLClassExpression> expressions = axiom.getClassExpressionsAsList();
            require(expressions.size() == 2, "non-binary disjointness axiom");
            for (OWLClassExpression expression : expressions) {
                require(!expression.isAnonymous(), "anonymous disjointness operand");
                disjointRoots.add(expression.asOWLClass());
            }
        }
        require(disjointAxioms == 6, "unexpected disjointness count: " + disjointAxioms);

        List<Gci> gcis = new ArrayList<>();
        for (OWLSubClassOfAxiom axiom : ontology.getAxioms(
                AxiomType.SUBCLASS_OF, Imports.EXCLUDED)) {
            if (axiom.getSubClass() instanceof OWLObjectIntersectionOf) {
                gcis.add(new Gci(
                        (OWLObjectIntersectionOf) axiom.getSubClass(), axiom.getSuperClass()));
            }
        }
        for (OWLEquivalentClassesAxiom axiom : ontology.getAxioms(
                AxiomType.EQUIVALENT_CLASSES, Imports.EXCLUDED)) {
            List<OWLClassExpression> expressions = axiom.getClassExpressionsAsList();
            for (OWLClassExpression left : expressions) {
                if (!(left instanceof OWLObjectIntersectionOf)) {
                    continue;
                }
                for (OWLClassExpression right : expressions) {
                    if (!left.equals(right)) {
                        gcis.add(new Gci((OWLObjectIntersectionOf) left, right));
                    }
                }
            }
        }

        Map<OWLClassExpression, OWLClass> representatives = new HashMap<>();
        int definerIndex = 0;
        for (Gci gci : gcis) {
            List<OWLClassExpression> expressions = new ArrayList<>();
            expressions.add(gci.right);
            expressions.addAll(gci.left.getOperands());
            for (OWLClassExpression expression : expressions) {
                if (!expression.isAnonymous() || representatives.containsKey(expression)) {
                    continue;
                }
                OWLClass definer = factory.getOWLClass(IRI.create(
                        "urn:km:oracle:4669:candidate-definer:" + definerIndex++));
                require(!ontology.containsClassInSignature(definer.getIRI()),
                        "candidate definer IRI collision");
                manager.addAxiom(
                        ontology, factory.getOWLEquivalentClassesAxiom(definer, expression));
                representatives.put(expression, definer);
            }
        }
        if (args.length == 4 && args[3].startsWith("--emit-augmented=")) {
            Path augmented = Paths.get(
                    args[3].substring("--emit-augmented=".length()))
                    .toAbsolutePath().normalize();
            Files.createDirectories(augmented.getParent());
            manager.saveOntology(
                    ontology,
                    new FunctionalSyntaxDocumentFormat(),
                    IRI.create(augmented.toUri()));
            System.err.println(
                    "augmented=" + augmented
                            + " definers=" + representatives.size()
                            + " gcis=" + gcis.size());
            return;
        }

        OWLReasonerFactory reasonerFactory = (OWLReasonerFactory) Class
                .forName("org.semanticweb.elk.owlapi.ElkReasonerFactory")
                .getDeclaredConstructor()
                .newInstance();
        OWLReasoner reasoner = reasonerFactory.createReasoner(ontology);
        require(reasoner.isConsistent(), "positive projection is inconsistent");
        reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
        int rootsWithProxyDescendants = 0;
        for (OWLClass root : new LinkedHashSet<>(disjointRoots)) {
            Set<OWLClass> descendants = namedSubclasses(reasoner, root);
            int baseDescendants = 0;
            int proxyDescendants = 0;
            for (OWLClass descendant : descendants) {
                if (base.contains(descendant)) {
                    baseDescendants++;
                } else if (proxies.contains(descendant)) {
                    proxyDescendants++;
                }
            }
            System.err.println(
                    "root=" + root.getIRI()
                            + " base_descendants=" + baseDescendants
                            + " proxy_descendants=" + proxyDescendants);
            if (proxyDescendants != 0) {
                rootsWithProxyDescendants++;
            }
        }
        if (args.length == 4) {
            require(args[3].equals("--roots-only"), "unknown option: " + args[3]);
            reasoner.dispose();
            return;
        }
        TreeSet<String> candidates = new TreeSet<>();
        Map<OWLClass, Set<OWLClass>> descendantCache = new HashMap<>();
        Set<OWLClass> proxyBearingOperands = new HashSet<>();
        int relevant = 0;
        int nonPrime = 0;
        for (Gci gci : gcis) {
            List<OWLClassExpression> operands = new ArrayList<>(gci.left.getOperands());
            require(operands.size() >= 2, "intersection has fewer than two operands");
            require(operands.size() <= 16,
                    "intersection has too many operands for exact split enumeration: "
                            + operands.size());
            OWLClass rightRepresentative = representative(gci.right, representatives);
            relevant++;
            boolean singletonConclusion = false;
            for (OWLClassExpression operand : operands) {
                if (isSubsumed(
                        reasoner, representative(operand, representatives), rightRepresentative)) {
                    singletonConclusion = true;
                    break;
                }
            }
            if (singletonConclusion) {
                continue;
            }
            nonPrime++;
            int full = (1 << operands.size()) - 1;
            // Complementary masks describe the same unordered split. Fix
            // operand zero on the left and exclude the all-left split.
            for (int mask = 1; mask < full; mask++) {
                if ((mask & 1) == 0) {
                    continue;
                }
                Set<OWLClass> left = null;
                Set<OWLClass> right = null;
                for (int index = 0; index < operands.size(); index++) {
                    OWLClass operand = representative(operands.get(index), representatives);
                    Set<OWLClass> descendants = descendantCache.computeIfAbsent(
                            operand, ignored -> namedSubclasses(reasoner, operand));
                    if (!proxyBearingOperands.contains(operand)) {
                        for (OWLClass descendant : descendants) {
                            if (proxies.contains(descendant)) {
                                proxyBearingOperands.add(operand);
                                break;
                            }
                        }
                    }
                    if ((mask & (1 << index)) != 0) {
                        left = intersect(left, descendants);
                    } else {
                        right = intersect(right, descendants);
                    }
                }
                if (left == null || right == null || left.isEmpty() || right.isEmpty()) {
                    continue;
                }
                addCrossPairs(candidates, left, right, base, proxies);
            }
        }
        reasoner.dispose();

        try (BufferedWriter output = Files.newBufferedWriter(outputPath, StandardCharsets.UTF_8)) {
            output.write("base_iri\tproxy_iri\n");
            for (String candidate : candidates) {
                output.write(candidate);
                output.write('\n');
            }
        }
        System.err.println(
                "base=" + base.size()
                        + " proxies=" + proxies.size()
                        + " gcis=" + gcis.size()
                        + " definers=" + representatives.size()
                        + " checked_gcis=" + relevant
                        + " nonprime_gcis=" + nonPrime
                        + " distinct_operands=" + descendantCache.size()
                        + " proxy_bearing_operands=" + proxyBearingOperands.size()
                        + " candidate_pairs=" + candidates.size());
        String summary = "{\n"
                + "  \"schema_version\": 1,\n"
                + "  \"certificate\": \"km-4669-elk-zero-cross-v1\",\n"
                + "  \"passed\": "
                + (candidates.isEmpty()
                        && proxyBearingOperands.isEmpty()
                        && rootsWithProxyDescendants == 0)
                + ",\n"
                + "  \"projected_sha256\": \"" + sha256File(projected) + "\",\n"
                + "  \"candidate_tsv_sha256\": \"" + sha256File(outputPath) + "\",\n"
                + "  \"base_classes\": " + base.size() + ",\n"
                + "  \"proxies\": " + proxies.size() + ",\n"
                + "  \"disjoint_axioms\": " + disjointAxioms + ",\n"
                + "  \"checked_gcis\": " + relevant + ",\n"
                + "  \"definers\": " + representatives.size() + ",\n"
                + "  \"distinct_operands\": " + descendantCache.size() + ",\n"
                + "  \"proxy_bearing_operands\": " + proxyBearingOperands.size() + ",\n"
                + "  \"roots_with_proxy_descendants\": " + rootsWithProxyDescendants + ",\n"
                + "  \"candidate_pairs\": " + candidates.size() + "\n"
                + "}\n";
        Files.write(summaryPath, summary.getBytes(StandardCharsets.UTF_8));
    }

    private static OWLClass representative(
            OWLClassExpression expression,
            Map<OWLClassExpression, OWLClass> representatives) {
        return expression.isAnonymous()
                ? representatives.get(expression)
                : expression.asOWLClass();
    }

    private static boolean isSubsumed(
            OWLReasoner reasoner, OWLClass sub, OWLClass sup) {
        return sub.equals(sup)
                || reasoner.getEquivalentClasses(sub).contains(sup)
                || reasoner.getSuperClasses(sub, false).containsEntity(sup);
    }

    private static Set<OWLClass> namedSubclasses(
            OWLReasoner reasoner, OWLClass expression) {
        Set<OWLClass> result = new HashSet<>(
                reasoner.getSubClasses(expression, false).getFlattened());
        result.addAll(reasoner.getEquivalentClasses(expression).getEntities());
        result.removeIf(cls -> cls.isOWLNothing());
        return result;
    }

    private static Set<OWLClass> intersect(Set<OWLClass> current, Set<OWLClass> next) {
        if (current == null) {
            return new HashSet<>(next);
        }
        current.retainAll(next);
        return current;
    }

    private static void addCrossPairs(
            Set<String> output,
            Set<OWLClass> left,
            Set<OWLClass> right,
            Set<OWLClass> base,
            Set<OWLClass> proxies) {
        for (OWLClass l : left) {
            if (base.contains(l)) {
                for (OWLClass r : right) {
                    if (proxies.contains(r)) {
                        output.add(l.getIRI() + "\t" + r.getIRI());
                    }
                }
            } else if (proxies.contains(l)) {
                for (OWLClass r : right) {
                    if (base.contains(r)) {
                        output.add(r.getIRI() + "\t" + l.getIRI());
                    }
                }
            }
        }
    }

    private static void require(boolean condition, String message) {
        if (!condition) {
            throw new IllegalStateException(message);
        }
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
}
