import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDeclarationAxiom;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLInverseObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.parameters.Imports;

/**
 * Independent OWLAPI projection for ORE ontology 4669.
 *
 * <p>For every private source definition N == not (exists R.F), this program
 * removes N and introduces a fresh P == exists R.F.  The resulting ontology is
 * a conservative positive extension of the base vocabulary.  An external OWL
 * reasoner can classify the P hierarchy; complement duality then reconstructs
 * the exact N hierarchy by reversing P subsumptions.</p>
 *
 * <p>The program fails closed unless the source has the separation shape used
 * by the reconstruction checker.  In particular, the negative names must be
 * private and the remaining TBox must be positive EL plus named disjointness,
 * with no top GCI, ABox, nominal, datatype, rule, universal role, or reflexive
 * role. Base-to-negative cross edges are recovered separately through a
 * complete reasoner's disjoint-class queries over the positive projection.</p>
 *
 * Usage:
 *   java ProxyProjection4669 SOURCE.owl PROJECTED.ofn MAPPING.tsv CERTIFICATE.json
 */
public final class ProxyProjection4669 {
    private static final String PROXY_PREFIX = "urn:km:oracle:4669:positive-proxy:";

    private static final class Mirror {
        final OWLClass negative;
        final OWLObjectProperty role;
        final OWLClass filler;
        final OWLEquivalentClassesAxiom definition;
        OWLClass proxy;

        Mirror(
                OWLClass negative,
                OWLObjectProperty role,
                OWLClass filler,
                OWLEquivalentClassesAxiom definition) {
            this.negative = negative;
            this.role = role;
            this.filler = filler;
            this.definition = definition;
        }
    }

    private ProxyProjection4669() {}

    public static void main(String[] args) throws Exception {
        if (args.length != 4) {
            System.err.println(
                    "Usage: ProxyProjection4669 SOURCE.owl PROJECTED.ofn MAPPING.tsv CERTIFICATE.json");
            System.exit(2);
        }
        Path sourcePath = Paths.get(args[0]).toAbsolutePath().normalize();
        Path projectedPath = Paths.get(args[1]).toAbsolutePath().normalize();
        Path mappingPath = Paths.get(args[2]).toAbsolutePath().normalize();
        Path certificatePath = Paths.get(args[3]).toAbsolutePath().normalize();
        require(Files.isRegularFile(sourcePath), "source ontology does not exist: " + sourcePath);
        Files.createDirectories(projectedPath.getParent());
        Files.createDirectories(mappingPath.getParent());
        Files.createDirectories(certificatePath.getParent());

        OWLOntologyManager sourceManager = OWLManager.createOWLOntologyManager();
        OWLOntology source = sourceManager.loadOntologyFromOntologyDocument(sourcePath.toFile());
        OWLDataFactory dataFactory = sourceManager.getOWLDataFactory();

        require(source.getImportsDeclarations().isEmpty(), "imports are not permitted in the certificate");
        require(source.getABoxAxioms(Imports.EXCLUDED).isEmpty(), "ABox axioms are not permitted");
        require(source.getIndividualsInSignature(Imports.EXCLUDED).isEmpty(),
                "individuals are not permitted");
        require(source.getAxioms(AxiomType.SWRL_RULE, Imports.EXCLUDED).isEmpty(),
                "SWRL rules are not permitted");
        require(source.getDataPropertiesInSignature(Imports.EXCLUDED).isEmpty(),
                "data properties are not permitted");
        require(source.getAxioms(AxiomType.DATATYPE_DEFINITION, Imports.EXCLUDED).isEmpty(),
                "datatype definitions are not permitted");
        require(source.getAxioms(AxiomType.REFLEXIVE_OBJECT_PROPERTY, Imports.EXCLUDED).isEmpty(),
                "reflexive roles are not permitted by the isolated-element proof");
        for (OWLLogicalAxiom axiom : source.getLogicalAxioms(Imports.EXCLUDED)) {
            for (OWLObjectProperty property : axiom.getObjectPropertiesInSignature()) {
                require(!property.isOWLTopObjectProperty(),
                        "universal role is not permitted by the isolated-element proof: " + axiom);
            }
        }

        List<Mirror> mirrors = collectMirrors(source);
        require(!mirrors.isEmpty(), "no exact negative-existential mirror definitions found");
        Collections.sort(mirrors, Comparator.comparing(m -> m.negative.getIRI().toString()));

        Map<OWLClass, Mirror> byNegative = new HashMap<>();
        Set<OWLEquivalentClassesAxiom> mirrorAxioms = new HashSet<>();
        for (Mirror mirror : mirrors) {
            require(!mirror.negative.isOWLThing() && !mirror.negative.isOWLNothing(),
                    "builtin class used as negative mirror: " + mirror.negative);
            require(byNegative.put(mirror.negative, mirror) == null,
                    "negative class has multiple mirror definitions: " + mirror.negative.getIRI());
            mirrorAxioms.add(mirror.definition);
            require(!source.getDeclarationAxioms(mirror.negative).isEmpty(),
                    "negative mirror is not declared: " + mirror.negative.getIRI());
        }

        Map<OWLClass, Integer> logicalOccurrences = new HashMap<>();
        Map<OWLClass, OWLLogicalAxiom> soleLogicalUse = new HashMap<>();
        for (OWLLogicalAxiom axiom : source.getLogicalAxioms(Imports.EXCLUDED)) {
            for (OWLClass name : axiom.getClassesInSignature()) {
                if (byNegative.containsKey(name)) {
                    logicalOccurrences.put(
                            name, logicalOccurrences.getOrDefault(name, 0) + 1);
                    soleLogicalUse.put(name, axiom);
                }
            }
        }
        for (Mirror mirror : mirrors) {
            int occurrences = logicalOccurrences.getOrDefault(mirror.negative, 0);
            require(occurrences == 1
                            && mirror.definition.equals(soleLogicalUse.get(mirror.negative)),
                    "negative mirror is not private to its definition: "
                            + mirror.negative.getIRI() + " occurrences=" + occurrences);
        }

        int complementCount = 0;
        for (OWLLogicalAxiom axiom : source.getLogicalAxioms(Imports.EXCLUDED)) {
            int inAxiom = 0;
            for (OWLClassExpression expression : axiom.getNestedClassExpressions()) {
                if (expression instanceof OWLObjectComplementOf) {
                    complementCount++;
                    inAxiom++;
                }
            }
            if (inAxiom != 0) {
                require(mirrorAxioms.contains(axiom) && inAxiom == 1,
                        "complement occurs outside one exact mirror definition: " + axiom);
            }
        }
        require(complementCount == mirrors.size(),
                "complement/mirror count differs: complements=" + complementCount
                        + " mirrors=" + mirrors.size());

        Set<OWLClass> negativeNames = new HashSet<>(byNegative.keySet());
        Set<OWLObjectProperty> mirrorRoles = new HashSet<>();
        for (Mirror mirror : mirrors) {
            mirrorRoles.add(mirror.role);
        }
        Set<OWLObjectProperty> roleComponent = roleComponent(source, mirrorRoles);

        int subclassAxioms = 0;
        int equivalentAxioms = 0;
        int disjointAxioms = 0;
        int domainAxioms = source.getAxioms(
                AxiomType.OBJECT_PROPERTY_DOMAIN, Imports.EXCLUDED).size();
        int rangeAxioms = source.getAxioms(
                AxiomType.OBJECT_PROPERTY_RANGE, Imports.EXCLUDED).size();
        for (OWLObjectPropertyDomainAxiom domain
                : source.getAxioms(AxiomType.OBJECT_PROPERTY_DOMAIN, Imports.EXCLUDED)) {
            require(isPositiveEl(domain.getDomain(), negativeNames),
                    "non-positive object-property domain remains: " + domain);
        }
        for (OWLObjectPropertyRangeAxiom range
                : source.getAxioms(AxiomType.OBJECT_PROPERTY_RANGE, Imports.EXCLUDED)) {
            require(isPositiveEl(range.getRange(), negativeNames),
                    "non-positive object-property range remains: " + range);
        }
        for (OWLAxiom rawAxiom : source.getTBoxAxioms(Imports.EXCLUDED)) {
            // OWLAPI's broad TBox view also contains role characteristics such
            // as FunctionalObjectProperty. They are audited by the logical-
            // axiom allowlist below and are vacuous on the isolated element.
            if (!(rawAxiom instanceof OWLClassAxiom)) {
                continue;
            }
            OWLClassAxiom axiom = (OWLClassAxiom) rawAxiom;
            if (mirrorAxioms.contains(axiom)) {
                continue;
            }
            if (axiom instanceof OWLSubClassOfAxiom) {
                OWLSubClassOfAxiom sub = (OWLSubClassOfAxiom) axiom;
                require(!sub.getSubClass().isOWLThing(), "top GCI is not permitted: " + sub);
                require(isPositiveEl(sub.getSubClass(), negativeNames)
                                && isPositiveEl(sub.getSuperClass(), negativeNames),
                        "non-positive subclass axiom remains: " + sub);
                subclassAxioms++;
            } else if (axiom instanceof OWLEquivalentClassesAxiom) {
                OWLEquivalentClassesAxiom equivalent = (OWLEquivalentClassesAxiom) axiom;
                for (OWLClassExpression expression : equivalent.getClassExpressions()) {
                    require(!expression.isOWLThing(),
                            "top equivalence is not permitted: " + equivalent);
                    require(isPositiveEl(expression, negativeNames),
                            "non-positive equivalence remains: " + equivalent);
                }
                equivalentAxioms++;
            } else if (axiom instanceof OWLDisjointClassesAxiom) {
                OWLDisjointClassesAxiom disjoint = (OWLDisjointClassesAxiom) axiom;
                require(disjoint.getClassExpressions().size() >= 2,
                        "degenerate disjointness axiom: " + disjoint);
                for (OWLClassExpression expression : disjoint.getClassExpressions()) {
                    require(!expression.isAnonymous()
                                    && !expression.isOWLNothing()
                                    && !negativeNames.contains(expression.asOWLClass()),
                            "disjointness is not over positive named classes: " + disjoint);
                }
                disjointAxioms++;
            } else if (axiom instanceof OWLObjectPropertyDomainAxiom) {
                // Validated independently of OWLAPI's TBox partition above.
            } else if (axiom instanceof OWLObjectPropertyRangeAxiom) {
                // Validated independently of OWLAPI's TBox partition above.
            } else {
                require(false, "unsupported class axiom in separation certificate: " + axiom);
            }
        }
        for (OWLLogicalAxiom axiom : source.getLogicalAxioms(Imports.EXCLUDED)) {
            boolean allowed = mirrorAxioms.contains(axiom)
                    || axiom instanceof OWLSubClassOfAxiom
                    || axiom instanceof OWLEquivalentClassesAxiom
                    || axiom instanceof OWLDisjointClassesAxiom
                    || axiom instanceof OWLObjectPropertyDomainAxiom
                    || axiom instanceof OWLObjectPropertyRangeAxiom
                    || axiom instanceof OWLObjectPropertyAxiom;
            require(allowed, "unsupported logical axiom in projection certificate: " + axiom);
        }

        Set<IRI> sourceClassIris = new HashSet<>();
        for (OWLClass owlClass : source.getClassesInSignature(Imports.EXCLUDED)) {
            sourceClassIris.add(owlClass.getIRI());
        }
        for (Mirror mirror : mirrors) {
            String digest = sha256Text(mirror.negative.getIRI().toString());
            IRI proxyIri = IRI.create(PROXY_PREFIX + digest);
            require(!sourceClassIris.contains(proxyIri), "fresh proxy IRI collision: " + proxyIri);
            mirror.proxy = dataFactory.getOWLClass(proxyIri);
        }

        OWLOntologyManager projectedManager = OWLManager.createOWLOntologyManager();
        OWLDataFactory projectedFactory = projectedManager.getOWLDataFactory();
        OWLOntology projected = projectedManager.createOntology(
                IRI.create("urn:km:oracle:4669:positive-projection"));
        Set<OWLAxiom> copied = new LinkedHashSet<>();
        for (OWLAxiom axiom : source.getAxioms(Imports.EXCLUDED)) {
            if (mirrorAxioms.contains(axiom)) {
                continue;
            }
            if (axiom instanceof OWLDeclarationAxiom
                    && ((OWLDeclarationAxiom) axiom).getEntity().isOWLClass()
                    && negativeNames.contains(
                            ((OWLDeclarationAxiom) axiom).getEntity().asOWLClass())) {
                continue;
            }
            copied.add(axiom);
        }
        projectedManager.addAxioms(projected, copied);
        for (Mirror mirror : mirrors) {
            OWLObjectSomeValuesFrom positive = projectedFactory.getOWLObjectSomeValuesFrom(
                    projectedFactory.getOWLObjectProperty(mirror.role.getIRI()),
                    projectedFactory.getOWLClass(mirror.filler.getIRI()));
            OWLClass proxy = projectedFactory.getOWLClass(mirror.proxy.getIRI());
            projectedManager.addAxiom(projected, projectedFactory.getOWLDeclarationAxiom(proxy));
            projectedManager.addAxiom(
                    projected, projectedFactory.getOWLEquivalentClassesAxiom(proxy, positive));
        }
        projectedManager.saveOntology(
                projected,
                new FunctionalSyntaxDocumentFormat(),
                IRI.create(projectedPath.toFile()));

        StringBuilder mapping = new StringBuilder();
        mapping.append("negative_iri\tproxy_iri\trole_iri\tfiller_iri\n");
        for (Mirror mirror : mirrors) {
            mapping.append(mirror.negative.getIRI()).append('\t')
                    .append(mirror.proxy.getIRI()).append('\t')
                    .append(mirror.role.getIRI()).append('\t')
                    .append(mirror.filler.getIRI()).append('\n');
        }
        Files.write(mappingPath, mapping.toString().getBytes(StandardCharsets.UTF_8));

        int sourceDeclaredClasses = 0;
        for (OWLDeclarationAxiom declaration
                : source.getAxioms(AxiomType.DECLARATION, Imports.EXCLUDED)) {
            if (declaration.getEntity().isOWLClass()
                    && !declaration.getEntity().asOWLClass().isOWLThing()
                    && !declaration.getEntity().asOWLClass().isOWLNothing()) {
                sourceDeclaredClasses++;
            }
        }
        int projectedDeclaredClasses = 0;
        for (OWLDeclarationAxiom declaration
                : projected.getAxioms(AxiomType.DECLARATION, Imports.EXCLUDED)) {
            if (declaration.getEntity().isOWLClass()
                    && !declaration.getEntity().asOWLClass().isOWLThing()
                    && !declaration.getEntity().asOWLClass().isOWLNothing()) {
                projectedDeclaredClasses++;
            }
        }

        List<String> mirrorRoleIris = iris(mirrorRoles);
        List<String> componentRoleIris = iris(roleComponent);
        String certificate = "{\n"
                + "  \"schema_version\": 1,\n"
                + "  \"certificate\": \"private-negative-existential-projection-v2\",\n"
                + "  \"passed\": true,\n"
                + "  \"source\": " + jstr(sourcePath.toString()) + ",\n"
                + "  \"source_sha256\": " + jstr(sha256File(sourcePath)) + ",\n"
                + "  \"projected\": " + jstr(projectedPath.toString()) + ",\n"
                + "  \"projected_sha256\": " + jstr(sha256File(projectedPath)) + ",\n"
                + "  \"mapping\": " + jstr(mappingPath.toString()) + ",\n"
                + "  \"mapping_sha256\": " + jstr(sha256File(mappingPath)) + ",\n"
                + "  \"proxy_prefix\": " + jstr(PROXY_PREFIX) + ",\n"
                + "  \"source_declared_classes\": " + sourceDeclaredClasses + ",\n"
                + "  \"projected_declared_classes\": " + projectedDeclaredClasses + ",\n"
                + "  \"negative_mirrors\": " + mirrors.size() + ",\n"
                + "  \"complement_occurrences\": " + complementCount + ",\n"
                + "  \"positive_subclass_axioms\": " + subclassAxioms + ",\n"
                + "  \"positive_equivalent_axioms\": " + equivalentAxioms + ",\n"
                + "  \"named_disjoint_axioms\": " + disjointAxioms + ",\n"
                + "  \"positive_object_property_domain_axioms\": " + domainAxioms + ",\n"
                + "  \"positive_object_property_range_axioms\": " + rangeAxioms + ",\n"
                + "  \"mirror_roles\": " + jsonStrings(mirrorRoleIris) + ",\n"
                + "  \"mirror_role_component\": " + jsonStrings(componentRoleIris) + ",\n"
                + "  \"cross_region_contract\": {\n"
                + "    \"negative_names_private\": true,\n"
                + "    \"remaining_tbox_positive_el_plus_named_disjointness\": true,\n"
                + "    \"no_top_gci_or_bottom_constructor\": true,\n"
                + "    \"no_reflexive_or_universal_role\": true,\n"
                + "    \"base_to_negative_requires_disjoint_oracle\": true,\n"
                + "    \"negative_to_base_absent_by_isolated_element\": true\n"
                + "  }\n"
                + "}\n";
        Files.write(certificatePath, certificate.getBytes(StandardCharsets.UTF_8));
        System.out.print(certificate);
    }

    private static List<Mirror> collectMirrors(OWLOntology ontology) {
        List<Mirror> result = new ArrayList<>();
        for (OWLEquivalentClassesAxiom axiom
                : ontology.getAxioms(AxiomType.EQUIVALENT_CLASSES, Imports.EXCLUDED)) {
            List<OWLClassExpression> expressions = axiom.getClassExpressionsAsList();
            if (expressions.size() != 2) {
                continue;
            }
            Mirror mirror = exactMirror(expressions.get(0), expressions.get(1), axiom);
            if (mirror == null) {
                mirror = exactMirror(expressions.get(1), expressions.get(0), axiom);
            }
            if (mirror != null) {
                result.add(mirror);
            }
        }
        return result;
    }

    private static Mirror exactMirror(
            OWLClassExpression name,
            OWLClassExpression expression,
            OWLEquivalentClassesAxiom axiom) {
        if (name.isAnonymous() || !(expression instanceof OWLObjectComplementOf)) {
            return null;
        }
        OWLClassExpression operand = ((OWLObjectComplementOf) expression).getOperand();
        if (!(operand instanceof OWLObjectSomeValuesFrom)) {
            return null;
        }
        OWLObjectSomeValuesFrom some = (OWLObjectSomeValuesFrom) operand;
        if (some.getProperty().isAnonymous() || some.getFiller().isAnonymous()) {
            return null;
        }
        return new Mirror(
                name.asOWLClass(),
                some.getProperty().asOWLObjectProperty(),
                some.getFiller().asOWLClass(),
                axiom);
    }

    private static boolean isPositiveEl(
            OWLClassExpression expression,
            Set<OWLClass> negativeNames) {
        if (!expression.isAnonymous()) {
            OWLClass name = expression.asOWLClass();
            return !name.isOWLNothing() && !negativeNames.contains(name);
        }
        if (expression instanceof OWLObjectIntersectionOf) {
            for (OWLClassExpression operand
                    : ((OWLObjectIntersectionOf) expression).getOperands()) {
                if (!isPositiveEl(operand, negativeNames)) {
                    return false;
                }
            }
            return true;
        }
        if (expression instanceof OWLObjectSomeValuesFrom) {
            OWLObjectSomeValuesFrom some = (OWLObjectSomeValuesFrom) expression;
            return !some.getProperty().isAnonymous()
                    && !some.getProperty().asOWLObjectProperty().isOWLTopObjectProperty()
                    && isPositiveEl(some.getFiller(), negativeNames);
        }
        return false;
    }

    private static Set<OWLObjectProperty> roleComponent(
            OWLOntology ontology,
            Set<OWLObjectProperty> roots) {
        Map<OWLObjectProperty, Set<OWLObjectProperty>> adjacency = new HashMap<>();
        for (OWLSubObjectPropertyOfAxiom axiom
                : ontology.getAxioms(AxiomType.SUB_OBJECT_PROPERTY, Imports.EXCLUDED)) {
            connect(adjacency, named(axiom.getSubProperty()), named(axiom.getSuperProperty()));
        }
        for (OWLInverseObjectPropertiesAxiom axiom
                : ontology.getAxioms(AxiomType.INVERSE_OBJECT_PROPERTIES, Imports.EXCLUDED)) {
            connect(adjacency, named(axiom.getFirstProperty()), named(axiom.getSecondProperty()));
        }
        for (OWLEquivalentObjectPropertiesAxiom axiom
                : ontology.getAxioms(AxiomType.EQUIVALENT_OBJECT_PROPERTIES, Imports.EXCLUDED)) {
            List<OWLObjectPropertyExpression> properties =
                    new ArrayList<>(axiom.getProperties());
            for (int i = 0; i < properties.size(); i++) {
                for (int j = i + 1; j < properties.size(); j++) {
                    connect(adjacency, named(properties.get(i)), named(properties.get(j)));
                }
            }
        }
        Set<OWLObjectProperty> component = new HashSet<>(roots);
        ArrayDeque<OWLObjectProperty> queue = new ArrayDeque<>(roots);
        while (!queue.isEmpty()) {
            OWLObjectProperty current = queue.removeFirst();
            for (OWLObjectProperty next
                    : adjacency.getOrDefault(current, Collections.<OWLObjectProperty>emptySet())) {
                if (component.add(next)) {
                    queue.addLast(next);
                }
            }
        }
        return component;
    }

    private static OWLObjectProperty named(OWLObjectPropertyExpression expression) {
        return expression.getNamedProperty();
    }

    private static void connect(
            Map<OWLObjectProperty, Set<OWLObjectProperty>> adjacency,
            OWLObjectProperty left,
            OWLObjectProperty right) {
        adjacency.computeIfAbsent(left, ignored -> new HashSet<>()).add(right);
        adjacency.computeIfAbsent(right, ignored -> new HashSet<>()).add(left);
    }

    private static List<String> iris(Set<OWLObjectProperty> properties) {
        List<String> result = new ArrayList<>();
        for (OWLObjectProperty property : properties) {
            result.add(property.getIRI().toString());
        }
        Collections.sort(result);
        return result;
    }

    private static String sha256Text(String text) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        byte[] hash = digest.digest(text.getBytes(StandardCharsets.UTF_8));
        return hex(hash);
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
        return hex(digest.digest());
    }

    private static String hex(byte[] bytes) {
        StringBuilder result = new StringBuilder(bytes.length * 2);
        for (byte value : bytes) {
            result.append(String.format("%02x", value & 0xff));
        }
        return result.toString();
    }

    private static String jsonStrings(List<String> strings) {
        StringBuilder result = new StringBuilder("[");
        for (int i = 0; i < strings.size(); i++) {
            if (i != 0) {
                result.append(", ");
            }
            result.append(jstr(strings.get(i)));
        }
        return result.append(']').toString();
    }

    private static String jstr(String value) {
        StringBuilder result = new StringBuilder("\"");
        for (int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
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
