package org.bioontology.kobayashimarust.protege;

import com.google.gson.Gson;
import com.google.gson.JsonParseException;
import org.semanticweb.owl.explanation.api.Explanation;
import org.semanticweb.owl.explanation.api.ExplanationException;
import org.semanticweb.owl.explanation.api.ExplanationGenerator;
import org.semanticweb.owl.explanation.api.ExplanationGeneratorInterruptedException;
import org.semanticweb.owl.explanation.api.ExplanationProgressMonitor;
import org.semanticweb.owl.explanation.api.UnsupportedEntailmentException;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.parameters.Imports;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.TimeUnit;

/**
 * OWL Explanation API adapter for KM's source-axiom explanation protocol.
 *
 * <p>The generator supports named {@link OWLSubClassOfAxiom} entailments,
 * named-class unsatisfiability ({@code A SubClassOf owl:Nothing}), and the
 * explanation-workbench inconsistency marker ({@code owl:Thing SubClassOf
 * owl:Nothing}). Every returned {@link Explanation} contains OWL API axioms
 * parsed from the source functional syntax emitted by KM.</p>
 */
public final class KMExplanationGenerator implements ExplanationGenerator<OWLAxiom> {

    private static final int SCHEMA_VERSION = 2;

    private final OWLOntology ontology;
    private final ExplanationProgressMonitor<OWLAxiom> progressMonitor;
    private final KMExplanationConfiguration configuration;
    private final Gson gson = new Gson();

    KMExplanationGenerator(
            OWLOntology ontology,
            ExplanationProgressMonitor<OWLAxiom> progressMonitor,
            KMExplanationConfiguration configuration) {
        try {
            // Bind enumeration to one source revision even if the caller later
            // mutates the live OWLAPI ontology.
            this.ontology = FlattenedOntology.snapshot(ontology);
        } catch (Exception error) {
            throw new ExplanationException(
                    "Could not snapshot the ontology for KM explanations", error);
        }
        this.progressMonitor = progressMonitor;
        this.configuration = configuration;
    }

    @Override
    public Set<Explanation<OWLAxiom>> getExplanations(OWLAxiom entailment)
            throws ExplanationException {
        KMExplanationRun run = generateBounded(
                entailment, configuration.getAllJustificationsCap());
        if (!run.isEnumerationComplete()) {
            throw new ExplanationException(
                    "KM did not exhaust all justifications within the configured cap/bounds; "
                            + "use getExplanations(entailment, limit) or raise "
                            + "km.explain.all.justifications.cap and km.explain.max.checks");
        }
        return run.getExplanations();
    }

    @Override
    public Set<Explanation<OWLAxiom>> getExplanations(OWLAxiom entailment, int limit)
            throws ExplanationException {
        // Validate the advertised entailment surface even when the caller asks
        // for zero results. Unsupported queries must fail explicitly, never
        // masquerade as a valid query with no explanations.
        queryArguments(entailment);
        if (limit <= 0) {
            return Collections.emptySet();
        }
        return generateBounded(entailment, limit).getExplanations();
    }

    KMExplanationRun generateBounded(OWLAxiom entailment, int limit) {
        if (limit <= 0) {
            throw new IllegalArgumentException("justification limit must be positive");
        }
        NativeReport report = invoke(entailment, limit);
        Set<Explanation<OWLAxiom>> explanations = materialize(entailment, report);
        return new KMExplanationRun(
                "entailed".equals(report.status),
                explanations,
                report.enumerationComplete,
                report.justificationLimitReached,
                report.classificationChecks,
                report.classificationCheckLimit,
                report.justificationLimit);
    }

    /** Exact entailment surface advertised to OWLAPI and Protégé callers. */
    public static boolean supportsEntailment(OWLAxiom entailment) {
        try {
            queryArguments(entailment);
            return true;
        } catch (UnsupportedEntailmentException error) {
            return false;
        }
    }

    private NativeReport invoke(OWLAxiom entailment, int limit) {
        if (progressMonitor.isCancelled()) {
            throw new ExplanationGeneratorInterruptedException();
        }

        List<String> query = queryArguments(entailment);
        Path source = null;
        Path stdout = null;
        Path stderr = null;
        Process process = null;
        try {
            source = Files.createTempFile("kmarust-explain-", ".ofn");
            stdout = Files.createTempFile("kmarust-explain-", ".json");
            stderr = Files.createTempFile("kmarust-explain-", ".log");
            FlattenedOntology.save(ontology, source);

            List<String> command = new ArrayList<>();
            command.add(configuration.getExecutable());
            command.add("explain");
            command.add("--route");
            command.add("auto");
            command.add("--max-axioms");
            command.add(Integer.toString(configuration.getMaxAxioms()));
            command.add("--max-checks");
            command.add(Integer.toString(configuration.getMaxChecks()));
            command.add("--max-source-bytes");
            command.add(Long.toString(configuration.getMaxSourceBytes()));
            command.add("--max-justifications");
            command.add(Integer.toString(limit));
            command.add(source.toString());
            command.addAll(query);

            ProcessBuilder processBuilder = new ProcessBuilder(command);
            processBuilder.redirectOutput(stdout.toFile());
            processBuilder.redirectError(stderr.toFile());
            process = processBuilder.start();
            waitFor(process);

            String errorText = new String(
                    Files.readAllBytes(stderr), StandardCharsets.UTF_8);
            if (process.exitValue() != 0) {
                throw new ExplanationException(
                        "KM explanation declined or failed (exit "
                                + process.exitValue() + "): " + errorText);
            }
            String json = new String(Files.readAllBytes(stdout), StandardCharsets.UTF_8);
            NativeReport report;
            try {
                report = gson.fromJson(json, NativeReport.class);
            } catch (JsonParseException error) {
                throw new ExplanationException(
                        "KM returned invalid explanation JSON: " + json, error);
            }
            validateReport(report, limit);
            return report;
        } catch (ExplanationException error) {
            throw error;
        } catch (InterruptedException error) {
            if (process != null) {
                terminateAndWait(process);
            }
            Thread.currentThread().interrupt();
            throw new ExplanationGeneratorInterruptedException();
        } catch (Exception error) {
            throw new ExplanationException("Could not generate a KM explanation", error);
        } finally {
            delete(source);
            delete(stdout);
            delete(stderr);
        }
    }

    private void waitFor(Process process) throws InterruptedException {
        long deadline = System.nanoTime()
                + TimeUnit.SECONDS.toNanos(configuration.getTimeoutSeconds());
        while (!process.waitFor(100, TimeUnit.MILLISECONDS)) {
            if (progressMonitor.isCancelled()) {
                terminateAndWait(process);
                throw new ExplanationGeneratorInterruptedException();
            }
            if (System.nanoTime() >= deadline) {
                terminateAndWait(process);
                throw new ExplanationException(
                        "KM explanation timed out after "
                                + configuration.getTimeoutSeconds() + " seconds");
            }
        }
    }

    /** Stop and reap a native request before its temporary files are removed. */
    private static void terminateAndWait(Process process) {
        process.destroy();
        try {
            if (!process.waitFor(500, TimeUnit.MILLISECONDS)) {
                process.destroyForcibly();
                process.waitFor(5, TimeUnit.SECONDS);
            }
        } catch (InterruptedException error) {
            process.destroyForcibly();
            Thread.currentThread().interrupt();
        }
    }

    private static List<String> queryArguments(OWLAxiom entailment) {
        if (!(entailment instanceof OWLSubClassOfAxiom)) {
            throw new UnsupportedEntailmentException(
                    "KM explanations support only named SubClassOf entailments");
        }
        OWLSubClassOfAxiom subClassOf = (OWLSubClassOfAxiom) entailment;
        OWLClassExpression subExpression = subClassOf.getSubClass();
        OWLClassExpression superExpression = subClassOf.getSuperClass();
        if (subExpression.isAnonymous() || superExpression.isAnonymous()) {
            throw new UnsupportedEntailmentException(
                    "KM explanations require named subclass and superclass expressions");
        }
        OWLClass subClass = subExpression.asOWLClass();
        OWLClass superClass = superExpression.asOWLClass();
        if (subClass.isOWLThing() && superClass.isOWLNothing()) {
            return Collections.singletonList("inconsistent");
        }
        if (superClass.isOWLNothing()) {
            List<String> args = new ArrayList<>();
            args.add("unsatisfiable");
            args.add(subClass.getIRI().toString());
            return args;
        }
        List<String> args = new ArrayList<>();
        args.add("subclass");
        args.add(subClass.getIRI().toString());
        args.add(superClass.getIRI().toString());
        return args;
    }

    private static void validateReport(NativeReport report, int requestedLimit) {
        if (report == null || report.schemaVersion != SCHEMA_VERSION) {
            throw new ExplanationException(
                    "Unsupported KM explanation schema: "
                            + (report == null ? "null" : report.schemaVersion));
        }
        if (!"auto".equals(report.requestedRoute)) {
            throw new ExplanationException(
                    "KM explanation did not use the automatic production gate");
        }
        if (report.checkLimitReached) {
            throw new ExplanationException(
                    "KM exhausted its classification-check bound before completing "
                            + "the requested explanation search");
        }
        if (!"entailed".equals(report.status) && !"not-entailed".equals(report.status)) {
            throw new ExplanationException("Unknown KM explanation status: " + report.status);
        }
        if ("entailed".equals(report.status) && report.justifications == null) {
            throw new ExplanationException("KM returned no justification array");
        }
        if (report.justifications != null && report.justifications.size() > requestedLimit) {
            throw new ExplanationException(
                    "KM returned more justifications than the requested bound");
        }
        if (report.justificationLimit != requestedLimit) {
            throw new ExplanationException(
                    "KM did not apply the requested justification bound");
        }
        if (report.classificationCheckLimit <= 0
                || report.classificationChecks < 0
                || report.classificationChecks > report.classificationCheckLimit) {
            throw new ExplanationException(
                    "KM returned an invalid classification-check count");
        }
        if (report.enumerationComplete
                && (report.checkLimitReached || report.justificationLimitReached)) {
            throw new ExplanationException(
                    "KM reported a complete enumeration and a limiting cause");
        }
        if (!report.enumerationComplete
                && !report.checkLimitReached
                && !report.justificationLimitReached) {
            throw new ExplanationException(
                    "KM reported an incomplete enumeration without a limiting cause");
        }
        if ("not-entailed".equals(report.status)
                && (!report.enumerationComplete
                    || (report.justifications != null && !report.justifications.isEmpty()))) {
            throw new ExplanationException(
                    "KM returned an invalid not-entailed explanation report");
        }
        if ("entailed".equals(report.status)
                && (report.justifications == null || report.justifications.isEmpty())) {
            throw new ExplanationException(
                    "KM returned an entailed verdict without a verified support");
        }
        if ("entailed".equals(report.status) && !report.oracleSubsetMinimal) {
            throw new ExplanationException(
                    "KM did not certify every returned support as subset-minimal");
        }
    }

    private Set<Explanation<OWLAxiom>> materialize(
            OWLAxiom entailment, NativeReport report) {
        if ("not-entailed".equals(report.status)) {
            return Collections.emptySet();
        }
        Set<Explanation<OWLAxiom>> explanations = new LinkedHashSet<>();
        Set<OWLAxiom> sourceAxioms = ontology.getAxioms(Imports.INCLUDED);
        List<String> prefixes = report.prefixDeclarations == null
                ? Collections.emptyList() : report.prefixDeclarations;
        for (NativeJustification nativeJustification : report.justifications) {
            if (!nativeJustification.verified || !nativeJustification.subsetMinimal) {
                throw new ExplanationException(
                        "KM attempted to expose an unverified or non-minimal support");
            }
            Set<OWLAxiom> axioms = new LinkedHashSet<>();
            if (nativeJustification.axioms != null) {
                for (NativeAxiom nativeAxiom : nativeJustification.axioms) {
                    if (nativeAxiom == null) {
                        throw new ExplanationException(
                                "KM returned a null source axiom");
                    }
                    OWLAxiom axiom = parseSourceAxiom(
                            prefixes, nativeAxiom.functionalSyntax);
                    if (!sourceAxioms.contains(axiom)) {
                        throw new ExplanationException(
                                "KM returned an axiom outside the flattened source ontology: "
                                        + nativeAxiom.functionalSyntax);
                    }
                    axioms.add(axiom);
                }
            }
            if (nativeJustification.axiomCount != axioms.size()) {
                throw new ExplanationException(
                        "KM source-axiom count did not match the parsed OWL axioms");
            }
            Explanation<OWLAxiom> explanation = new Explanation<>(entailment, axioms);
            explanations.add(explanation);
            progressMonitor.foundExplanation(this, explanation, explanations);
            if (progressMonitor.isCancelled()) {
                throw new ExplanationGeneratorInterruptedException();
            }
        }
        if (explanations.size() != report.justifications.size()) {
            throw new ExplanationException(
                    "KM returned duplicate source justifications");
        }
        return explanations;
    }

    private static OWLAxiom parseSourceAxiom(List<String> prefixes, String functionalSyntax) {
        if (functionalSyntax == null || functionalSyntax.isEmpty()) {
            throw new ExplanationException("KM returned an empty source axiom");
        }
        Path document = null;
        try {
            document = Files.createTempFile("kmarust-source-axiom-", ".ofn");
            StringBuilder source = new StringBuilder();
            for (String prefix : prefixes) {
                source.append(prefix).append('\n');
            }
            source.append("Ontology(\n  ")
                    .append(functionalSyntax)
                    .append("\n)\n");
            Files.write(document, source.toString().getBytes(StandardCharsets.UTF_8));
            OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
            OWLOntology parsed = manager.loadOntologyFromOntologyDocument(document.toFile());
            Set<OWLAxiom> axioms = parsed.getAxioms();
            if (axioms.size() != 1) {
                throw new ExplanationException(
                        "Expected one OWL source axiom, parsed " + axioms.size()
                                + " from " + functionalSyntax);
            }
            return axioms.iterator().next();
        } catch (ExplanationException error) {
            throw error;
        } catch (Exception error) {
            throw new ExplanationException(
                    "Could not parse KM source axiom: " + functionalSyntax, error);
        } finally {
            delete(document);
        }
    }

    private static void delete(Path path) {
        if (path != null) {
            try {
                Files.deleteIfExists(path);
            } catch (Exception ignored) {
                // Temporary-file cleanup must not mask the explanation result.
            }
        }
    }

    private static final class NativeReport {
        int schemaVersion;
        String status;
        String requestedRoute;
        boolean enumerationComplete;
        boolean oracleSubsetMinimal;
        boolean checkLimitReached;
        boolean justificationLimitReached;
        int classificationChecks;
        int classificationCheckLimit;
        int justificationLimit;
        List<String> prefixDeclarations;
        List<NativeJustification> justifications;
    }

    private static final class NativeJustification {
        boolean verified;
        boolean subsetMinimal;
        int axiomCount;
        List<NativeAxiom> axioms;
    }

    private static final class NativeAxiom {
        String functionalSyntax;
    }
}
