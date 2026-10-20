package org.bioontology.kobayashimarust.protege;

import java.io.StringWriter;
import java.util.*;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.functional.renderer.FunctionalSyntaxObjectRenderer;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.util.DefaultPrefixManager;
import org.semanticweb.owlapi.vocab.OWLXMLVocabulary;

/** Private prototype: exact initial rendering, bounded retained axiom splicing. */
class RetainedFunctionalSyntax {
    static final class CaptureIneligible extends RuntimeException {
        CaptureIneligible(String reason) { super(reason); }
    }
    private State committed;
    private long generation;

    static final class Prepared {
        final String source;
        final boolean reused;
        final boolean usedSuppliedDelta;
        // Non-null only on normal-render fallback. Fast preparation does not
        // allocate a detached ontology; the caller can update its own committed
        // snapshot after successful native publication using the exact delta.
        final OWLOntology fallbackSnapshot;
        final Set<OWLAxiom> added;
        final Set<OWLAxiom> removed;
        final Set<OWLClass> classes;
        final Set<OWLOntology> imports;
        private final RetainedFunctionalSyntax owner;
        private final long generation;
        private final State state;
        // Non-null when the state shares the committed axiom set and must patch
        // it in place at commit; nothing is mutated before the commit.
        private final Set<OWLAxiom> patchAdded, patchRemoved;

        private Prepared(RetainedFunctionalSyntax owner, State state, String source, boolean reused,
                         OWLOntology snapshot, Set<OWLAxiom> added,
                         Set<OWLAxiom> removed, boolean usedSuppliedDelta, Set<OWLOntology> imports,
                         Set<OWLAxiom> patchAdded, Set<OWLAxiom> patchRemoved) {
            this.owner = owner;
            this.generation = owner.generation;
            this.state = state;
            this.patchAdded = patchAdded;
            this.patchRemoved = patchRemoved;
            this.source = source;
            this.reused = reused;
            this.usedSuppliedDelta = usedSuppliedDelta;
            this.imports = Collections.unmodifiableSet(imports);
            this.fallbackSnapshot = snapshot;
            this.added = Collections.unmodifiableSet(added);
            this.removed = Collections.unmodifiableSet(removed);
            Set<OWLClass> classes = new HashSet<>();
            for (OWLEntity entity : state.signature)
                if (entity.isOWLClass()) classes.add(entity.asOWLClass());
            this.classes = Collections.unmodifiableSet(classes);
        }
    }

    private static final class Span {
        final OWLAxiom axiom;
        final int start, end;
        Span(OWLAxiom axiom, int start, int end) {
            this.axiom = axiom; this.start = start; this.end = end;
        }
    }

    private static final class Origin {
        final String source;
        final List<Span> spans;
        // Axioms with at least one captured span (only membership is queried).
        final Set<OWLAxiom> captured;
        final Set<OWLAxiom> axioms;
        final Set<OWLEntity> signature;
        final int closing;
        Origin(String source, List<Span> spans, Set<OWLAxiom> axioms, Set<OWLEntity> signature) {
            if (!source.endsWith(")")) throw new CaptureIneligible("ontology close missing");
            this.source = source;
            this.closing = source.length() - 1;
            this.spans = Collections.unmodifiableList(new ArrayList<>(spans));
            this.captured = new HashSet<>();
            int previous = 0;
            for (Span span : spans) {
                if (span.start < previous || span.end <= span.start || span.end > closing)
                    throw new CaptureIneligible("invalid overlapping capture");
                previous = span.end;
                captured.add(span.axiom);
            }
            this.axioms = axioms;
            // The private preparation owns this set; State also exposes only
            // an immutable view. Keep the original typed domain across edits.
            this.signature = Collections.unmodifiableSet(signature);
        }
    }

    private static final class State {
        final OWLOntologyID id;
        final Set<OWLEntity> signature;
        final Set<OWLAxiom> axioms;
        // Backing set of the unmodifiable view above. Successive committed states
        // share it and patch it in place in commit(); never the Origin's set.
        private final Set<OWLAxiom> owned;
        final Origin origin;
        // Only currently active non-origin axioms; historical additions vanish.
        final Map<OWLAxiom, String> additions;
        // The rendered text is not retained here: only Origin.source is kept.
        State(OWLOntologyID id, Set<OWLEntity> signature, Set<OWLAxiom> axioms,
              Origin origin, Map<OWLAxiom, String> additions) {
            this.id = id;
            this.signature = Collections.unmodifiableSet(signature);
            this.owned = axioms;
            this.axioms = Collections.unmodifiableSet(axioms);
            this.origin = origin;
            this.additions = Collections.unmodifiableMap(additions);
        }
    }

    Prepared prepare(OWLOntology root) throws Exception {
        return prepare(root, null, null);
    }

    // The caller certifies that these are the complete effective base-class
    // deltas relative to the last successfully committed exact source. Raw
    // changes alone are not such a certificate (imports can duplicate axioms).
    Prepared prepare(OWLOntology root, Set<OWLAxiom> suppliedAdded,
                     Set<OWLAxiom> suppliedRemoved) throws Exception {
        FlattenedOntology.validateImports(root);
        Set<OWLOntology> imports = importsView(root);
        State old = committed;
        // Initialization always needs the detached snapshot. Build its signature
        // once and let the renderer reuse OWLAPI's cache, instead of sorting the
        // same (potentially very large) entity domain on both ontology objects.
        OWLOntology initialSnapshot = old == null ? FlattenedOntology.snapshot(root) : null;
        Set<OWLEntity> signature = initialSnapshot == null
                ? new HashSet<>(root.getSignature(Imports.INCLUDED))
                : initialSignature(root, initialSnapshot);
        boolean sameSignature = old != null && old.signature.equals(signature);
        boolean withinOriginSignature = old != null && old.origin != null
                && old.origin.signature.containsAll(signature);
        boolean supplied = old != null && old.id.equals(root.getOntologyID())
                && (sameSignature || withinOriginSignature) && suppliedAdded != null && suppliedRemoved != null
                && admissibleDelta(root, old, suppliedAdded, suppliedRemoved);
        // A certified delta is applied to the committed set only at commit();
        // until then membership in the next revision is an overlay on `old`.
        final Set<OWLAxiom> nextAxioms = supplied ? null : new HashSet<>(root.getAxioms(Imports.INCLUDED));
        final java.util.function.Predicate<OWLAxiom> inNext = supplied
                ? a -> (old.axioms.contains(a) && !suppliedRemoved.contains(a)) || suppliedAdded.contains(a)
                : nextAxioms::contains;
        if (old != null && old.origin != null && old.id.equals(root.getOntologyID()) && withinOriginSignature) {
            Set<OWLAxiom> added = supplied ? new HashSet<>(suppliedAdded) : difference(nextAxioms, old.axioms);
            Set<OWLAxiom> removed = supplied ? new HashSet<>(suppliedRemoved) : difference(old.axioms, nextAxioms);
            boolean eligible = true;
            for (OWLAxiom a : removed)
                eligible &= capturedOrigin(old.origin, a)
                        || (!old.origin.axioms.contains(a)
                            && old.additions.containsKey(a) && namedSubclass(a));
            for (OWLAxiom a : added)
                eligible &= old.origin.axioms.contains(a)
                        ? capturedOrigin(old.origin, a) : namedSubclass(a);
            if (eligible) {
                Map<OWLAxiom, String> active = new LinkedHashMap<>();
                for (Map.Entry<OWLAxiom, String> entry : old.additions.entrySet())
                    if (inNext.test(entry.getKey())) active.put(entry.getKey(), entry.getValue());
                List<OWLAxiom> order = new ArrayList<>(added);
                Collections.sort(order);
                for (OWLAxiom a : order) {
                    if (old.origin.axioms.contains(a)) continue;
                    String text = old.additions.get(a);
                    if (text == null) text = renderAxiom(root, a);
                    active.put(a, text);
                }
                StringBuilder out = new StringBuilder(old.origin.source.length());
                int cursor = 0;
                for (Span span : old.origin.spans) {
                    // Explicit declarations still force normal rendering via
                    // capturedOrigin. Synthetic declarations follow the exact
                    // current typed signature, not just their IRI spelling.
                    boolean omit = old.origin.axioms.contains(span.axiom)
                            ? !inNext.test(span.axiom)
                            : span.axiom instanceof OWLDeclarationAxiom
                                && !signature.contains(((OWLDeclarationAxiom)span.axiom).getEntity());
                    if (omit) {
                        out.append(old.origin.source, cursor, span.start);
                        cursor = span.end;
                    }
                }
                out.append(old.origin.source, cursor, old.origin.closing);
                for (String text : active.values()) out.append('\n').append(text).append('\n');
                out.append(old.origin.source, old.origin.closing, old.origin.source.length());
                State state = new State(root.getOntologyID(), signature,
                        supplied ? old.owned : nextAxioms, old.origin, active);
                return new Prepared(this, state, out.toString(), true, null, added, removed,
                        supplied, imports, supplied ? added : null, supplied ? removed : null);
            }
        }
        // Fallback owns a fresh set; the committed one is untouched until commit.
        final Set<OWLAxiom> axioms;
        if (supplied) {
            axioms = new HashSet<>(old.axioms);
            axioms.removeAll(suppliedRemoved);
            axioms.addAll(suppliedAdded);
        } else {
            axioms = nextAxioms;
        }
        OWLOntology snapshot = initialSnapshot == null
                ? FlattenedOntology.snapshot(root) : initialSnapshot;
        Origin origin = null;
        String source;
        try {
            Capture capture = createCapture(snapshot);
            snapshot.accept(capture);
            if (capture.pending != null) throw new CaptureIneligible("unclosed axiom capture");
            source = capture.output.toString();
            // The origin keeps its own copy: committed states patch their set in place.
            origin = new Origin(source, capture.spans, new HashSet<>(axioms), signature);
        } catch (CaptureIneligible unsupportedCapture) {
            // Capture is an optimization. The ordinary renderer remains the
            // authority for any shape our offset bookkeeping cannot represent.
            source = FlattenedOntology.functionalSyntaxOfSnapshot(snapshot);
        }
        State state = new State(root.getOntologyID(), signature, axioms, origin,
                Collections.emptyMap());
        return new Prepared(this, state, source, false, snapshot,
                old == null ? new HashSet<>(axioms) : difference(axioms, old.axioms),
                old == null ? new HashSet<>() : difference(old.axioms, axioms), false, imports,
                null, null);
    }

    static Set<OWLEntity> initialSignature(OWLOntology root, OWLOntology snapshot) {
        Set<OWLEntity> signature = new HashSet<>(snapshot.getSignature());
        // FlattenedOntology copies the imports-closure axioms, but deliberately
        // omits ontology annotations. Their typed entities still belong to the
        // live signature used by the retained serializer's eligibility checks.
        for (OWLOntology member : root.getImportsClosure())
            for (OWLAnnotation annotation : member.getAnnotations())
                signature.addAll(annotation.getSignature());
        return signature;
    }

    // OWLAPI's concurrent ontology facade is used by change events, while its
    // imports closure exposes delegate objects. Bind both identities so unsafe
    // events cannot be mistaken for changes in an unrelated ontology.
    static Set<OWLOntology> importsView(OWLOntology root) {
        Set<OWLOntology> view = Collections.newSetFromMap(new IdentityHashMap<>());
        view.add(root);
        for (OWLOntology member : root.getImportsClosure()) {
            view.add(member);
            OWLOntology wrapper = root.getOWLOntologyManager().getOntology(member.getOntologyID());
            if (wrapper != null) view.add(wrapper);
        }
        return view;
    }

    private static boolean admissibleDelta(OWLOntology root, State old,
                                           Set<OWLAxiom> added, Set<OWLAxiom> removed) {
        for (OWLAxiom axiom : added) {
            if (!safeDeltaAxiom(axiom) || old.axioms.contains(axiom) || removed.contains(axiom)
                    || !root.containsAxiom(axiom, Imports.INCLUDED,
                        org.semanticweb.owlapi.model.parameters.AxiomAnnotations.CONSIDER_AXIOM_ANNOTATIONS))
                return false;
        }
        for (OWLAxiom axiom : removed) {
            if (!safeDeltaAxiom(axiom) || !old.axioms.contains(axiom)
                    || root.containsAxiom(axiom, Imports.INCLUDED,
                        org.semanticweb.owlapi.model.parameters.AxiomAnnotations.CONSIDER_AXIOM_ANNOTATIONS))
                return false;
        }
        return true;
    }

    static boolean safeDeltaAxiom(OWLAxiom axiom) {
        return !axiom.isAnnotated() && (axiom.isLogicalAxiom() || axiom instanceof OWLDeclarationAxiom);
    }

    void commit(Prepared prepared) {
        if (prepared.owner != this || prepared.generation != generation)
            throw new IllegalStateException("stale or foreign serializer transaction");
        // Patch in place only now that the native transaction has succeeded; the
        // new state shares the set of the one it replaces.
        if (prepared.patchAdded != null) {
            prepared.state.owned.removeAll(prepared.patchRemoved);
            prepared.state.owned.addAll(prepared.patchAdded);
        }
        committed = prepared.state;
        generation++;
    }

    private static Set<OWLAxiom> difference(Set<OWLAxiom> a, Set<OWLAxiom> b) {
        Set<OWLAxiom> result = new HashSet<>(a); result.removeAll(b); return result;
    }

    private static boolean namedSubclass(OWLAxiom a) {
        if (!(a instanceof OWLSubClassOfAxiom) || a.isAnnotated()) return false;
        OWLSubClassOfAxiom sc = (OWLSubClassOfAxiom)a;
        return !sc.getSubClass().isAnonymous() && !sc.getSuperClass().isAnonymous();
    }

    private static boolean namedDisjoint(OWLAxiom a) {
        if (!(a instanceof OWLDisjointClassesAxiom) || a.isAnnotated()) return false;
        Set<OWLClassExpression> operands = ((OWLDisjointClassesAxiom)a).getClassExpressions();
        if (operands.size() < 2) return false;
        for (OWLClassExpression c : operands) if (c.isAnonymous()) return false;
        return true;
    }

    // Only exact emitted origin text is deleted/restored. Declarations are
    // excluded because ordinary rendering may synthesize their replacement.
    // Novel axioms still require the independent named-subclass renderer path.
    private static boolean capturedOrigin(Origin origin, OWLAxiom a) {
        return !(a instanceof OWLDeclarationAxiom)
                && origin.axioms.contains(a) && origin.captured.contains(a);
    }

    private static void fullIri(FunctionalSyntaxObjectRenderer renderer) {
        DefaultPrefixManager prefixes = new DefaultPrefixManager();
        prefixes.clear();
        renderer.setPrefixManager(prefixes);
    }

    private static String renderAxiom(OWLOntology ontology, OWLAxiom axiom) {
        StringWriter output = new StringWriter();
        FunctionalSyntaxObjectRenderer renderer = new FunctionalSyntaxObjectRenderer(
                ontology, new FunctionalSyntaxDocumentFormat(), output);
        fullIri(renderer);
        axiom.accept(renderer);
        return output.toString();
    }

    Capture createCapture(OWLOntology ontology) { return new Capture(ontology); }

    static class Capture extends FunctionalSyntaxObjectRenderer {
        final StringWriter output;
        final List<Span> spans = new ArrayList<>();
        OWLAxiom pending;
        int start;
        Capture(OWLOntology ontology) { this(ontology, new StringWriter()); }
        private Capture(OWLOntology ontology, StringWriter output) {
            super(ontology, new FunctionalSyntaxDocumentFormat(), output);
            this.output = output;
            fullIri(this);
        }
        @Override protected void writeAxiomStart(OWLXMLVocabulary vocabulary, OWLAxiom axiom) {
            if (pending != null) throw new CaptureIneligible("nested axiom capture");
            pending = axiom;
            start = output.getBuffer().length();
            super.writeAxiomStart(vocabulary, axiom);
        }
        @Override protected void writeAxiomEnd() {
            super.writeAxiomEnd();
            if (pending == null) throw new CaptureIneligible("missing axiom capture");
            spans.add(new Span(pending, start, output.getBuffer().length()));
            pending = null;
        }
    }
}
