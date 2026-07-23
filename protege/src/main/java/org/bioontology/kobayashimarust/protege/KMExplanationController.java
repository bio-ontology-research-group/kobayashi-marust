package org.bioontology.kobayashimarust.protege;

import org.semanticweb.owl.explanation.api.ExplanationGeneratorInterruptedException;
import org.semanticweb.owl.explanation.api.ExplanationProgressMonitor;
import org.semanticweb.owl.explanation.api.NullExplanationProgressMonitor;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLOntology;

import java.util.concurrent.Executor;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * One-request-at-a-time asynchronous controller for the Protégé explanation
 * result panel. Native work never runs on Swing's event-dispatch thread.
 */
final class KMExplanationController implements AutoCloseable {

    interface Listener {
        void completed(KMExplanationRun result);

        void failed(RuntimeException error);

        void cancelled();
    }

    @FunctionalInterface
    interface GenerationTask {
        KMExplanationRun generate(
                int limit, ExplanationProgressMonitor<OWLAxiom> progressMonitor);
    }

    private final GenerationTask task;
    private final Executor callbackExecutor;
    private final ExecutorService worker;
    private Request current;
    private boolean closed;

    static KMExplanationController forOntology(
            OWLOntology ontology,
            OWLAxiom entailment,
            KMExplanationConfiguration configuration,
            Executor callbackExecutor) {
        return new KMExplanationController(
                (limit, monitor) -> new KMExplanationGenerator(
                        ontology, monitor, configuration)
                        .generateBounded(entailment, limit),
                callbackExecutor);
    }

    KMExplanationController(GenerationTask task, Executor callbackExecutor) {
        if (task == null || callbackExecutor == null) {
            throw new NullPointerException("task and callbackExecutor are required");
        }
        this.task = task;
        this.callbackExecutor = callbackExecutor;
        this.worker = Executors.newSingleThreadExecutor(runnable -> {
            Thread thread = new Thread(runnable, "km-explanation");
            thread.setDaemon(true);
            thread.setPriority(Thread.MIN_PRIORITY);
            return thread;
        });
    }

    synchronized boolean start(int limit, Listener listener) {
        if (closed) {
            throw new IllegalStateException("explanation controller is closed");
        }
        if (limit <= 0) {
            throw new IllegalArgumentException("justification limit must be positive");
        }
        if (listener == null) {
            throw new NullPointerException("listener");
        }
        if (current != null) {
            return false;
        }
        Request request = new Request(listener);
        current = request;
        request.future = worker.submit(() -> run(request, limit));
        return true;
    }

    synchronized boolean isRunning() {
        return current != null;
    }

    boolean cancel() {
        Request request;
        synchronized (this) {
            request = current;
            if (request == null) {
                return false;
            }
            current = null;
            request.cancelled.set(true);
        }
        Future<?> future = request.future;
        if (future != null) {
            future.cancel(true);
        }
        dispatchCancelled(request);
        return true;
    }

    private void run(Request request, int limit) {
        ExplanationProgressMonitor<OWLAxiom> monitor =
                new NullExplanationProgressMonitor<OWLAxiom>() {
                    @Override
                    public boolean isCancelled() {
                        return request.cancelled.get()
                                || Thread.currentThread().isInterrupted();
                    }
                };
        try {
            KMExplanationRun result = task.generate(limit, monitor);
            if (request.cancelled.get()) {
                dispatchCancelled(request);
            } else {
                dispatch(request, () -> request.listener.completed(result));
            }
        } catch (ExplanationGeneratorInterruptedException error) {
            dispatchCancelled(request);
        } catch (RuntimeException error) {
            if (request.cancelled.get()) {
                dispatchCancelled(request);
            } else {
                dispatch(request, () -> request.listener.failed(error));
            }
        } finally {
            // Future.cancel(true) interrupts this reusable worker thread.
            Thread.interrupted();
            synchronized (this) {
                if (current == request) {
                    current = null;
                }
            }
        }
    }

    private void dispatchCancelled(Request request) {
        dispatch(request, request.listener::cancelled);
    }

    private void dispatch(Request request, Runnable callback) {
        if (request.callbackDelivered.compareAndSet(false, true)) {
            callbackExecutor.execute(callback);
        }
    }

    @Override
    public void close() {
        synchronized (this) {
            closed = true;
        }
        cancel();
        worker.shutdownNow();
    }

    private static final class Request {
        final Listener listener;
        final AtomicBoolean cancelled = new AtomicBoolean(false);
        final AtomicBoolean callbackDelivered = new AtomicBoolean(false);
        volatile Future<?> future;

        Request(Listener listener) {
            this.listener = listener;
        }
    }
}
