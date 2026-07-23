package org.bioontology.kobayashimarust.protege;

import org.junit.Test;
import org.semanticweb.owl.explanation.api.Explanation;
import org.semanticweb.owl.explanation.api.ExplanationGeneratorInterruptedException;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLDataFactory;

import java.util.Collections;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/** Headless tests for the asynchronous Protégé result-panel controller. */
public class KMExplanationControllerTest {

    @Test
    public void completesOffThreadAndPreservesBoundAndVerificationStatus()
            throws Exception {
        OWLDataFactory dataFactory = OWLManager.getOWLDataFactory();
        OWLAxiom source = dataFactory.getOWLSubClassOfAxiom(
                dataFactory.getOWLClass(IRI.create("urn:km:A")),
                dataFactory.getOWLClass(IRI.create("urn:km:B")));
        OWLAxiom entailment = dataFactory.getOWLSubClassOfAxiom(
                dataFactory.getOWLClass(IRI.create("urn:km:A")),
                dataFactory.getOWLClass(IRI.create("urn:km:C")));
        Explanation<OWLAxiom> explanation = new Explanation<>(
                entailment, Collections.singleton(source));
        KMExplanationRun expected = new KMExplanationRun(
                true,
                Collections.singleton(explanation),
                false,
                true,
                7,
                64,
                1);
        CountDownLatch delivered = new CountDownLatch(1);
        AtomicReference<KMExplanationRun> completed = new AtomicReference<>();
        AtomicReference<RuntimeException> failed = new AtomicReference<>();
        AtomicBoolean cancelled = new AtomicBoolean(false);

        try (KMExplanationController controller = new KMExplanationController(
                (limit, monitor) -> expected,
                Runnable::run)) {
            assertTrue(controller.start(1, new KMExplanationController.Listener() {
                @Override
                public void completed(KMExplanationRun result) {
                    completed.set(result);
                    delivered.countDown();
                }

                @Override
                public void failed(RuntimeException error) {
                    failed.set(error);
                    delivered.countDown();
                }

                @Override
                public void cancelled() {
                    cancelled.set(true);
                    delivered.countDown();
                }
            }));
            assertTrue(delivered.await(5, TimeUnit.SECONDS));
        }

        assertEquals(expected, completed.get());
        assertFalse(cancelled.get());
        assertNull(failed.get());
        String status = completed.get().statusText();
        assertTrue(status.contains("verified, subset-minimal"));
        assertTrue(status.contains("requested limit of 1 was reached"));
        assertTrue(status.contains("more may exist"));
        assertTrue(status.contains("7/64"));

        KMExplanationRun complete = new KMExplanationRun(
                true, Collections.singleton(explanation), true, false, 4, 64, 2);
        assertTrue(complete.statusText().contains("Enumeration complete"));
    }

    @Test
    public void cancellationStopsWorkAndDeliversOnlyCancelled() throws Exception {
        CountDownLatch entered = new CountDownLatch(1);
        CountDownLatch delivered = new CountDownLatch(1);
        AtomicBoolean completed = new AtomicBoolean(false);
        AtomicReference<RuntimeException> failed = new AtomicReference<>();
        AtomicBoolean cancelled = new AtomicBoolean(false);

        try (KMExplanationController controller = new KMExplanationController(
                (limit, monitor) -> {
                    entered.countDown();
                    while (!monitor.isCancelled()) {
                        try {
                            Thread.sleep(10);
                        } catch (InterruptedException error) {
                            Thread.currentThread().interrupt();
                        }
                    }
                    throw new ExplanationGeneratorInterruptedException();
                },
                Runnable::run)) {
            assertTrue(controller.start(1, new KMExplanationController.Listener() {
                @Override
                public void completed(KMExplanationRun result) {
                    completed.set(true);
                    delivered.countDown();
                }

                @Override
                public void failed(RuntimeException error) {
                    failed.set(error);
                    delivered.countDown();
                }

                @Override
                public void cancelled() {
                    cancelled.set(true);
                    delivered.countDown();
                }
            }));
            assertTrue(entered.await(5, TimeUnit.SECONDS));
            assertTrue(controller.cancel());
            assertTrue(delivered.await(5, TimeUnit.SECONDS));
        }

        assertTrue(cancelled.get());
        assertFalse(completed.get());
        assertNull(failed.get());
    }
}
