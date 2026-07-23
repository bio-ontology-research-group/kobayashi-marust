package org.bioontology.kobayashimarust.protege;

import org.protege.editor.owl.ui.explanation.ExplanationResult;
import org.semanticweb.owl.explanation.api.Explanation;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLOntology;

import javax.swing.BorderFactory;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSpinner;
import javax.swing.JTextArea;
import javax.swing.SpinnerNumberModel;
import javax.swing.SwingUtilities;
import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/** Result panel opened by Protégé's standard Explain action. */
final class KMNativeExplanationResult extends ExplanationResult {

    private static final long serialVersionUID = 1L;

    private final JSpinner limit = new JSpinner(new SpinnerNumberModel(1, 1, 100, 1));
    private final JButton generate = new JButton("Generate");
    private final JButton cancel = new JButton("Cancel");
    private final JTextArea status = textArea(3);
    private final JTextArea output = textArea(18);
    private final KMExplanationController controller;

    KMNativeExplanationResult(
            OWLOntology ontology,
            OWLAxiom entailment,
            KMExplanationConfiguration configuration) {
        setLayout(new BorderLayout(8, 8));
        setBorder(BorderFactory.createEmptyBorder(8, 8, 8, 8));
        setPreferredSize(new Dimension(780, 480));

        JPanel header = new JPanel();
        header.setLayout(new BoxLayout(header, BoxLayout.Y_AXIS));
        JTextArea query = textArea(2);
        query.setText(entailment.toString());
        query.setBorder(BorderFactory.createTitledBorder("Selected entailment"));
        header.add(query);

        JPanel controls = new JPanel(new FlowLayout(FlowLayout.LEFT));
        controls.add(new JLabel("Maximum justifications:"));
        controls.add(limit);
        controls.add(generate);
        controls.add(cancel);
        header.add(controls);
        add(header, BorderLayout.NORTH);

        status.setBorder(BorderFactory.createTitledBorder("Verification status"));
        output.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
        JScrollPane outputScroll = new JScrollPane(output);
        outputScroll.setBorder(BorderFactory.createTitledBorder("Source OWL axioms"));
        JPanel body = new JPanel(new BorderLayout(6, 6));
        body.add(status, BorderLayout.NORTH);
        body.add(outputScroll, BorderLayout.CENTER);
        add(body, BorderLayout.CENTER);

        controller = KMExplanationController.forOntology(
                ontology,
                entailment,
                configuration,
                SwingUtilities::invokeLater);
        generate.addActionListener(event -> generate());
        cancel.addActionListener(event -> controller.cancel());
        setBusy(false);
        status.setText(
                "Ready. Every displayed support will be revalidated and subset-minimal.");
        SwingUtilities.invokeLater(this::generate);
    }

    private static JTextArea textArea(int rows) {
        JTextArea area = new JTextArea(rows, 72);
        area.setEditable(false);
        area.setLineWrap(true);
        area.setWrapStyleWord(true);
        return area;
    }

    private void generate() {
        int requested = ((Number) limit.getValue()).intValue();
        output.setText("");
        status.setText("Running KM through the automatic production gate...");
        setBusy(true);
        boolean started = controller.start(requested, new KMExplanationController.Listener() {
            @Override
            public void completed(KMExplanationRun result) {
                setBusy(false);
                status.setText(result.statusText());
                output.setText(render(result));
                output.setCaretPosition(0);
            }

            @Override
            public void failed(RuntimeException error) {
                setBusy(false);
                String message = error.getMessage();
                status.setText("Explanation failed closed: "
                        + (message == null ? error.getClass().getSimpleName() : message));
            }

            @Override
            public void cancelled() {
                setBusy(false);
                status.setText("Cancelled. No partial explanation was displayed.");
            }
        });
        if (!started) {
            status.setText("An explanation request is already running.");
        }
    }

    private static String render(KMExplanationRun run) {
        if (!run.isEntailed()) {
            return "";
        }
        StringBuilder rendered = new StringBuilder();
        int index = 0;
        for (Explanation<OWLAxiom> explanation : run.getExplanations()) {
            index++;
            rendered.append("Justification ").append(index).append("\n");
            List<String> axioms = new ArrayList<>();
            for (OWLAxiom axiom : explanation.getAxioms()) {
                axioms.add(axiom.toString());
            }
            Collections.sort(axioms);
            for (String axiom : axioms) {
                rendered.append("  ").append(axiom).append("\n");
            }
            rendered.append('\n');
        }
        return rendered.toString();
    }

    private void setBusy(boolean busy) {
        generate.setEnabled(!busy);
        limit.setEnabled(!busy);
        cancel.setEnabled(busy);
    }

    @Override
    public void dispose() {
        controller.close();
    }
}
