package org.bioontology.kobayashimarust.protege;

import org.junit.Test;
import org.protege.editor.owl.ui.explanation.ExplanationResult;
import org.protege.editor.owl.ui.explanation.ExplanationService;

import java.io.InputStream;
import java.nio.charset.StandardCharsets;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

/** Guards the service metadata consumed by Protégé and Java clients. */
public class PluginRegistrationTest {

    @Test
    public void registersTheNativeExplanationServiceAndFactory() throws Exception {
        String pluginXml = resource("/plugin.xml");
        assertTrue(pluginXml.contains("org.protege.editor.owl.explanation"));
        assertTrue(pluginXml.contains(KMNativeExplanationService.class.getName()));
        assertTrue(pluginXml.contains("KobayashiMarustReasonerFactory"));

        String factory = resource(
                "/META-INF/services/"
                        + "org.semanticweb.owl.explanation.api.ExplanationGeneratorFactory");
        assertTrue(factory.contains(KMExplanationGeneratorFactory.class.getName()));
        assertNotNull(Class.forName(KMNativeExplanationResult.class.getName()));
        assertNotNull(Class.forName(KMExplanationController.class.getName()));
        assertTrue(ExplanationService.class.isAssignableFrom(
                KMNativeExplanationService.class));
        assertTrue(ExplanationResult.class.isAssignableFrom(
                KMNativeExplanationResult.class));
        assertNotNull(KMNativeExplanationService.class.getDeclaredConstructor());
    }

    private static String resource(String name) throws Exception {
        try (InputStream input = PluginRegistrationTest.class.getResourceAsStream(name)) {
            assertNotNull("missing bundle resource " + name, input);
            return new String(input.readAllBytes(), StandardCharsets.UTF_8);
        }
    }
}
