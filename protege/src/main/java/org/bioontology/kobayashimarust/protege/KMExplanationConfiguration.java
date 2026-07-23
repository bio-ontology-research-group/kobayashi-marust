package org.bioontology.kobayashimarust.protege;

/** Immutable process and safety bounds for the native explanation adapter. */
public final class KMExplanationConfiguration {

    public static final int DEFAULT_MAX_AXIOMS = 256;
    public static final int DEFAULT_MAX_CHECKS = 4096;
    public static final long DEFAULT_MAX_SOURCE_BYTES = 8L * 1024L * 1024L;
    public static final int DEFAULT_ALL_JUSTIFICATIONS_CAP = 8;
    public static final long DEFAULT_TIMEOUT_SECONDS = 600L;

    private final String executable;
    private final long timeoutSeconds;
    private final int maxAxioms;
    private final int maxChecks;
    private final long maxSourceBytes;
    private final int allJustificationsCap;

    public KMExplanationConfiguration(
            String executable,
            long timeoutSeconds,
            int maxAxioms,
            int maxChecks,
            long maxSourceBytes,
            int allJustificationsCap) {
        this.executable = requireText(executable, "executable");
        this.timeoutSeconds = requirePositive(timeoutSeconds, "timeoutSeconds");
        this.maxAxioms = requirePositive(maxAxioms, "maxAxioms");
        this.maxChecks = requirePositive(maxChecks, "maxChecks");
        this.maxSourceBytes = requirePositive(maxSourceBytes, "maxSourceBytes");
        this.allJustificationsCap = requirePositive(
                allJustificationsCap, "allJustificationsCap");
    }

    public static KMExplanationConfiguration fromSystemProperties() {
        return new KMExplanationConfiguration(
                setting("km.bin", "KM_BIN", "km"),
                longSetting(
                        "km.timeout.seconds",
                        "KM_TIMEOUT_SECONDS",
                        DEFAULT_TIMEOUT_SECONDS),
                intSetting(
                        "km.explain.max.axioms",
                        "KM_EXPLAIN_MAX_AXIOMS",
                        DEFAULT_MAX_AXIOMS),
                intSetting(
                        "km.explain.max.checks",
                        "KM_EXPLAIN_MAX_CHECKS",
                        DEFAULT_MAX_CHECKS),
                longSetting(
                        "km.explain.max.source.bytes",
                        "KM_EXPLAIN_MAX_SOURCE_BYTES",
                        DEFAULT_MAX_SOURCE_BYTES),
                intSetting(
                        "km.explain.all.justifications.cap",
                        "KM_EXPLAIN_ALL_JUSTIFICATIONS_CAP",
                        DEFAULT_ALL_JUSTIFICATIONS_CAP));
    }

    public String getExecutable() {
        return executable;
    }

    public long getTimeoutSeconds() {
        return timeoutSeconds;
    }

    public int getMaxAxioms() {
        return maxAxioms;
    }

    public int getMaxChecks() {
        return maxChecks;
    }

    public long getMaxSourceBytes() {
        return maxSourceBytes;
    }

    public int getAllJustificationsCap() {
        return allJustificationsCap;
    }

    private static String setting(String property, String environment, String fallback) {
        String value = System.getProperty(property);
        if (value == null || value.isEmpty()) {
            value = System.getenv(environment);
        }
        return value == null || value.isEmpty() ? fallback : value;
    }

    private static int intSetting(String property, String environment, int fallback) {
        String value = setting(property, environment, Integer.toString(fallback));
        try {
            return requirePositive(Integer.parseInt(value), property);
        } catch (NumberFormatException error) {
            throw new IllegalArgumentException(property + " must be an integer", error);
        }
    }

    private static long longSetting(String property, String environment, long fallback) {
        String value = setting(property, environment, Long.toString(fallback));
        try {
            return requirePositive(Long.parseLong(value), property);
        } catch (NumberFormatException error) {
            throw new IllegalArgumentException(property + " must be an integer", error);
        }
    }

    private static String requireText(String value, String name) {
        if (value == null || value.isEmpty()) {
            throw new IllegalArgumentException(name + " must not be empty");
        }
        return value;
    }

    private static int requirePositive(int value, String name) {
        if (value <= 0) {
            throw new IllegalArgumentException(name + " must be greater than zero");
        }
        return value;
    }

    private static long requirePositive(long value, String name) {
        if (value <= 0) {
            throw new IllegalArgumentException(name + " must be greater than zero");
        }
        return value;
    }
}
