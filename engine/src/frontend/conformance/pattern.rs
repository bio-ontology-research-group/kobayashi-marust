//! Validate the XSD regex dialect without compiling arbitrarily large counts.
use super::facets::XSD;

fn quantity_order(lower: &str, upper: &str) -> bool {
    let lower = lower.trim_start_matches('0');
    let upper = upper.trim_start_matches('0');
    lower.len() < upper.len() || (lower.len() == upper.len() && lower <= upper)
}

/// Quantities affect matching, not the surrounding regex grammar. After
/// checking their exact decimal bounds, use {1} solely for syntax validation.
/// Escapes (including Unicode properties) and character classes stay intact.
fn syntax_pattern(pattern: &str) -> Result<String, String> {
    let mut chars = pattern.chars().peekable();
    let mut output = String::with_capacity(pattern.len());
    let mut class_depth = 0usize;
    while let Some(c) = chars.next() {
        if c == '\\' {
            output.push(c);
            if let Some(escaped) = chars.next() {
                output.push(escaped);
                if matches!(escaped, 'p' | 'P') && chars.peek() == Some(&'{') {
                    for part in chars.by_ref() {
                        output.push(part);
                        if part == '}' { break; }
                    }
                }
            }
        } else if c == '[' {
            class_depth += 1;
            output.push(c);
        } else if c == ']' {
            class_depth = class_depth.saturating_sub(1);
            output.push(c);
        } else if c == '{' && class_depth == 0 {
            let mut quantity = String::new();
            let mut closed = false;
            for part in chars.by_ref() {
                if part == '}' { closed = true; break; }
                quantity.push(part);
            }
            let parts: Vec<_> = quantity.split(',').collect();
            let digits = |s: &str| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit());
            let valid = match parts.as_slice() {
                [count] => digits(count),
                [lower, upper] => digits(lower) && (upper.is_empty() || (digits(upper) && quantity_order(lower, upper))),
                _ => false,
            };
            if !closed || !valid {
                return Err("invalid OWL 2 DL input: xsd:pattern contains a malformed repetition quantity or an upper bound smaller than its lower bound".into());
            }
            output.push_str("{1}");
        } else {
            output.push(c);
        }
    }
    Ok(output)
}

pub(super) fn check(quoted: &str, datatype: &str) -> Result<(), String> {
    // Literal lexical validity and membership in the string value space have
    // already been checked. Only quote and backslash escapes exist in OFN.
    let body = &quoted[1..quoted.len()-1];
    let mut chars = body.chars();
    let mut value = String::with_capacity(body.len());
    while let Some(c) = chars.next() {
        value.push(if c == '\\' { chars.next().unwrap_or(c) } else { c });
    }
    if datatype == "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral" {
        value.pop(); // Empty language suffix: this value is an ordinary string.
    } else if let Some(kind) = datatype.strip_prefix(XSD) {
        if kind == "normalizedString" {
            value = value.replace(['\t', '\r', '\n'], " ");
        } else if matches!(kind, "token" | "language" | "Name" | "NCName" | "NMTOKEN") {
            value = value.split([' ', '\t', '\r', '\n']).filter(|s| !s.is_empty()).collect::<Vec<_>>().join(" ");
        }
    }
    let syntax = syntax_pattern(&value)?;
    oxixml_regex::Regex::xsd(&syntax).map(|_| ()).map_err(|error| {
        let detail = error.to_string();
        if detail.contains("nesting") && detail.contains("limit") {
            format!("OWL 2 DL validation resource limit: xsd:pattern nesting exceeds the regex parser's capacity; no conformance verdict was produced: {detail}")
        } else {
            format!("invalid OWL 2 DL input: malformed xsd:pattern: {detail}")
        }
    })
}

#[cfg(test)]
mod tests {
    use super::super::check_source;
    fn document(pattern: &str) -> String {
        let quoted = pattern.replace('\\', "\\\\").replace('"', "\\\"");
        format!("Ontology(DataPropertyRange(<urn:p> DatatypeRestriction(xsd:string xsd:pattern \"{quoted}\")))")
    }
    #[test]
    fn xml_regex_syntax_preserves_large_quantities_and_xml_specific_constructs() {
        for pattern in ["", "a{0}", "a{0002,003}", "a{2,}", "[a-z-[aeiou]]+",
            "\\i\\c*", "\\p{Lu}+", "\\p{IsBasicLatin}", "a|", "^literal$",
            "a{999999999999999999999999999999999999}",
            "a{999999999999999999999999999999999998,999999999999999999999999999999999999}",
            "\\{2\\}", "[{}]"] {
            check_source(&document(pattern)).unwrap_or_else(|e| panic!("{pattern}: {e}"));
        }
    }
    #[test]
    fn xml_regex_syntax_rejects_invalid_counts_classes_and_xpath_extensions() {
        for pattern in ["[", "(", "(?=a)", "a*?", "a{3,2}",
            "a{999999999999999999999999999999999999,999999999999999999999999999999999998}",
            "a{,2}", "a{1,2,3}", "a{1", "{1}a", "a*{1}", "[z-a]", "\\1", "\\p{NotACategory}"] {
            let error = check_source(&document(pattern)).unwrap_err();
            assert!(error.contains("xsd:pattern"), "{pattern}: {error}");
        }
    }
    #[test]
    fn decimal_bound_comparison_matches_machine_oracle_in_its_range() {
        for lower in 0..100 {
            for upper in 0..100 {
                assert_eq!(super::quantity_order(&format!("{lower:04}"), &upper.to_string()), lower <= upper);
            }
        }
    }
}
