//! One-sided NEW outer-grammar check for reuse of individually validated spans.
//! This never grants admission alone: header and every retained axiom span
//! still need exact validated provenance. Unsupported forms use full validation.
use crate::source_locality::Scan;

fn trivia(bytes: &[u8], mut at: usize) -> usize {
    while at < bytes.len() {
        match bytes[at] {
            b' ' | b'\t' | b'\n' | b'\r' => at += 1,
            b'#' => {
                at += 1;
                while at < bytes.len() && !matches!(bytes[at], b'\r' | b'\n') { at += 1; }
            }
            _ => break,
        }
    }
    at
}

/// The vendor grammar's trivia, ontology Annotation* phase and final ')'.
/// Unicode remains legal inside unchanged validated spans and comments.
/// Returning false MUST fall back before any non-byte-identical answer reuse.
pub fn outer_grammar(text: &str, scan: &Scan) -> bool {
    if scan.open_end > text.len() || !text.is_char_boundary(scan.open_end) { return false; }
    let bytes = text.as_bytes();
    let mut at = scan.open_end;
    let mut axioms = false;
    for st in &scan.statements {
        if st.start < at || st.start >= st.end || st.end > bytes.len()
            || trivia(&bytes[at..st.start], 0) != st.start-at { return false; }
        let Some(span) = text.get(st.start..st.end) else { return false; };
        let head_end = span.bytes().take_while(u8::is_ascii_alphabetic).count();
        if head_end == 0 || span.as_bytes().get(trivia(span.as_bytes(), head_end)) != Some(&b'(') { return false; }
        let head = &span[..head_end];
        if head == "Import" { return false; } // A validated self-contained donor has none.
        if head == "Annotation" {
            if axioms { return false; }
        } else { axioms = true; }
        at = st.end;
    }
    at = trivia(bytes, at);
    if bytes.get(at) != Some(&b')') { return false; }
    trivia(bytes, at+1) == bytes.len()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source_locality::scan;
    #[test]
    fn exact_vendor_spaces_comments_and_phase() {
        for gap in [" ", "\t\n\r", "# comment\n", "# comment\r\n", "# comment\r"] {
            let text=format!("Ontology(Declaration(Class(<urn:A>)){gap}SubClassOf(<urn:A> <urn:A>)) # tail\r\n");
            // The locality scanner treats CR-only comments differently; it may
            // decline or omit a statement. The outer check must not grant reuse.
            let s=scan(&text);
            if gap=="# comment\r" { if let Ok(s)=s { assert!(!outer_grammar(&text,&s)); } }
            else { assert!(outer_grammar(&text,&s.unwrap()),"{gap:?}"); }
        }
        let good="Ontology(Annotation(rdfs:label \"x\") Declaration(Class(<urn:A>)))";
        assert!(outer_grammar(good,&scan(good).unwrap()));
        let bad="Ontology(Declaration(Class(<urn:A>)) Annotation(rdfs:label \"x\"))";
        assert!(!outer_grammar(bad,&scan(bad).unwrap()));
    }
    #[test]
    fn unicode_inside_validated_spans_keeps_outer_reuse() {
        let text="Ontology(Annotation(rdfs:label \"Καλημέρα\") Declaration(Class(<urn:é>)))";
        assert!(outer_grammar(text,&scan(text).unwrap()));
    }

    #[test]
    fn unicode_byte_class_split_is_a_fallible_scan() {
        for gap in ["\u{0085}","\u{00a0}"] {
            let text=format!("Ontology({gap}Declaration(Class(<urn:A>)))");
            assert!(scan(&text).is_err());
        }
    }

    #[test]
    fn unsupported_or_hidden_gap_tokens_decline() {
        for gap in ["\x0b", "\x0c", "# hidden\rUnknown()\n"] {
            let text=format!("Ontology(Declaration(Class(<urn:A>)){gap}Declaration(Class(<urn:B>)))");
            assert!(!outer_grammar(&text,&scan(&text).unwrap()));
        }
        for gap in ["\u{0085}","\u{00a0}","\u{2003}"] {
            let text=format!("Ontology(Declaration(Class(<urn:A>)){gap}Declaration(Class(<urn:B>)))");
            // Checked token boundaries return Err rather than panicking;
            // a successfully scanned unsupported gap must decline reuse.
            if let Ok(scanned)=scan(&text) { assert!(!outer_grammar(&text,&scanned)); }
        }
    }
}
