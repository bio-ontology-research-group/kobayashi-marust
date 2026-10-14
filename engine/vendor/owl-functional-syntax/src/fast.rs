//! Hand-written structural recognizer for `ofn-iri-cached.pest`.
//!
//! It is a one-sided acceptance test. `recognize` returns the document's
//! distinct full-IRI and language-tag spellings only when the PEG grammar's
//! own parse would succeed on the document structure: every choice point is
//! decided by the token that the first succeeding PEG alternative requires,
//! greedy repetitions stop exactly where the PEG repetition stops, and the
//! `DataSomeValuesFrom`/`DataAllValuesFrom` lookahead workaround is mirrored.
//! Any construct it does not reproduce exactly, any parse failure, and every
//! description-graph extension return `None`; the caller then runs the pest
//! grammar, which therefore still decides every rejection and its message.
//! The returned IRI and tag spellings must still pass the original atomic
//! `FullIRI` and `BCP47_LanguageTag` rules.

use std::collections::HashSet;
use std::hash::{BuildHasherDefault, Hasher};

/// Multiplicative word hasher for the per-document spelling sets.
#[derive(Default)]
pub struct WordHasher(u64);

impl Hasher for WordHasher {
    fn write(&mut self, bytes: &[u8]) {
        let mut chunks = bytes.chunks_exact(8);
        for chunk in &mut chunks {
            let word = u64::from_le_bytes(chunk.try_into().unwrap());
            self.0 = (self.0.rotate_left(5) ^ word).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
        }
        for &byte in chunks.remainder() {
            self.0 = (self.0.rotate_left(5) ^ byte as u64).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
        }
    }
    fn finish(&self) -> u64 {
        self.0
    }
}

pub type SpellingSet<'a> = HashSet<&'a str, BuildHasherDefault<WordHasher>>;

pub struct Recognized<'a> {
    /// Distinct full-IRI spellings that `ascii_http_iri` does not accept.
    pub full_iris: SpellingSet<'a>,
    pub language_tags: SpellingSet<'a>,
}

struct P<'a> {
    text: &'a str,
    s: &'a [u8],
    i: usize,
    iris: SpellingSet<'a>,
    tags: SpellingSet<'a>,
}

type R = Option<()>;

/// Recognize a complete `OntologyDocument`; `None` means "not decided here".
pub fn recognize(text: &str) -> Option<Recognized<'_>> {
    let mut p = P { text, s: text.as_bytes(), i: 0, iris: SpellingSet::default(), tags: SpellingSet::default() };
    p.document()?;
    Some(Recognized { full_iris: p.iris, language_tags: p.tags })
}

fn pn_chars_base(c: char) -> bool {
    c.is_ascii_alphabetic()
        || ('\u{00C0}'..='\u{00D6}').contains(&c)
        || ('\u{00D8}'..='\u{00F6}').contains(&c)
        || ('\u{00F8}'..='\u{02FF}').contains(&c)
        || ('\u{0370}'..='\u{037D}').contains(&c)
        || ('\u{037F}'..='\u{1FFF}').contains(&c)
        || ('\u{200C}'..='\u{200D}').contains(&c)
        || ('\u{2070}'..='\u{218F}').contains(&c)
        || ('\u{2C00}'..='\u{2FEF}').contains(&c)
        || ('\u{3001}'..='\u{D7FF}').contains(&c)
        || ('\u{F900}'..='\u{FDCF}').contains(&c)
        || ('\u{FDF0}'..='\u{FFFD}').contains(&c)
        || ('\u{10000}'..='\u{EFFFF}').contains(&c)
}

fn pn_chars_u(c: char) -> bool {
    pn_chars_base(c) || c == '_'
}

fn pn_chars(c: char) -> bool {
    pn_chars_u(c)
        || c == '-'
        || c.is_ascii_digit()
        || c == '\u{00B7}'
        || ('\u{0300}'..='\u{036F}').contains(&c)
        || ('\u{203F}'..='\u{2040}').contains(&c)
}

impl<'a> P<'a> {
    fn ch(&self, at: usize) -> Option<char> {
        let b = *self.s.get(at)?;
        if b < 0x80 {
            Some(b as char)
        } else {
            self.text[at..].chars().next()
        }
    }

    /// Implicit `(WHITESPACE | COMMENT)*` between non-atomic sequence items.
    fn skip(&mut self) {
        let s = self.s;
        let mut i = self.i;
        while i < s.len() {
            match s[i] {
                b' ' | b'\t' | b'\n' | b'\r' => i += 1,
                b'#' => {
                    i += 1;
                    while i < s.len() && s[i] != b'\n' && s[i] != b'\r' {
                        i += 1;
                    }
                }
                _ => break,
            }
        }
        self.i = i;
    }

    fn peek(&mut self) -> Option<u8> {
        self.skip();
        self.s.get(self.i).copied()
    }

    fn expect(&mut self, byte: u8) -> R {
        if self.peek()? == byte {
            self.i += 1;
            Some(())
        } else {
            None
        }
    }

    /// Maximal ASCII-letter run at the current position (after skipping).
    fn word(&mut self) -> &'a str {
        self.skip();
        let start = self.i;
        let mut i = start;
        while i < self.s.len() && self.s[i].is_ascii_alphabetic() {
            i += 1;
        }
        &self.text[start..i]
    }

    /// Keyword followed by `(`; restores the position when it is absent.
    fn open(&mut self, keyword: &str) -> bool {
        let save = self.i;
        if self.word() == keyword {
            self.i += keyword.len();
            if self.peek() == Some(b'(') {
                self.i += 1;
                return true;
            }
        }
        self.i = save;
        false
    }

    /// Peek the keyword introducing the next construct without consuming it.
    fn peek_word(&mut self) -> &'a str {
        let save = self.i;
        let w = self.word();
        self.i = save;
        w
    }

    // ---- atomic tokens ------------------------------------------------

    /// `FullIRI = @{ "<" ~ (!">" ~ ANY)* ~ ">" }` at the current position.
    fn full_iri(&mut self) -> R {
        let start = self.i;
        if self.s.get(start) != Some(&b'<') {
            return None;
        }
        let rel = self.s[start + 1..].iter().position(|&b| b == b'>')?;
        let end = start + 1 + rel + 1;
        // A spelling the specialised ASCII HTTP check accepts needs no grammar
        // check; only the others are collected (`validate_handwritten` checks
        // each collected spelling with the same predicate first).
        let spelling = &self.text[start..end];
        if !crate::ascii_http_iri(spelling) {
            self.iris.insert(spelling);
        }
        self.i = end;
        Some(())
    }

    /// `SPARQL_PnPrefix` body after its first character, then position.
    fn pn_tail(&self, mut i: usize) -> usize {
        loop {
            match self.ch(i) {
                Some('.') => match self.ch(i + 1) {
                    Some(c) if pn_chars(c) => i += 1 + c.len_utf8(),
                    _ => return i,
                },
                Some(c) if pn_chars(c) => i += c.len_utf8(),
                _ => return i,
            }
        }
    }

    /// `SPARQL_PnameNs = @{ SPARQL_PnPrefix? ~ ":" }`; returns the end.
    fn pname_ns_end(&self, at: usize) -> Option<usize> {
        let mut i = at;
        if let Some(c) = self.ch(i) {
            if pn_chars_base(c) {
                i = self.pn_tail(i + c.len_utf8());
            }
        }
        (self.s.get(i) == Some(&b':')).then_some(i + 1)
    }

    /// `SPARQL_PnLocal`; returns the end.
    fn pn_local_end(&self, at: usize) -> Option<usize> {
        let c = self.ch(at)?;
        if !(pn_chars_u(c) || c.is_ascii_digit()) {
            return None;
        }
        Some(self.pn_tail(at + c.len_utf8()))
    }

    /// `IRI = { FullIRI | AbbreviatedIRI }` (no skip; caller skipped).
    fn try_iri(&mut self) -> bool {
        if self.s.get(self.i) == Some(&b'<') {
            return self.full_iri().is_some();
        }
        if let Some(ns) = self.pname_ns_end(self.i) {
            if let Some(end) = self.pn_local_end(ns) {
                self.i = end;
                return true;
            }
        }
        false
    }

    fn iri(&mut self) -> R {
        self.skip();
        self.try_iri().then_some(())
    }

    /// `NodeID = SPARQL_BlankNodeLabel = @{ "_:" ~ SPARQL_PnLocal }`.
    fn try_node_id(&mut self) -> bool {
        if self.s.get(self.i) == Some(&b'_') && self.s.get(self.i + 1) == Some(&b':') {
            if let Some(end) = self.pn_local_end(self.i + 2) {
                self.i = end;
                return true;
            }
        }
        false
    }

    fn non_negative_integer(&mut self) -> R {
        self.skip();
        let start = self.i;
        while self.i < self.s.len() && self.s[self.i].is_ascii_digit() {
            self.i += 1;
        }
        (self.i > start).then_some(())
    }

    /// `QuotedString = @{ "\"" ~ (!"\"" ~ ("\\\\" | "\\\"" | ANY))* ~ "\"" }`.
    fn quoted_string(&mut self) -> R {
        let s = self.s;
        let mut i = self.i;
        if s.get(i) != Some(&b'"') {
            return None;
        }
        i += 1;
        loop {
            match s.get(i)? {
                b'"' => {
                    self.i = i + 1;
                    return Some(());
                }
                b'\\' if matches!(s.get(i + 1), Some(b'\\') | Some(b'"')) => i += 2,
                _ => i += 1,
            }
        }
    }

    /// `Literal = { TypedLiteral | StringLiteralWithLanguage | StringLiteralNoLanguage }`.
    fn literal(&mut self) -> R {
        self.skip();
        self.quoted_string()?;
        match self.peek() {
            Some(b'^') => {
                self.i += 1;
                self.expect(b'^')?;
                self.iri()
            }
            Some(b'@') => {
                // LanguageTag = @{ "@" ~ BCP47_LanguageTag }. BCP 47 only
                // inspects [A-Za-z0-9-]; the caller requires the PEG rule to
                // consume this whole run, so the document match is identical.
                let start = self.i + 1;
                let mut end = start;
                while end < self.s.len()
                    && (self.s[end].is_ascii_alphanumeric() || self.s[end] == b'-')
                {
                    end += 1;
                }
                if end == start {
                    return None;
                }
                self.tags.insert(&self.text[start..end]);
                self.i = end;
                Some(())
            }
            _ => Some(()),
        }
    }

    // ---- entities and expressions --------------------------------------

    fn individual(&mut self) -> R {
        self.skip();
        (self.try_iri() || self.try_node_id()).then_some(())
    }

    fn object_property_expression(&mut self) -> R {
        self.skip();
        if self.try_iri() {
            return Some(());
        }
        if self.open("ObjectInverseOf") {
            self.iri()?;
            return self.expect(b')');
        }
        None
    }

    fn at_close(&mut self) -> bool {
        self.peek() == Some(b')')
    }

    fn data_range(&mut self) -> R {
        self.skip();
        if self.try_iri() {
            return Some(());
        }
        match self.peek_word() {
            "DataIntersectionOf" | "DataUnionOf" => {
                let w = self.peek_word();
                if !self.open(w) {
                    return None;
                }
                self.data_range()?;
                self.data_range()?;
                while !self.at_close() {
                    self.data_range()?;
                }
                self.expect(b')')
            }
            "DataComplementOf" => {
                if !self.open("DataComplementOf") {
                    return None;
                }
                self.data_range()?;
                self.expect(b')')
            }
            "DataOneOf" => {
                if !self.open("DataOneOf") {
                    return None;
                }
                self.literal()?;
                while !self.at_close() {
                    self.literal()?;
                }
                self.expect(b')')
            }
            "DatatypeRestriction" => {
                if !self.open("DatatypeRestriction") {
                    return None;
                }
                self.iri()?;
                self.iri()?;
                self.literal()?;
                while !self.at_close() {
                    self.iri()?;
                    self.literal()?;
                }
                self.expect(b')')
            }
            _ => None,
        }
    }

    /// `(DataProperty ~ !RBRACKET)+ ~ DataRange ~ RBRACKET` after the keyword.
    fn data_quantified_body(&mut self) -> R {
        let mut iterations = 0;
        loop {
            let save = self.i;
            self.skip();
            if !self.try_iri() {
                self.i = save;
                break;
            }
            if self.at_close() {
                // The lookahead fails: PEG undoes this iteration entirely.
                self.i = save;
                break;
            }
            iterations += 1;
        }
        if iterations == 0 {
            return None;
        }
        self.data_range()?;
        self.expect(b')')
    }

    fn class_expression(&mut self) -> R {
        self.skip();
        if self.try_iri() {
            return Some(());
        }
        let w = self.peek_word();
        if !self.open(w) {
            return None;
        }
        match w {
            "ObjectIntersectionOf" | "ObjectUnionOf" => {
                self.class_expression()?;
                self.class_expression()?;
                while !self.at_close() {
                    self.class_expression()?;
                }
            }
            "ObjectComplementOf" => self.class_expression()?,
            "ObjectOneOf" => {
                self.individual()?;
                while !self.at_close() {
                    self.individual()?;
                }
            }
            "ObjectSomeValuesFrom" | "ObjectAllValuesFrom" => {
                self.object_property_expression()?;
                self.class_expression()?;
            }
            "ObjectHasValue" => {
                self.object_property_expression()?;
                self.individual()?;
            }
            "ObjectHasSelf" => self.object_property_expression()?,
            "ObjectMinCardinality" | "ObjectMaxCardinality" | "ObjectExactCardinality" => {
                self.non_negative_integer()?;
                self.object_property_expression()?;
                if !self.at_close() {
                    self.class_expression()?;
                }
            }
            "DataSomeValuesFrom" | "DataAllValuesFrom" => return self.data_quantified_body(),
            "DataHasValue" => {
                self.iri()?;
                self.literal()?;
            }
            "DataMinCardinality" | "DataMaxCardinality" | "DataExactCardinality" => {
                self.non_negative_integer()?;
                self.iri()?;
                if !self.at_close() {
                    self.data_range()?;
                }
            }
            _ => return None,
        }
        self.expect(b')')
    }

    // ---- annotations ----------------------------------------------------

    fn annotations(&mut self) -> R {
        while self.open("Annotation") {
            self.annotations()?;
            self.iri()?;
            self.annotation_value()?;
            self.expect(b')')?;
        }
        Some(())
    }

    /// `AnnotationValue = { AnonymousIndividual | IRI | Literal }`.
    fn annotation_value(&mut self) -> R {
        self.skip();
        if self.try_node_id() || self.try_iri() {
            return Some(());
        }
        self.literal()
    }

    // ---- rules ------------------------------------------------------------

    fn variable(&mut self) -> R {
        if !self.open("Variable") {
            return None;
        }
        self.iri()?;
        self.expect(b')')
    }

    /// `IArg = { Individual | Variable }`.
    fn i_arg(&mut self) -> R {
        self.skip();
        if self.try_iri() || self.try_node_id() {
            return Some(());
        }
        self.variable()
    }

    /// `DArg = { Literal | Variable }`.
    fn d_arg(&mut self) -> R {
        if self.peek()? == b'"' {
            return self.literal();
        }
        self.variable()
    }

    fn atoms(&mut self) -> R {
        while !self.at_close() {
            let w = self.peek_word();
            if !self.open(w) {
                return None;
            }
            match w {
                "ClassAtom" => {
                    self.class_expression()?;
                    self.i_arg()?;
                }
                "DataRangeAtom" => {
                    self.data_range()?;
                    self.d_arg()?;
                }
                "ObjectPropertyAtom" => {
                    self.object_property_expression()?;
                    self.i_arg()?;
                    self.i_arg()?;
                }
                "DataPropertyAtom" => {
                    self.iri()?;
                    self.i_arg()?;
                    self.d_arg()?;
                }
                "BuiltInAtom" => {
                    self.iri()?;
                    self.d_arg()?;
                    while !self.at_close() {
                        self.d_arg()?;
                    }
                }
                "SameIndividualAtom" | "DifferentIndividualsAtom" => {
                    self.i_arg()?;
                    self.i_arg()?;
                }
                _ => return None,
            }
            self.expect(b')')?;
        }
        Some(())
    }

    // ---- axioms -------------------------------------------------------------

    fn axiom(&mut self) -> R {
        let w = self.peek_word();
        if !self.open(w) {
            return None;
        }
        match w {
            "Declaration" => {
                self.annotations()?;
                let entity = self.peek_word();
                if !matches!(entity, "Class" | "Datatype" | "ObjectProperty" | "DataProperty"
                    | "AnnotationProperty" | "NamedIndividual") || !self.open(entity) {
                    return None;
                }
                self.iri()?;
                self.expect(b')')?;
            }
            "SubClassOf" => {
                self.annotations()?;
                self.class_expression()?;
                self.class_expression()?;
            }
            "EquivalentClasses" | "DisjointClasses" => {
                self.annotations()?;
                self.class_expression()?;
                self.class_expression()?;
                while !self.at_close() {
                    self.class_expression()?;
                }
            }
            "DisjointUnion" => {
                self.annotations()?;
                self.iri()?;
                self.class_expression()?;
                self.class_expression()?;
                while !self.at_close() {
                    self.class_expression()?;
                }
            }
            "SubObjectPropertyOf" => {
                self.annotations()?;
                self.skip();
                let save = self.i;
                if self.object_property_expression().is_none() {
                    self.i = save;
                    if !self.open("ObjectPropertyChain") {
                        return None;
                    }
                    self.object_property_expression()?;
                    self.object_property_expression()?;
                    while !self.at_close() {
                        self.object_property_expression()?;
                    }
                    self.expect(b')')?;
                }
                self.object_property_expression()?;
            }
            "EquivalentObjectProperties" | "DisjointObjectProperties" => {
                self.annotations()?;
                self.object_property_expression()?;
                self.object_property_expression()?;
                while !self.at_close() {
                    self.object_property_expression()?;
                }
            }
            "InverseObjectProperties" => {
                self.annotations()?;
                self.iri()?;
                self.iri()?;
            }
            "ObjectPropertyDomain" | "ObjectPropertyRange" => {
                self.annotations()?;
                self.object_property_expression()?;
                self.class_expression()?;
            }
            "FunctionalObjectProperty" | "InverseFunctionalObjectProperty"
            | "ReflexiveObjectProperty" | "IrreflexiveObjectProperty"
            | "SymmetricObjectProperty" | "AsymmetricObjectProperty"
            | "TransitiveObjectProperty" => {
                self.annotations()?;
                self.object_property_expression()?;
            }
            "SubDataPropertyOf" => {
                self.annotations()?;
                self.iri()?;
                self.iri()?;
            }
            "EquivalentDataProperties" | "DisjointDataProperties" => {
                self.annotations()?;
                self.iri()?;
                self.iri()?;
                while !self.at_close() {
                    self.iri()?;
                }
            }
            "DataPropertyDomain" => {
                self.annotations()?;
                self.iri()?;
                self.class_expression()?;
            }
            "DataPropertyRange" | "DatatypeDefinition" => {
                self.annotations()?;
                self.iri()?;
                self.data_range()?;
            }
            "FunctionalDataProperty" => {
                self.annotations()?;
                self.iri()?;
            }
            "HasKey" => {
                self.annotations()?;
                self.class_expression()?;
                self.expect(b'(')?;
                while !self.at_close() {
                    self.object_property_expression()?;
                }
                self.expect(b')')?;
                self.expect(b'(')?;
                while !self.at_close() {
                    self.iri()?;
                }
                self.expect(b')')?;
            }
            "SameIndividual" | "DifferentIndividuals" => {
                self.annotations()?;
                self.individual()?;
                self.individual()?;
                while !self.at_close() {
                    self.individual()?;
                }
            }
            "ClassAssertion" => {
                self.annotations()?;
                self.class_expression()?;
                self.individual()?;
            }
            "ObjectPropertyAssertion" | "NegativeObjectPropertyAssertion" => {
                self.annotations()?;
                self.object_property_expression()?;
                self.individual()?;
                self.individual()?;
            }
            "DataPropertyAssertion" | "NegativeDataPropertyAssertion" => {
                self.annotations()?;
                self.iri()?;
                self.individual()?;
                self.literal()?;
            }
            "AnnotationAssertion" => {
                self.annotations()?;
                self.iri()?;
                // AnnotationSubject = { IRI | AnonymousIndividual }
                self.skip();
                if !(self.try_iri() || self.try_node_id()) {
                    return None;
                }
                self.annotation_value()?;
            }
            "SubAnnotationPropertyOf" | "AnnotationPropertyDomain" | "AnnotationPropertyRange" => {
                self.annotations()?;
                self.iri()?;
                self.iri()?;
            }
            "DLSafeRule" => {
                self.annotations()?;
                if !self.open("Body") {
                    return None;
                }
                self.atoms()?;
                self.expect(b')')?;
                if !self.open("Head") {
                    return None;
                }
                self.atoms()?;
                self.expect(b')')?;
            }
            // Description-graph extensions and unknown heads: not decided here.
            _ => return None,
        }
        self.expect(b')')
    }

    fn document(&mut self) -> R {
        // PrefixDeclaration = { "Prefix" "(" PrefixName "=" FullIRI ")" }
        while self.open("Prefix") {
            self.skip();
            self.i = self.pname_ns_end(self.i)?;
            self.expect(b'=')?;
            self.skip();
            self.full_iri()?;
            self.expect(b')')?;
        }
        if !self.open("Ontology") {
            return None;
        }
        // (OntologyIRI ~ VersionIRI?)?
        self.skip();
        if self.try_iri() {
            self.skip();
            self.try_iri();
        }
        while self.open("Import") {
            self.iri()?;
            self.expect(b')')?;
        }
        self.annotations()?;
        while !self.at_close() {
            self.axiom()?;
        }
        self.expect(b')')?;
        self.skip();
        (self.i == self.s.len()).then_some(())
    }
}
