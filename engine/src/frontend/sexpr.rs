//! Tokeniser + s-expression parser for OWL functional syntax.
//!
//! Port of `frontend.tokenize` (the `_TOK` regex) and the `class P`
//! recursive-descent parser in `engine/py/frontend.py`, reworked to be
//! zero-copy: tokens are `&str` slices into the source text (no per-token heap
//! allocation) and are produced lazily by an iterator, so the token stream is
//! never materialised. A parsed node is either an atom slice or a
//! `(head, [args])` pair borrowing from the source.

/// A parsed s-expression node: a bare token, or a head with arguments. Borrows
/// the source text (token slices), so it costs no string allocations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Node<'a> {
    Atom(&'a str),
    List(&'a str, Vec<Node<'a>>),
}

impl<'a> Node<'a> {
    pub fn as_atom(&self) -> Option<&'a str> {
        match self {
            Node::Atom(s) => Some(s),
            _ => None,
        }
    }
    pub fn head(&self) -> Option<&'a str> {
        match self {
            Node::List(h, _) => Some(h),
            _ => None,
        }
    }
}

/// Lazy tokeniser. Port of `frontend.tokenize` / `_TOK`:
/// `\s+ | (<[^>]*>) | (#[^\n]*) | ([()]) | ("(?:[^"\\]|\\.)*") | ([^\s()]+)`.
/// IRIs `<...>` are matched before the comment rule so a `#` inside an IRI is
/// not treated as a comment. Comments (the `#...` group) are dropped.
pub struct Tokens<'a> {
    text: &'a str,
    i: usize,
}

const WHITESPACE: u8 = 1;
const ATOM_END: u8 = 2;

/// Byte classes for the tokenizer. `WHITESPACE` is exactly the set of bytes
/// `b` with `(b as char).is_whitespace()` (ASCII whitespace plus 0x85 and
/// 0xA0, as the per-byte `char` test has always classified them); `ATOM_END`
/// adds `(` and `)`.
const BYTE_CLASS: [u8; 256] = {
    let mut table = [0u8; 256];
    let mut b = 0;
    while b < 256 {
        if matches!(b, 0x09..=0x0D | 0x20 | 0x85 | 0xA0) {
            table[b] = WHITESPACE | ATOM_END;
        } else if b == b'(' as usize || b == b')' as usize {
            table[b] = ATOM_END;
        }
        b += 1;
    }
    table
};

/// Index of the first `needle` at or after `i`, or `bytes.len()`. Scans eight
/// bytes per step (SWAR zero-byte test); the result equals the plain
/// byte-by-byte scan's.
#[inline]
fn find_byte(bytes: &[u8], mut i: usize, needle: u8) -> usize {
    const LO: u64 = 0x0101_0101_0101_0101;
    const HI: u64 = 0x8080_8080_8080_8080;
    let n = bytes.len();
    let pattern = LO.wrapping_mul(needle as u64);
    while i + 8 <= n {
        let mut word = [0u8; 8];
        word.copy_from_slice(&bytes[i..i + 8]);
        let word = u64::from_le_bytes(word) ^ pattern;
        // A zero byte in `word` marks a match; the lowest flagged byte is
        // always a true zero, so `trailing_zeros` finds the first match.
        let found = word.wrapping_sub(LO) & !word & HI;
        if found != 0 {
            return i + (found.trailing_zeros() / 8) as usize;
        }
        i += 8;
    }
    while i < n && bytes[i] != needle {
        i += 1;
    }
    i
}

pub fn tokens(text: &str) -> Tokens<'_> {
    Tokens { text, i: 0 }
}

impl<'a> Iterator for Tokens<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        let bytes = self.text.as_bytes();
        let n = bytes.len();
        let mut i = self.i;
        while i < n {
            let c = bytes[i] as char;
            if BYTE_CLASS[bytes[i] as usize] & WHITESPACE != 0 {
                i += 1;
                continue;
            }
            if c == '<' {
                // IRI: <[^>]*>
                let start = i;
                i += 1;
                i = find_byte(bytes, i, b'>');
                if i < n {
                    i += 1; // consume '>'
                }
                self.i = i;
                return Some(&self.text[start..i]);
            }
            if c == '#' {
                // comment to end of line
                i = find_byte(bytes, i, b'\n');
                continue;
            }
            if c == '(' || c == ')' {
                self.i = i + 1;
                return Some(&self.text[i..i + 1]);
            }
            if c == '"' {
                // string literal: "(?:[^"\\]|\\.)*"
                let start = i;
                i += 1;
                while i < n {
                    let b = bytes[i];
                    if b == b'\\' {
                        i += 2;
                        continue;
                    }
                    if b == b'"' {
                        i += 1;
                        break;
                    }
                    i += 1;
                }
                // a `\\` escape can step past the end of the text
                if i > n {
                    i = n;
                }
                self.i = i;
                return Some(&self.text[start..i]);
            }
            // atom: [^\s()]+
            let start = i;
            while i < n && BYTE_CLASS[bytes[i] as usize] & ATOM_END == 0 {
                i += 1;
            }
            self.i = i;
            return Some(&self.text[start..i]);
        }
        self.i = i;
        None
    }
}

/// Eager tokenisation (kept for tests / small inputs).
pub fn tokenize(text: &str) -> Vec<&str> {
    tokens(text).collect()
}

/// Port of `frontend.P` recursive-descent parser, over the lazy token stream.
pub struct Parser<'a> {
    toks: std::iter::Peekable<Tokens<'a>>,
    /// Children of the lists currently being parsed, innermost last. Each
    /// finished list moves its children out into one exactly sized vector,
    /// instead of growing a fresh vector child by child.
    scratch: Vec<Node<'a>>,
}

impl<'a> Parser<'a> {
    pub fn new(text: &'a str) -> Self {
        Parser {
            toks: tokens(text).peekable(),
            scratch: Vec::new(),
        }
    }

    pub fn peek(&mut self) -> Option<&'a str> {
        self.toks.peek().copied()
    }

    pub fn next_tok(&mut self) -> Option<&'a str> {
        self.toks.next()
    }

    /// Parse list children up to and including the closing `)`.
    fn list_args(&mut self) -> Result<Vec<Node<'a>>, String> {
        let base = self.scratch.len();
        while self.peek() != Some(")") {
            if self.peek().is_none() {
                self.scratch.truncate(base);
                return Err("unexpected end of input".to_string());
            }
            match self.parse() {
                Ok(child) => self.scratch.push(child),
                Err(error) => {
                    self.scratch.truncate(base);
                    return Err(error);
                }
            }
        }
        self.next_tok(); // consume ')'
        Ok(self.scratch.drain(base..).collect())
    }

    /// Parse one node. A token followed by `(` becomes `(token, args...)`.
    /// Anonymous lists (used by HasKey) have an empty head.
    pub fn parse(&mut self) -> Result<Node<'a>, String> {
        let t = self
            .next_tok()
            .ok_or_else(|| "unexpected end of input".to_string())?;
        if t == "(" {
            let args = self.list_args()?;
            return Ok(Node::List("", args));
        }
        // An IRI before a HasKey property list is an argument, not a
        // constructor. Only bare functional-syntax keywords introduce lists.
        if t.bytes().all(|b| b.is_ascii_alphabetic()) && self.peek() == Some("(") {
            self.next_tok(); // consume '('
            let args = self.list_args()?;
            return Ok(Node::List(t, args));
        }
        Ok(Node::Atom(t))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn find_byte_matches_the_plain_scan() {
        let text = b"ab>cdefghij>klmnopqrstuvwxyz\n0123456789>>\n";
        for needle in [b'>', b'\n', b'z', b'#'] {
            for start in 0..=text.len() {
                let plain = text[start..].iter().position(|&b| b == needle).map_or(text.len(), |p| start + p);
                assert_eq!(find_byte(text, start, needle), plain, "{needle} {start}");
            }
        }
    }

    #[test]
    fn parser_errors_and_nesting_are_unchanged() {
        let mut p = Parser::new("A(B(c d) e(f) <g> (h i) j)");
        let node = p.parse().unwrap();
        assert_eq!(node, Node::List("A", vec![
            Node::List("B", vec![Node::Atom("c"), Node::Atom("d")]),
            Node::List("e", vec![Node::Atom("f")]),
            Node::Atom("<g>"),
            Node::List("", vec![Node::Atom("h"), Node::Atom("i")]),
            Node::Atom("j"),
        ]));
        assert!(Parser::new("A(B(c").parse().is_err());
        let mut p = Parser::new("A(B(c) ");
        assert!(p.parse().is_err());
        assert!(p.scratch.is_empty());
    }

    #[test]
    fn byte_classes_match_the_per_byte_char_tests() {
        for b in 0..=255u8 {
            let c = b as char;
            assert_eq!(BYTE_CLASS[b as usize] & WHITESPACE != 0, c.is_whitespace(), "{b:#x}");
            assert_eq!(BYTE_CLASS[b as usize] & ATOM_END != 0,
                c.is_whitespace() || c == '(' || c == ')', "{b:#x}");
        }
    }
}
