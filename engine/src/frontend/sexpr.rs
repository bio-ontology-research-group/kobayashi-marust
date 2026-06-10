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
            if c.is_whitespace() {
                i += 1;
                continue;
            }
            if c == '<' {
                // IRI: <[^>]*>
                let start = i;
                i += 1;
                while i < n && bytes[i] != b'>' {
                    i += 1;
                }
                if i < n {
                    i += 1; // consume '>'
                }
                self.i = i;
                return Some(&self.text[start..i]);
            }
            if c == '#' {
                // comment to end of line
                while i < n && bytes[i] != b'\n' {
                    i += 1;
                }
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
            while i < n {
                let b = bytes[i] as char;
                if b.is_whitespace() || b == '(' || b == ')' {
                    break;
                }
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
}

impl<'a> Parser<'a> {
    pub fn new(text: &'a str) -> Self {
        Parser {
            toks: tokens(text).peekable(),
        }
    }

    pub fn peek(&mut self) -> Option<&'a str> {
        self.toks.peek().copied()
    }

    pub fn next_tok(&mut self) -> Option<&'a str> {
        self.toks.next()
    }

    /// Parse one node. Mirrors `P.parse`: a leading `(` is an error; a token
    /// followed by `(` becomes `(token, args...)` up to the matching `)`.
    pub fn parse(&mut self) -> Result<Node<'a>, String> {
        let t = self
            .next_tok()
            .ok_or_else(|| "unexpected end of input".to_string())?;
        if t == "(" {
            return Err("unexpected (".to_string());
        }
        if self.peek() == Some("(") {
            self.next_tok(); // consume '('
            let mut args = Vec::new();
            while self.peek() != Some(")") {
                if self.peek().is_none() {
                    return Err("unexpected end of input".to_string());
                }
                args.push(self.parse()?);
            }
            self.next_tok(); // consume ')'
            return Ok(Node::List(t, args));
        }
        Ok(Node::Atom(t))
    }
}
