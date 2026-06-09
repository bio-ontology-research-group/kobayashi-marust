//! Tokeniser + s-expression parser for OWL functional syntax.
//!
//! Direct port of `frontend.tokenize` (the `_TOK` regex) and the `class P`
//! recursive-descent parser in `engine/py/frontend.py`. A parsed node is either
//! an atom string or a `(head, [args])` pair.

/// A parsed s-expression node: a bare token, or a head with arguments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Node {
    Atom(String),
    List(String, Vec<Node>),
}

impl Node {
    pub fn as_atom(&self) -> Option<&str> {
        match self {
            Node::Atom(s) => Some(s.as_str()),
            _ => None,
        }
    }
    pub fn head(&self) -> Option<&str> {
        match self {
            Node::List(h, _) => Some(h.as_str()),
            _ => None,
        }
    }
}

/// Port of `frontend.tokenize` / `_TOK`:
/// `\s+ | (<[^>]*>) | (#[^\n]*) | ([()]) | ("(?:[^"\\]|\\.)*") | ([^\s()]+)`.
/// IRIs `<...>` are matched before the comment rule so a `#` inside an IRI is
/// not treated as a comment. Comments (the `#...` group) are dropped.
pub fn tokenize(text: &str) -> Vec<String> {
    let bytes = text.as_bytes();
    let n = bytes.len();
    let mut i = 0;
    let mut out: Vec<String> = Vec::new();
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
            out.push(text[start..i].to_string());
            continue;
        }
        if c == '#' {
            // comment to end of line
            while i < n && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if c == '(' || c == ')' {
            out.push(c.to_string());
            i += 1;
            continue;
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
            out.push(text[start..i].to_string());
            continue;
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
        out.push(text[start..i].to_string());
    }
    out
}

/// Port of `frontend.P` recursive-descent parser.
pub struct Parser {
    toks: Vec<String>,
    i: usize,
}

impl Parser {
    pub fn new(toks: Vec<String>) -> Self {
        Parser { toks, i: 0 }
    }

    pub fn peek(&self) -> Option<&str> {
        self.toks.get(self.i).map(|s| s.as_str())
    }

    fn next(&mut self) -> String {
        let t = self.toks[self.i].clone();
        self.i += 1;
        t
    }

    /// Parse one node. Mirrors `P.parse`: a leading `(` is an error; a token
    /// followed by `(` becomes `(token, args...)` up to the matching `)`.
    pub fn parse(&mut self) -> Result<Node, String> {
        let t = self.next();
        if t == "(" {
            return Err("unexpected (".to_string());
        }
        if self.peek() == Some("(") {
            self.next(); // consume '('
            let mut args = Vec::new();
            while self.peek() != Some(")") {
                if self.peek().is_none() {
                    return Err("unexpected end of input".to_string());
                }
                args.push(self.parse()?);
            }
            self.next(); // consume ')'
            return Ok(Node::List(t, args));
        }
        Ok(Node::Atom(t))
    }
}
