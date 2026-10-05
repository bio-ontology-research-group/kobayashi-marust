//! Validate self-contained, namespace-well-formed XML content without I/O.
use quick_xml::{events::Event, name::ResolveResult, NsReader};

fn qname(name: &[u8]) -> bool {
    let Ok(name) = std::str::from_utf8(name) else { return false };
    let parts: Vec<_> = name.split(':').collect();
    parts.len() <= 2 && parts.iter().all(|part| part.chars().next().is_some_and(super::lexical::name_start)
        && part.chars().all(super::lexical::name_char))
}
fn characters(text: &str) -> bool {
    text.chars().all(|c| matches!(c, '\t' | '\n' | '\r' | '\u{20}'..='\u{d7ff}'
        | '\u{e000}'..='\u{fffd}' | '\u{10000}'..='\u{10ffff}'))
}
pub(super) fn check(text: &str) -> Result<(), String> {
    let error = || "invalid OWL 2 DL input: rdf:XMLLiteral is not self-contained, namespace-well-formed XML content".to_owned();
    let source = format!("<kmLiteralRoot>{text}</kmLiteralRoot>");
    let mut reader = NsReader::from_str(&source);
    reader.config_mut().check_comments = true;
    let mut depth = 0usize;
    loop {
        let (namespace, event) = reader.read_resolved_event().map_err(|_|error())?;
        if matches!(namespace, ResolveResult::Unknown(_)) { return Err(error()); }
        let opens_element = matches!(&event, Event::Start(_));
        match event {
            Event::Start(element) | Event::Empty(element) => {
                if !qname(element.name().as_ref()) { return Err(error()); }
                let mut expanded_attributes = std::collections::BTreeSet::new();
                for attribute in element.attributes() {
                    let attribute = attribute.map_err(|_|error())?;
                    if !qname(attribute.key.as_ref()) { return Err(error()); }
                    if attribute.value.contains(&b'<') { return Err(error()); }
                    let value = attribute.unescape_value().map_err(|_|error())?;
                    if !characters(&value) { return Err(error()); }
                    if attribute.key.as_ref().starts_with(b"xmlns:") && value.is_empty() { return Err(error()); }
                    if attribute.key.as_ref()==b"xmlns" || attribute.key.as_ref().starts_with(b"xmlns:") { continue; }
                    let (namespace, local) = reader.resolve_attribute(attribute.key);
                    let namespace = match namespace {
                        ResolveResult::Unknown(_) => return Err(error()),
                        ResolveResult::Bound(ns) => ns.as_ref().to_vec(),
                        ResolveResult::Unbound => Vec::new(),
                    };
                    if !expanded_attributes.insert((namespace,local.as_ref().to_vec())) { return Err(error()); }
                }
                depth += usize::from(opens_element);
            }
            Event::Text(value) => {
                if value.as_ref().windows(3).any(|v|v==b"]]>") || !characters(&value.unescape().map_err(|_|error())?) { return Err(error()); }
            }
            Event::PI(value) => {
                if !qname(value.target()) || value.target().eq_ignore_ascii_case(b"xml") { return Err(error()); }
            }
            Event::DocType(_) | Event::Decl(_) => return Err(error()),
            Event::End(_) => { depth = depth.checked_sub(1).ok_or_else(error)?; if depth==0 && reader.buffer_position() as usize != source.len() { return Err(error()); } }
            Event::Eof => return if depth==0 {Ok(())} else {Err(error())},
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::check;
    #[test]
    fn accepts_xml_content_and_rejects_unbound_or_malformed_markup() {
        for value in ["", "text &amp; more", "<a/><b/>", "<p:a xmlns:p='urn:p' p:x='1'/>", "<!--ok--><?target data?>"] {
            assert!(check(value).is_ok(), "{value}");
        }
        for value in ["<a x='<b'/>", "bad]]>text", "<a xmlns:p=''/>", "<a>", "<a></b>", "<p:a/>", "<a p:x='1'/>", "&unknown;", "&#0;", "<!--a--b-->", "<?xml version='1.0'?>", "</kmLiteralRoot><x>", "<a xmlns:p='urn:x' xmlns:q='urn:x' p:x='1' q:x='2'/>"] {
            assert!(check(value).is_err(), "{value}");
        }
    }
}
