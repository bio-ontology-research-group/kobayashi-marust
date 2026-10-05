//! Lexical-space checks that do not depend on the reasoner's numeric storage.
//! Arbitrarily large integer and decimal spellings remain valid OWL literals.

fn signed_digits(text: &str) -> Option<(bool, &str)> {
    let negative = text.starts_with('-');
    let digits = text.strip_prefix(['+', '-']).unwrap_or(text);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) { return None; }
    let digits = digits.trim_start_matches('0');
    Some((negative && !digits.is_empty(), if digits.is_empty() { "0" } else { digits }))
}

fn decimal(text: &str) -> bool {
    let text = text.strip_prefix(['+', '-']).unwrap_or(text);
    let mut dot = false;
    let mut digits = 0;
    for b in text.bytes() {
        if b == b'.' && !dot { dot = true; }
        else if b.is_ascii_digit() { digits += 1; }
        else { return false; }
    }
    digits > 0
}

fn at_most(digits: &str, bound: &str) -> bool {
    digits.len() < bound.len() || (digits.len() == bound.len() && digits <= bound)
}

pub(super) fn name_start(c: char) -> bool {
    matches!(c, ':' | '_' | 'A'..='Z' | 'a'..='z' | '\u{c0}'..='\u{d6}' | '\u{d8}'..='\u{f6}'
        | '\u{f8}'..='\u{2ff}' | '\u{370}'..='\u{37d}' | '\u{37f}'..='\u{1fff}'
        | '\u{200c}'..='\u{200d}' | '\u{2070}'..='\u{218f}' | '\u{2c00}'..='\u{2fef}'
        | '\u{3001}'..='\u{d7ff}' | '\u{f900}'..='\u{fdcf}' | '\u{fdf0}'..='\u{fffd}'
        | '\u{10000}'..='\u{effff}')
}
pub(super) fn name_char(c: char) -> bool {
    name_start(c) || matches!(c, '-' | '.' | '0'..='9' | '\u{b7}' | '\u{300}'..='\u{36f}' | '\u{203f}'..='\u{2040}')
}
fn derived_string(text: &str, kind: &str) -> bool {
    // All constrained string types below have the collapse whitespace facet.
    let text = text.trim_matches([' ', '\t', '\r', '\n']);
    if text.is_empty() { return false; }
    match kind {
        "language" => text.split('-').enumerate().all(|(i,part)| !part.is_empty()
            && part.len()<=8 && part.bytes().all(|b| if i==0 { b.is_ascii_alphabetic() } else { b.is_ascii_alphanumeric() })),
        "Name" => text.chars().next().is_some_and(name_start) && text.chars().all(name_char),
        "NCName" => !text.contains(':') && text.chars().next().is_some_and(name_start) && text.chars().all(name_char),
        "NMTOKEN" => text.chars().all(name_char),
        _ => unreachable!(),
    }
}

fn base64(text: &str) -> bool {
    let bytes: Vec<_> = text.bytes().filter(|b| !matches!(b, b' ' | b'\t' | b'\r' | b'\n')).collect();
    if bytes.len() % 4 != 0 { return false; }
    let value = |b: u8| -> Option<u8> { match b {
        b'A'..=b'Z' => Some(b-b'A'), b'a'..=b'z' => Some(b-b'a'+26),
        b'0'..=b'9' => Some(b-b'0'+52), b'+' => Some(62), b'/' => Some(63), _ => None,
    }};
    let padding = bytes.iter().rev().take_while(|&&b| b == b'=').count();
    if padding > 2 { return false; }
    let content = &bytes[..bytes.len()-padding];
    if content.iter().any(|&b| value(b).is_none()) { return false; }
    match padding {
        0 => true,
        1 => content.last().and_then(|&b| value(b)).is_some_and(|v| v & 3 == 0),
        2 => content.last().and_then(|&b| value(b)).is_some_and(|v| v & 15 == 0),
        _ => false,
    }
}

fn date_time(text: &str, require_zone: bool) -> bool {
    if !text.is_ascii() { return false; }
    let Some((date, time)) = text.split_once('T') else { return false };
    let mut fields = date.rsplitn(3, '-');
    let (Some(day),Some(month),Some(year)) = (fields.next(),fields.next(),fields.next()) else { return false };
    let digits = year.strip_prefix('-').unwrap_or(year);
    if digits.len()<4 || !digits.bytes().all(|b| b.is_ascii_digit())
        || (digits.len()>4 && digits.starts_with('0')) || (year.starts_with('-') && digits.bytes().all(|b| b==b'0')) { return false; }
    let year_mod400 = digits.bytes().fold(0u32, |v,b| (10*v+u32::from(b-b'0'))%400);
    let two = |s: &str| -> Option<u32> { (s.len()==2 && s.bytes().all(|b| b.is_ascii_digit())).then(|| s.parse().ok()).flatten() };
    let (Some(day),Some(month)) = (two(day),two(month)) else { return false };
    let leap = year_mod400%4==0 && (year_mod400%100!=0 || year_mod400==0);
    let days = match month { 1|3|5|7|8|10|12=>31,4|6|9|11=>30,2=>if leap {29} else {28},_=>return false };
    if day==0 || day>days { return false; }
    let clock = if let Some(clock) = time.strip_suffix('Z') { clock }
    else if time.len()>=6 && matches!(time.as_bytes()[time.len()-6],b'+'|b'-') {
        let (clock, zone)=time.split_at(time.len()-6);
        if zone.as_bytes()[3]!=b':' { return false; }
        let (Some(hour),Some(minute))=(two(&zone[1..3]),two(&zone[4..])) else { return false };
        if hour>14 || minute>59 || (hour==14 && minute!=0) { return false; }
        clock
    } else { if require_zone { return false; } time };
    let fields: Vec<_> = clock.split(':').collect();
    let [hour,minute,second]=fields.as_slice() else { return false };
    let (Some(hour),Some(minute))=(two(hour),two(minute)) else { return false };
    let (second,fraction)=second.split_once('.').map_or((*second,None),|(s,f)|(s,Some(f)));
    let Some(second)=two(second) else { return false };
    if fraction.is_some_and(|f|f.is_empty() || !f.bytes().all(|b|b.is_ascii_digit())) { return false; }
    hour<=24 && minute<=59 && second<=59 && (hour!=24 || (minute==0 && second==0 && fraction.is_none_or(|f|f.bytes().all(|b|b==b'0'))))
}

pub(super) fn integer(text: &str, kind: &str) -> bool {
    let Some((negative, digits)) = signed_digits(text) else { return false };
    let zero = digits == "0";
    match kind {
        "integer" => true,
        "nonNegativeInteger" => !negative,
        "positiveInteger" => !negative && !zero,
        "nonPositiveInteger" => negative || zero,
        "negativeInteger" => negative,
        "long" => at_most(digits, if negative { "9223372036854775808" } else { "9223372036854775807" }),
        "int" => at_most(digits, if negative { "2147483648" } else { "2147483647" }),
        "short" => at_most(digits, if negative { "32768" } else { "32767" }),
        "byte" => at_most(digits, if negative { "128" } else { "127" }),
        "unsignedLong" => !negative && at_most(digits, "18446744073709551615"),
        "unsignedInt" => !negative && at_most(digits, "4294967295"),
        "unsignedShort" => !negative && at_most(digits, "65535"),
        "unsignedByte" => !negative && at_most(digits, "255"),
        _ => unreachable!(),
    }
}

pub(super) fn check(quoted: &str, datatype: &str) -> Result<(), String> {
    let Some(body) = quoted.strip_prefix('"').and_then(|s| s.strip_suffix('"')) else {
        return Err("invalid OWL 2 DL input: unterminated literal".into());
    };
    let mut lexical = String::with_capacity(body.len());
    let mut chars = body.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some(c @ ('\\' | '"')) => lexical.push(c),
                _ => return Err("invalid OWL 2 DL input: invalid functional-syntax literal escape".into()),
            }
        } else { lexical.push(c); }
    }
    if !lexical.chars().all(|c| matches!(c, '\t' | '\n' | '\r' | '\u{20}'..='\u{d7ff}' | '\u{e000}'..='\u{fffd}' | '\u{10000}'..='\u{10ffff}')) {
        return Err("invalid OWL 2 DL input: literal contains a character outside the XML character set".into());
    }
    if datatype == "http://www.w3.org/2002/07/owl#rational" {
        let valid = lexical.split_once('/').is_some_and(|(num,den)| signed_digits(num).is_some()
            && !den.is_empty() && den.bytes().all(|b|b.is_ascii_digit()) && den.bytes().any(|b|b!=b'0'));
        return if valid { Ok(()) } else { Err(format!("invalid OWL 2 DL input: {quoted} is outside the lexical space of owl:rational (integer/positive denominator, no spaces or denominator sign)")) };
    }
    if datatype == "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral" {
        let valid = lexical.rsplit_once('@').is_some_and(|(_, tag)| tag.is_empty()
            || oxilangtag::LanguageTag::parse(tag).is_ok());
        return if valid { Ok(()) } else { Err("invalid OWL 2 DL input: rdf:PlainLiteral requires a final @ followed by an empty or well-formed language tag".into()) };
    }
    if datatype == "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral" {
        return super::xml_literal::check(&lexical);
    }
    let Some(kind) = datatype.strip_prefix("http://www.w3.org/2001/XMLSchema#") else { return Ok(()) };
    let text = lexical.trim_matches([' ', '\t', '\r', '\n']);
    let valid = match kind {
        "boolean" => matches!(text, "true" | "false" | "1" | "0"),
        "decimal" => decimal(text),
        "integer" | "nonNegativeInteger" | "positiveInteger" | "nonPositiveInteger"
            | "negativeInteger" | "long" | "int" | "short" | "byte" | "unsignedLong"
            | "unsignedInt" | "unsignedShort" | "unsignedByte" => integer(text, kind),
        "float" | "double" => {
            if matches!(text, "INF" | "+INF" | "-INF" | "NaN") { true }
            else if let Some((mantissa, exponent)) = text.split_once(['e', 'E']) {
                decimal(mantissa) && signed_digits(exponent).is_some()
            } else { decimal(text) }
        }
        "hexBinary" => text.len() % 2 == 0 && text.bytes().all(|b| b.is_ascii_hexdigit()),
        "base64Binary" => base64(text),
        "dateTime" | "dateTimeStamp" => date_time(text, kind=="dateTimeStamp"),
        "language" | "Name" | "NCName" | "NMTOKEN" => derived_string(text, kind),
        // The remaining built-in lexical spaces are checked separately in
        // subsequent conformance work. Success here alone is not certification.
        _ => true,
    };
    if valid { Ok(()) }
    else { Err(format!("invalid OWL 2 DL input: {quoted} is outside the lexical space of <{datatype}>")) }
}

#[cfg(test)]
mod tests {
    use super::check;
    fn valid(lex: &str, kind: &str) -> bool {
        check(&format!("\"{lex}\""), &format!("http://www.w3.org/2001/XMLSchema#{kind}")).is_ok()
    }
    #[test]
    fn integer_validation_preserves_arbitrary_precision_and_derived_bounds() {
        assert!(valid(&"9".repeat(200), "integer"));
        for (kind, good, bad) in [("byte", "-128", "128"), ("int", "2147483647", "2147483648"),
            ("unsignedLong", "18446744073709551615", "18446744073709551616"),
            ("positiveInteger", "+0001", "0"), ("negativeInteger", "-1", "-0")] {
            assert!(valid(good,kind)); assert!(!valid(bad,kind));
        }
        assert!(valid("-0", "unsignedByte"));
        for bad in ["", "+", "1.0", "1e2", "1 2", "１２"] { assert!(!valid(bad, "integer")); }
    }
    #[test]
    fn boolean_decimal_float_and_hex_lexical_spaces_are_checked() {
        assert!(valid(" true ", "boolean")); assert!(!valid("TRUE", "boolean"));
        assert!(valid("+.5", "decimal")); assert!(!valid("1e2", "decimal"));
        assert!(valid("1e999999999999999999999", "float"));
        for good in ["INF", "+INF", "-INF", "NaN", "-.5E+2"] { assert!(valid(good, "double")); }
        for bad in ["inf", "1e", "1e2e3", "."] { assert!(!valid(bad, "double")); }
        assert!(valid("a0FF", "hexBinary")); assert!(!valid("abc", "hexBinary"));
    }
    #[test]
    fn binary_padding_and_datetime_lexical_bounds() {
        for good in ["", "TQ==", "TWE=", "T W F u", " TQ==\n"] { assert!(valid(good,"base64Binary")); }
        for bad in ["TQ=", "TR==", "TWF=", "====", "AA=A", "TQ==\u{a0}"] { assert!(!valid(bad,"base64Binary")); }
        for good in ["2000-02-29T24:00:00Z", "0000-01-01T00:00:00+14:00", "123456789123456789123456789-01-01T00:00:00Z"] { assert!(valid(good,"dateTimeStamp"),"{good}"); }
        for bad in ["1900-02-29T00:00:00Z", "2000-01-01T24:00:00.1Z", "2000-01-01T00:00:00+14:01", "-0000-01-01T00:00:00Z", "2000-01-01T00:00:00"] { assert!(!valid(bad,"dateTimeStamp"),"{bad}"); }
        assert!(valid("2000-01-01T00:00:00","dateTime"));
    }
    #[test]
    fn derived_strings_and_arbitrary_rationals() {
        for (text,kind) in [("en-GB","language"),("a:b","Name"),("éclair","NCName"),("9a:b","NMTOKEN")] { assert!(valid(text,kind)); }
        for (text,kind) in [("en--GB","language"),("9name","Name"),("a:b","NCName"),("a b","NMTOKEN")] { assert!(!valid(text,kind)); }
        let rational = |s: &str| check(&format!("\"{s}\""),"http://www.w3.org/2002/07/owl#rational").is_ok();
        assert!(rational(&format!("+{}/{}","9".repeat(200),"8".repeat(200))));
        for bad in ["1/0","1/+2","1/-2","1 /2","1/2/3"] { assert!(!rational(bad)); }
        assert!(!valid("\u{0}","string"));
    }
}
