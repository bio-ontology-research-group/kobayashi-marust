//! Fast deserialization of internally tagged enums whose tag comes first.
//!
//! `#[serde(tag = "...")]` makes serde buffer every value into an
//! intermediate `Content` tree and decode it a second time, which made the
//! clause decoding of large inputs slow (ore_ont_12128: 5.2 s in the
//! orchestrator and 2.4 s in the tableau worker). Every KM writer emits the
//! tag as the first key (derived `Serialize` of an internally tagged enum
//! does), so `tag_first_enum!` decodes such a map in one pass: it reads the
//! tag, then the variant's fields directly. Any other shape (tag not first,
//! a sequence) is decoded by the original derived representation, kept as a
//! private shadow type, so every input decodes exactly as before: same
//! values, unknown fields ignored, missing or duplicate fields rejected.

use serde::de::{self, Visitor};
use std::fmt;

/// A map key or tag value, borrowed from the input when possible.
pub(crate) enum Name<'de> {
    Borrowed(&'de str),
    Owned(String),
}

impl Name<'_> {
    pub(crate) fn as_str(&self) -> &str {
        match self {
            Name::Borrowed(s) => s,
            Name::Owned(s) => s,
        }
    }
}

impl<'de> de::Deserialize<'de> for Name<'de> {
    fn deserialize<D: de::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        struct V;
        impl<'de> Visitor<'de> for V {
            type Value = Name<'de>;
            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str("a string")
            }
            fn visit_borrowed_str<E: de::Error>(self, v: &'de str) -> Result<Name<'de>, E> {
                Ok(Name::Borrowed(v))
            }
            fn visit_str<E: de::Error>(self, v: &str) -> Result<Name<'de>, E> {
                Ok(Name::Owned(v.to_owned()))
            }
            fn visit_string<E: de::Error>(self, v: String) -> Result<Name<'de>, E> {
                Ok(Name::Owned(v))
            }
        }
        d.deserialize_str(V)
    }
}

/// `tag_first_enum!(Type, Shadow, "tag", { "name" => Variant { field: Ty, ... }, ... })`
/// implements `Deserialize` for `Type` (whose `Serialize` stays derived) and
/// defines `Shadow`, the derived internally tagged twin used as the fallback.
#[macro_export]
macro_rules! tag_first_enum {
    ($ty:ident, $shadow:ident, $tag:literal, { $( $vname:literal => $variant:ident { $( $field:ident : $fty:ty ),* $(,)? } ),* $(,)? }) => {
        #[derive(serde::Deserialize)]
        #[serde(tag = $tag)]
        enum $shadow {
            $( #[serde(rename = $vname)] $variant { $( $field: $fty ),* } ),*
        }

        impl From<$shadow> for $ty {
            fn from(shadow: $shadow) -> Self {
                match shadow {
                    $( $shadow::$variant { $( $field ),* } => $ty::$variant { $( $field ),* } ),*
                }
            }
        }

        impl<'de> serde::Deserialize<'de> for $ty {
            fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
                use serde::de::{self, MapAccess, SeqAccess, Visitor};
                struct V;
                impl<'de> Visitor<'de> for V {
                    type Value = $ty;
                    fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                        write!(f, "an internally tagged {}", stringify!($ty))
                    }
                    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<$ty, A::Error> {
                        let Some(first) = map.next_key::<$crate::tag_first::Name<'de>>()? else {
                            return Err(de::Error::missing_field($tag));
                        };
                        if first.as_str() != $tag {
                            // Slow path: buffer everything, decode as derived.
                            let mut object = serde_json::Map::new();
                            object.insert(first.as_str().to_owned(), map.next_value::<serde_json::Value>()?);
                            while let Some((key, value)) = map.next_entry::<String, serde_json::Value>()? {
                                object.insert(key, value);
                            }
                            return serde_json::from_value::<$shadow>(serde_json::Value::Object(object))
                                .map($ty::from)
                                .map_err(de::Error::custom);
                        }
                        let tag = map.next_value::<$crate::tag_first::Name<'de>>()?;
                        $(
                            if tag.as_str() == $vname {
                                $( let mut $field: Option<$fty> = None; )*
                                while let Some(key) = map.next_key::<$crate::tag_first::Name<'de>>()? {
                                    let key = key.as_str();
                                    $(
                                        if key == stringify!($field) {
                                            if $field.is_some() {
                                                return Err(de::Error::duplicate_field(stringify!($field)));
                                            }
                                            $field = Some(map.next_value()?);
                                            continue;
                                        }
                                    )*
                                    if key == $tag {
                                        return Err(de::Error::duplicate_field($tag));
                                    }
                                    map.next_value::<de::IgnoredAny>()?;
                                }
                                return Ok($ty::$variant {
                                    $( $field: $field.ok_or_else(|| de::Error::missing_field(stringify!($field)))? ),*
                                });
                            }
                        )*
                        Err(de::Error::unknown_variant(tag.as_str(), &[$( $vname ),*]))
                    }
                    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<$ty, A::Error> {
                        let mut items = Vec::new();
                        while let Some(item) = seq.next_element::<serde_json::Value>()? {
                            items.push(item);
                        }
                        serde_json::from_value::<$shadow>(serde_json::Value::Array(items))
                            .map($ty::from)
                            .map_err(de::Error::custom)
                    }
                }
                d.deserialize_any(V)
            }
        }
    };
}

#[cfg(test)]
mod tests {
    use crate::json_io::{JAtom, JClause, JTerm};

    // The derived internally tagged twins, as the types were before.
    #[derive(serde::Deserialize, serde::Serialize, PartialEq, Debug)]
    #[serde(tag = "kind")]
    enum OldTerm {
        #[serde(rename = "var")]
        Var { name: String },
        #[serde(rename = "ind")]
        Ind { name: String },
        #[serde(rename = "aux")]
        Aux { root: String, label: Vec<(String, i64)> },
        #[serde(rename = "fun")]
        Fun { function: String, arg: Box<OldTerm> },
    }
    #[derive(serde::Deserialize, serde::Serialize, PartialEq, Debug)]
    #[serde(tag = "kind")]
    enum OldAtom {
        #[serde(rename = "concept")]
        Concept { concept: String, term: OldTerm },
        #[serde(rename = "role")]
        Role { role: String, source: OldTerm, target: OldTerm },
        #[serde(rename = "eq")]
        Eq { left: OldTerm, right: OldTerm },
    }

    fn same(json: &str) {
        let new: Result<JAtom, _> = serde_json::from_str(json);
        let old: Result<OldAtom, _> = serde_json::from_str(json);
        match (new, old) {
            (Ok(new), Ok(old)) => assert_eq!(
                serde_json::to_value(&new).unwrap(),
                serde_json::to_value(&old).unwrap(),
                "{json}"
            ),
            (Err(_), Err(_)) => {}
            (new, old) => panic!("{json}: new ok={} old ok={}", new.is_ok(), old.is_ok()),
        }
    }

    #[test]
    fn tag_first_decoding_matches_the_derived_internally_tagged_enum() {
        let _test_env = crate::test_env::read();
        for json in [
            r#"{"kind":"concept","concept":"A","term":{"kind":"var","name":"x"}}"#,
            r#"{"concept":"A","kind":"concept","term":{"name":"x","kind":"var"}}"#,
            r#"{"kind":"role","role":"r","source":{"kind":"ind","name":"a"},"target":{"kind":"fun","function":"f","arg":{"kind":"var","name":"x"}}}"#,
            r#"{"kind":"eq","left":{"kind":"aux","root":"q","label":[["l",3],["m",-1]]},"right":{"kind":"var","name":"y"}}"#,
            r#"{"kind":"concept","concept":"A","term":{"kind":"var","name":"x"},"extra":[1,{"k":2}]}"#,
            r#"{"kind":"concept","concept":"Aé\"q","term":{"kind":"var","name":"x\\n"}}"#,
            r#"{"kind":"concept","term":{"kind":"var","name":"x"}}"#,
            r#"{"kind":"concept","concept":"A","concept":"B","term":{"kind":"var","name":"x"}}"#,
            r#"{"kind":"nope","concept":"A"}"#,
            r#"{"concept":"A"}"#,
            r#"{}"#,
            r#"["concept","A",{"kind":"var","name":"x"}]"#,
        ] {
            same(json);
        }
    }

    #[test]
    fn tag_first_decoding_round_trips_written_clauses() {
        let _test_env = crate::test_env::read();
        let clause = JClause {
            body: vec![JAtom::Role {
                role: "r".into(),
                source: JTerm::Var { name: "x".into() },
                target: JTerm::Fun { function: "f".into(), arg: Box::new(JTerm::Var { name: "x".into() }) },
            }],
            head: vec![JAtom::Concept {
                concept: "B".into(),
                term: JTerm::Aux { root: "q".into(), label: vec![("l".into(), 2)] },
            }],
        };
        let text = serde_json::to_string(&clause).unwrap();
        let back: JClause = serde_json::from_str(&text).unwrap();
        assert!(back == clause);
        let reader: JClause = serde_json::from_reader(text.as_bytes()).unwrap();
        assert!(reader == clause);
    }
}
