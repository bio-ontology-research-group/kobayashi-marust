//! The data vocabulary the relation generator decides, made exact
//! (docs/DATATYPES.md, "Boolean data ranges and ordered cells").
//!
//! The relation generator relates the `__dt__` names of a clause set pairwise
//! and adds covers. That is exact only when every admissible label set of a
//! data node (a set of names closed under the emitted clauses) has a value
//! with exactly those labels. This module supplies the three parts that
//! make it so, and reports every name for which it cannot:
//!
//! 1. *Boolean structure.* `DataIntersectionOf`, `DataUnionOf` and
//!    `DataComplementOf` names get definitional clauses over their operands,
//!    and the operands join the vocabulary and the role groups. A complex
//!    name is then equivalent, in every model of the clauses, to the Boolean
//!    combination of its operand names.
//! 2. *Ordered cells.* In a role group with two or more atomic ranges of the
//!    decimal tower (one of them not integral) or of one IEEE width, the
//!    range endpoints cut the partition into cells (points, open decimal
//!    gaps split into their integers and their non-integers, IEEE rank
//!    segments). Every cell lies inside or outside each range of the group,
//!    and every range is covered by its cells, so every data node with a
//!    range of the partition carries a cell, which fixes its membership in
//!    every range.
//! 3. *The decided fragment.* A name whose structure or value the datatype
//!    map defines but the oracle does not decide (a pattern or length facet,
//!    a dateTime facet, an ill-typed literal, a literal whose membership in a
//!    range is undecided) is reported, and the frontend publishes the input
//!    as not represented (`DROPPED`). Datatypes outside the OWL 2 datatype
//!    map (custom IRIs, `xsd:date`, `xsd:duration`, ...) have no fixed value
//!    space and keep the free abstraction.
use super::{
    builtin_datatype_key, cx, datatype_concept_key, glued_atoms, integral_cell_name, parse_literal,
    range_disjoint, range_from_node, range_of_internal_name, range_subsumed, rat_cmp, rat_midpoint,
    val_in_range, FloatRange, Node, Parser, Partition, Rat, Val, DRange,
};
use crate::frontend::clauses::{clause, DLClause};
use std::collections::BTreeSet;

/// Upper bound on the cells of one partition in one role group. A group
/// that needs more is reported (`too many data cells`), not approximated.
const MAX_CELLS: usize = 512;

/// The expanded vocabulary and the clauses that make it exact.
#[derive(Default)]
pub(crate) struct DataVocabulary {
    /// Source names, the operands of their Boolean structure (closed
    /// transitively) and the cells.
    pub(crate) names: BTreeSet<String>,
    /// The role groups with the operands and cells added.
    pub(crate) groups: Option<Vec<BTreeSet<String>>>,
    /// `DataUnionOf` names with their member names (cover `U → ⋁ M`).
    pub(crate) unions: Vec<(String, Vec<String>)>,
    /// `DataComplementOf` names with their operand (excluded middle).
    pub(crate) complements: Vec<(String, String)>,
    /// Names with Boolean structure: their exhaustion and counting are
    /// decided on their operands and cells, not on the name itself.
    pub(crate) boolean: BTreeSet<String>,
    /// Definitional clauses beyond the union covers and excluded middles,
    /// and the cell clauses.
    pub(crate) extra: Vec<DLClause>,
    /// Names outside the decided fragment, with the reason.
    pub(crate) undecided: Vec<(&'static str, String)>,
}

/// The `__dt__` name of a data-range node, as the parser names it.
fn operand_name(node: &Node) -> String {
    match node {
        Node::Atom(atom) => format!("__dt__{}", datatype_concept_key(atom)),
        list => format!("__dt__c__{}", crate::frontend::parse::serialize_node(list)),
    }
}

enum Structure {
    Union(Vec<String>),
    Intersection(Vec<String>),
    Complement(String),
}

/// The Boolean structure of a complex range name. An intersection of facet
/// intervals of one base is an atomic interval (`range_from_node` merges
/// it) and has none.
fn structure(name: &str) -> Option<Structure> {
    let text = name.strip_prefix("__dt__c__")?;
    let node = Parser::new(text).parse().ok()?;
    match &node {
        Node::List("DataUnionOf", args) if args.len() >= 2 =>
            Some(Structure::Union(args.iter().map(operand_name).collect())),
        Node::List("DataComplementOf", args) if args.len() == 1 =>
            Some(Structure::Complement(operand_name(&args[0]))),
        Node::List("DataIntersectionOf", args) if args.len() >= 2 => match range_from_node(&node) {
            DRange::Intersection(_) => Some(Structure::Intersection(args.iter().map(operand_name).collect())),
            _ => None,
        },
        _ => None,
    }
}

fn parsed(name: &str) -> Option<DRange> {
    match super::classify_name(name)? {
        super::DtEntry::Range(_, range) => Some(range),
        super::DtEntry::Value(_, value) => Some(DRange::OneOf(vec![value])),
    }
}

/// Datatypes the parser recognises that are not in the OWL 2 datatype map:
/// their value spaces are not fixed, so their names and literals are free.
fn outside_map(key: &str) -> bool {
    matches!(key, "date" | "time" | "gYear" | "gMonth" | "gDay" | "gYearMonth" | "gMonthDay" | "duration")
}

fn literal_status(literal: &str) -> Result<(), &'static str> {
    let Some((value, datatype)) = parse_literal(literal) else {
        return Err("a data literal that does not parse");
    };
    if let Val::Opaque(_) = value {
        let key = datatype.as_deref().and_then(builtin_datatype_key);
        if key.is_some_and(|key| !outside_map(key)) {
            return Err("a literal of the datatype map outside the decided value fragment");
        }
    }
    Ok(())
}

fn atomic_status(key: &str) -> Result<(), &'static str> {
    if key.starts_with("iri__") {
        return Ok(());
    }
    match range_of_internal_name(key) {
        DRange::Unknown if !outside_map(key) => Err("a datatype of the map outside the decided fragment"),
        _ => Ok(()),
    }
}

fn node_status(node: &Node) -> Result<(), &'static str> {
    match node {
        Node::Atom(atom) => atomic_status(&datatype_concept_key(atom)),
        Node::List("DataIntersectionOf" | "DataUnionOf", args) => args.iter().try_for_each(node_status),
        Node::List("DataComplementOf", args) if args.len() == 1 => node_status(&args[0]),
        Node::List("DataOneOf", args) => match glued_atoms(args) {
            Some(literals) => literals.iter().try_for_each(|literal| literal_status(literal)),
            None => Err("a data enumeration with a non-literal member"),
        },
        Node::List("DatatypeRestriction", args) => {
            let base = args.first().and_then(|arg| arg.as_atom());
            match base.and_then(builtin_datatype_key) {
                None if base.is_some() => Ok(()),
                Some(key) if outside_map(key) => Ok(()),
                _ if matches!(range_from_node(node), DRange::Unknown) =>
                    Err("a facet restriction outside the decided fragment (pattern, length, digits, or a non-numeric base)"),
                _ => Ok(()),
            }
        }
        _ => Err("a data range of unknown shape"),
    }
}

/// Whether `name` is inside the decided fragment (see the module comment).
fn name_status(name: &str) -> Result<(), &'static str> {
    if super::is_value_aux_name(name) {
        return Ok(());
    }
    let Some(rest) = name.strip_prefix("__dt__") else { return Ok(()) };
    if matches!(rest, "opaque" | "val" | "val__opaque") {
        return Err("an unparsed data literal or range");
    }
    if let Some(literal) = rest.strip_prefix("val__") {
        return literal_status(literal);
    }
    if let Some(text) = rest.strip_prefix("c__") {
        return match Parser::new(text).parse() {
            Ok(node) => node_status(&node),
            Err(_) => Err("a data range of unknown shape"),
        };
    }
    atomic_status(rest)
}

/// An atomic range of the decided map (not an enumeration).
fn ordered_or_named(range: &DRange) -> bool {
    matches!(range, DRange::Named(_) | DRange::Num(_) | DRange::Float(_))
}

/// Expand `names` (and `groups`) as described in the module comment.
pub(crate) fn expand(names: &BTreeSet<String>, groups: Option<&[BTreeSet<String>]>) -> DataVocabulary {
    let mut out = DataVocabulary::default();
    // 1. Boolean structure, closed transitively over operands.
    let mut all: BTreeSet<String> = names.clone();
    let mut pending: Vec<String> = names.iter().cloned().collect();
    let mut links: Vec<(String, Vec<String>)> = Vec::new();
    let mut intersections: Vec<(String, Vec<String>)> = Vec::new();
    while let Some(name) = pending.pop() {
        let Some(found) = structure(&name) else { continue };
        let operands = match &found {
            Structure::Union(members) | Structure::Intersection(members) => members.clone(),
            Structure::Complement(operand) => vec![operand.clone()],
        };
        for operand in &operands {
            if all.insert(operand.clone()) {
                pending.push(operand.clone());
            }
        }
        match found {
            Structure::Union(members) => out.unions.push((name.clone(), members)),
            Structure::Intersection(members) => intersections.push((name.clone(), members)),
            Structure::Complement(operand) => out.complements.push((name.clone(), operand)),
        }
        out.boolean.insert(name.clone());
        links.push((name, operands));
    }
    out.unions.sort();
    out.complements.sort();
    intersections.sort();
    let mut expanded_groups: Option<Vec<BTreeSet<String>>> = groups.map(|groups| groups.iter().map(|group| {
        let mut group = group.clone();
        loop {
            let before = group.len();
            for (name, operands) in &links {
                if group.contains(name) {
                    group.extend(operands.iter().cloned());
                }
            }
            if group.len() == before {
                break;
            }
        }
        group
    }).collect());
    // Definitional clauses not already emitted by the historical union
    // covers, excluded middles and the oracle's pairwise relations.
    for (union, members) in &out.unions {
        let whole = parsed(union);
        for member in members {
            if matches!(parsed(member), Some(DRange::Top)) {
                out.undecided.push(("rdfs:Literal inside a data union", union.clone()));
            }
            let decided = match (parsed(member), &whole) {
                (Some(m), Some(w)) => range_subsumed(&m, w) == Some(true),
                _ => false,
            };
            if !decided {
                out.extra.push(clause([cx(member)], [cx(union)]));
            }
        }
    }
    for (complement, operand) in &out.complements {
        let operand_range = parsed(operand);
        if matches!(operand_range, Some(DRange::Top)) {
            out.extra.push(clause([cx(complement)], []));
            continue;
        }
        let decided = match (parsed(complement), &operand_range) {
            (Some(c), Some(o)) => range_disjoint(&c, o) == Some(true),
            _ => false,
        };
        if !decided {
            out.extra.push(clause([cx(complement), cx(operand)], []));
        }
    }
    for (intersection, members) in &intersections {
        let mut body = Vec::new();
        for member in members {
            if matches!(parsed(member), Some(DRange::Top)) {
                continue;
            }
            out.extra.push(clause([cx(intersection)], [cx(member)]));
            body.push(cx(member));
        }
        out.extra.push(clause(body, [cx(intersection)]));
    }
    // 3. The decided fragment.
    for name in &all {
        if let Err(reason) = name_status(name) {
            out.undecided.push((reason, name.clone()));
        }
    }
    let atomic: Vec<(String, DRange)> = all.iter()
        .filter_map(|name| parsed(name).filter(ordered_or_named).map(|range| (name.clone(), range)))
        .filter(|(name, _)| !name.starts_with("__dt__val__"))
        .collect();
    for name in all.iter().filter(|name| name.starts_with("__dt__val__")) {
        let Some(super::DtEntry::Value(_, value)) = super::classify_name(name) else { continue };
        if matches!(value, Val::Opaque(_)) {
            continue;
        }
        if let Some((range, _)) = atomic.iter().find(|(range_name, range)|
            !range_name.starts_with("__dt__iri__") && val_in_range(&value, range).is_none()
                && !free_range(range_name))
        {
            out.undecided.push(("a literal with an undecided membership in a data range", format!("{name} in {range}")));
        }
    }
    // 2. Ordered cells, per role group.
    let cell_groups: Vec<BTreeSet<String>> = match &expanded_groups {
        Some(groups) => groups.clone(),
        None => vec![all.clone()],
    };
    let mut seen_cells: BTreeSet<String> = BTreeSet::new();
    let mut added: Vec<(usize, Vec<String>)> = Vec::new();
    for (index, group) in cell_groups.iter().enumerate() {
        let ranges: Vec<(&String, &DRange)> = atomic.iter()
            .filter(|(name, _)| group.contains(name))
            .map(|(name, range)| (name, range))
            .collect();
        let mut group_cells: Vec<String> = Vec::new();
        for partition in [Partition::Numeric, Partition::Float32, Partition::Float64] {
            match partition_cells(partition, &ranges) {
                Ok(None) => {}
                Ok(Some(cells)) => {
                    emit_cells(&cells, &ranges, partition, &mut out, &mut seen_cells);
                    group_cells.extend(cells.into_iter().map(|cell| cell.name));
                }
                Err(reason) => out.undecided.push((reason, format!("role group {index}"))),
            }
        }
        if !group_cells.is_empty() {
            added.push((index, group_cells));
        }
    }
    for (index, cells) in added {
        all.extend(cells.iter().cloned());
        if let Some(groups) = expanded_groups.as_mut() {
            groups[index].extend(cells);
        }
    }
    out.names = all;
    out.groups = expanded_groups;
    out
}

/// A range named by a custom datatype IRI (free) or a datatype outside the map.
fn free_range(name: &str) -> bool {
    let rest = name.strip_prefix("__dt__").unwrap_or(name);
    rest.starts_with("iri__") || outside_map(rest)
}

struct Cell {
    name: String,
    /// A value of the cell. Every atomic range of the cell's partition in
    /// the group contains either every value of the cell or none, so the
    /// representative decides the cell's membership.
    rep: Val,
    /// For a band of rationals or reals without decimals: the kind level,
    /// which decides membership instead of `rep` (`cell_member`).
    level: Option<u8>,
    /// The cell is a single value (its name is a value concept).
    point: bool,
}

fn partition_of(range: &DRange) -> Option<Partition> {
    match range {
        DRange::Named(datatype) => Some(datatype.part),
        DRange::Num(_) => Some(Partition::Numeric),
        DRange::Float(range) => Some(range.part),
        _ => None,
    }
}

fn integral(range: &DRange) -> bool {
    match range {
        DRange::Named(datatype) => datatype.integral,
        DRange::Num(range) => range.integral,
        _ => false,
    }
}

/// The cells of `partition` for the atomic ranges of one group, or `None`
/// when the group needs none: fewer than two ranges of the partition, or (on
/// the decimal tower) only integral ones, which the integral cells of
/// `integral_cell_covers` already decide.
fn partition_cells(partition: Partition, ranges: &[(&String, &DRange)]) -> Result<Option<Vec<Cell>>, &'static str> {
    let members: Vec<&DRange> = ranges.iter().map(|(_, range)| *range)
        .filter(|range| partition_of(range) == Some(partition))
        .collect();
    if members.len() < 2 {
        return Ok(None);
    }
    let cells = match partition {
        Partition::Numeric => {
            if members.iter().all(|range| integral(range)) {
                return Ok(None);
            }
            decimal_cells(&members)?
        }
        _ => ieee_cells(partition, &members)?,
    };
    // Only cells inside some range of the partition are needed.
    let cells: Vec<Cell> = cells.into_iter()
        .filter(|cell| members.iter().any(|range| cell_member(cell, range) == Some(true)))
        .collect();
    if cells.len() > MAX_CELLS {
        return Err("too many data cells in one role group");
    }
    Ok(Some(cells))
}

fn decimal_lexical(value: &Rat) -> Option<String> {
    if value.is_integer() {
        return Some(value.num.to_string());
    }
    // A finite decimal has a denominator 2^a 5^b; scale it to 10^max(a,b).
    let mut den = value.den;
    let (mut twos, mut fives) = (0u32, 0u32);
    while den % 2 == 0 { den /= 2; twos += 1; }
    while den % 5 == 0 { den /= 5; fives += 1; }
    if den != 1 {
        return None;
    }
    let digits = twos.max(fives);
    let scale = 10i128.checked_pow(digits)?;
    let scaled = value.num.checked_mul(scale / value.den)?;
    let negative = scaled < 0;
    let text = scaled.unsigned_abs().to_string();
    let text = if text.len() <= digits as usize {
        format!("{}{}", "0".repeat(digits as usize + 1 - text.len()), text)
    } else {
        text
    };
    let (whole, fraction) = text.split_at(text.len() - digits as usize);
    Some(format!("{}{whole}.{fraction}", if negative { "-" } else { "" }))
}

fn numeric_value_name(value: &Rat) -> Option<String> {
    let lexical = decimal_lexical(value)?;
    Some(if value.is_integer() {
        format!("__dt__val__\"{lexical}\"^^xsd:integer")
    } else {
        format!("__dt__val__\"{lexical}\"^^xsd:decimal")
    })
}

fn rat_half(value: &Rat) -> Option<Rat> {
    Rat::new(value.num, value.den.checked_mul(2)?)
}

fn rat_add(left: &Rat, right: &Rat) -> Option<Rat> {
    Rat::new(left.num.checked_mul(right.den)?.checked_add(right.num.checked_mul(left.den)?)?, left.den.checked_mul(right.den)?)
}

fn rat_sub(left: &Rat, right: &Rat) -> Option<Rat> {
    rat_add(left, &Rat::new(-right.num, right.den)?)
}

/// A finite decimal strictly between `lo` and `hi` (`None` = unbounded)
/// that is not an integer.
fn noninteger_between(lo: Option<&Rat>, hi: Option<&Rat>) -> Option<Rat> {
    let half = Rat::new(1, 2)?;
    let (a, b) = match (lo, hi) {
        (Some(a), Some(b)) => (*a, *b),
        (Some(a), None) => (*a, rat_add(a, &Rat::from_int(2))?),
        (None, Some(b)) => (rat_sub(b, &Rat::from_int(2))?, *b),
        (None, None) => return Some(half),
    };
    // Halve the distance to `a` until the point is not an integer: once the
    // distance is below 1/2 and `a` is an integer the point is not one, and
    // for a non-integer `a` the points approach `a` from above.
    let mut point = rat_midpoint(&a, &b)?;
    for _ in 0..128 {
        if !point.is_integer() {
            return Some(point);
        }
        point = rat_half(&rat_add(&a, &point)?)?;
    }
    None
}

fn any_between(lo: Option<&Rat>, hi: Option<&Rat>) -> Option<Rat> {
    match (lo, hi) {
        (Some(a), Some(b)) => rat_midpoint(a, b),
        (Some(a), None) => rat_add(a, &Rat::from_int(1)),
        (None, Some(b)) => rat_sub(b, &Rat::from_int(1)),
        (None, None) => Some(Rat::from_int(0)),
    }
}

/// Value kinds of the decimal tower, by level: integers, decimals,
/// rationals, reals.
fn kind_level(kind: &str, integral: bool) -> u8 {
    if integral {
        return 0;
    }
    match kind {
        "rational" => 2,
        "real" => 3,
        _ => 1,
    }
}

fn kind_base(level: u8) -> &'static str {
    match level {
        0 => "xsd:integer",
        1 => "xsd:decimal",
        2 => "owl:rational",
        _ => "owl:real",
    }
}

/// Cells of the decimal tower: every endpoint is a point, and every open
/// gap between endpoints is split into bands by the value kinds the group
/// distinguishes (integers, decimals, rationals, reals): the band of the
/// lowest present kind, then each present kind minus the one below it.
/// A band that contains decimals has a decimal representative; a band of
/// rationals that are not decimals or of irrational reals has none, and its
/// membership is decided by kind (`Cell::level`), which is exact because
/// only the unbounded named types `owl:rational` and `owl:real` have those
/// kinds: a facet interval over `owl:rational` or `owl:real` is reported.
fn decimal_cells(members: &[&DRange]) -> Result<Vec<Cell>, &'static str> {
    const REAL: &str = "a facet interval over owl:real or owl:rational next to another decimal-tower range";
    const OVERFLOW: &str = "a decimal-tower endpoint outside the exact arithmetic";
    let mut cuts: Vec<Rat> = Vec::new();
    let mut levels: BTreeSet<u8> = BTreeSet::new();
    for range in members {
        match range {
            DRange::Named(datatype) => {
                levels.insert(kind_level(datatype.kind, datatype.integral));
                cuts.extend(datatype.min.map(Rat::from_int));
                cuts.extend(datatype.max.map(Rat::from_int));
            }
            DRange::Num(range) => {
                if matches!(range.base_kind, "real" | "rational") {
                    return Err(REAL);
                }
                levels.insert(kind_level(range.base_kind, range.integral));
                cuts.extend(range.min.map(|(bound, _)| bound));
                cuts.extend(range.max.map(|(bound, _)| bound));
            }
            _ => {}
        }
    }
    let levels: Vec<u8> = levels.into_iter().collect();
    let mut failed = false;
    cuts.sort_by(|a, b| rat_cmp(a, b).unwrap_or_else(|| { failed = true; std::cmp::Ordering::Equal }));
    if failed {
        return Err(OVERFLOW);
    }
    cuts.dedup();
    let mut cells = Vec::new();
    let gap = |lo: Option<&Rat>, hi: Option<&Rat>, cells: &mut Vec<Cell>| -> Result<(), &'static str> {
        let mut below: Option<u8> = None;
        for &level in &levels {
            if level == 0 {
                let first = match lo { Some(lo) => Some(super::div_floor_rat(lo).and_then(|f| f.checked_add(1)).ok_or(OVERFLOW)?), None => None };
                let last = match hi { Some(hi) => Some(super::div_ceil_rat(hi).and_then(|c| c.checked_sub(1)).ok_or(OVERFLOW)?), None => None };
                if !matches!((first, last), (Some(f), Some(l)) if f > l) {
                    let rep = first.or(last).unwrap_or(0);
                    cells.push(Cell { name: integral_cell_name(first, last), rep: Val::Num(Rat::from_int(rep)),
                        level: None, point: first.is_some() && first == last });
                }
                below = Some(0);
                continue;
            }
            let mut facets = String::new();
            if let Some(lo) = lo {
                facets.push_str(&format!(" xsd:minExclusive \"{}\"^^xsd:decimal", decimal_lexical(lo).ok_or(OVERFLOW)?));
            }
            if let Some(hi) = hi {
                facets.push_str(&format!(" xsd:maxExclusive \"{}\"^^xsd:decimal", decimal_lexical(hi).ok_or(OVERFLOW)?));
            }
            let base = kind_base(level);
            let band = if facets.is_empty() { base.to_string() } else { format!("DatatypeRestriction({base}{facets})") };
            let name = match below {
                None if facets.is_empty() => format!("__dt__{}", datatype_concept_key(base)),
                None => format!("__dt__c__{band}"),
                Some(previous) => format!("__dt__c__DataIntersectionOf({band} DataComplementOf({}))", kind_base(previous)),
            };
            // Decimals lie in the band unless a decimal kind lies below it.
            let (rep, rule) = match below {
                None => (any_between(lo, hi).ok_or(OVERFLOW)?, None),
                Some(0) => (noninteger_between(lo, hi).ok_or(OVERFLOW)?, None),
                Some(_) => (any_between(lo, hi).ok_or(OVERFLOW)?, Some(level)),
            };
            cells.push(Cell { name, rep: Val::Num(rep), level: rule, point: false });
            below = Some(level);
        }
        Ok(())
    };
    let mut previous: Option<Rat> = None;
    for cut in &cuts {
        gap(previous.as_ref(), Some(cut), &mut cells)?;
        cells.push(Cell { name: numeric_value_name(cut).ok_or(OVERFLOW)?, rep: Val::Num(*cut), level: None, point: true });
        previous = Some(*cut);
    }
    gap(previous.as_ref(), None, &mut cells)?;
    Ok(cells)
}

/// Membership of a whole cell in an atomic range (see `Cell`).
fn cell_member(cell: &Cell, range: &DRange) -> Option<bool> {
    match cell.level {
        None => val_in_range(&cell.rep, range),
        Some(level) => match range {
            DRange::Named(datatype) if datatype.part == Partition::Numeric =>
                Some(kind_level(datatype.kind, datatype.integral) >= level),
            DRange::Num(_) => Some(false),
            DRange::Named(_) | DRange::Float(_) => Some(false),
            _ => None,
        },
    }
}

fn ieee_value(part: Partition, bits: u64) -> Val {
    if part == Partition::Float32 { Val::Float32(bits as u32) } else { Val::Float64(bits) }
}

fn ieee_lexical(part: Partition, bits: u64) -> String {
    let datatype = if part == Partition::Float32 { "float" } else { "double" };
    let value = if part == Partition::Float32 { f32::from_bits(bits as u32) as f64 } else { f64::from_bits(bits) };
    let text = if value.is_nan() {
        "NaN".to_string()
    } else if value == f64::INFINITY {
        "INF".to_string()
    } else if value == f64::NEG_INFINITY {
        "-INF".to_string()
    } else if part == Partition::Float32 {
        format!("{:e}", f32::from_bits(bits as u32))
    } else {
        format!("{:e}", f64::from_bits(bits))
    };
    format!("\"{text}\"^^xsd:{datatype}")
}

/// Cells of one IEEE width: the rank segments between range endpoints, with
/// both zeros and `NaN` as points of their own.
fn ieee_cells(part: Partition, members: &[&DRange]) -> Result<Vec<Cell>, &'static str> {
    let intervals: Vec<FloatRange> = members.iter().filter_map(|range| match range {
        DRange::Float(range) => Some(range.clone()),
        DRange::Named(datatype) if datatype.part == part => Some(FloatRange::full(part)),
        _ => None,
    }).collect();
    let full = FloatRange::full(part);
    let sign = FloatRange::sign(part) as u128;
    let (start, end) = (full.lo as u128, full.hi as u128 + 1);
    let mut cuts: Vec<u128> = vec![start, end, sign - 1, sign, sign + 1];
    for range in &intervals {
        if range.lo <= range.hi {
            cuts.push(range.lo as u128);
            cuts.push(range.hi as u128 + 1);
        }
    }
    cuts.retain(|&cut| start <= cut && cut <= end);
    cuts.sort_unstable();
    cuts.dedup();
    let mut cells = Vec::new();
    for window in cuts.windows(2) {
        let (from, to) = (window[0], window[1]);
        let first = FloatRange::unrank(from as u64, part);
        if to - from == 1 {
            cells.push(Cell { name: format!("__dt__val__{}", ieee_lexical(part, first)), rep: ieee_value(part, first), level: None, point: true });
        } else {
            let last = FloatRange::unrank((to - 1) as u64, part);
            let datatype = if part == Partition::Float32 { "xsd:float" } else { "xsd:double" };
            let name = format!("__dt__c__DatatypeRestriction({datatype} xsd:minInclusive {} xsd:maxInclusive {})",
                ieee_lexical(part, first), ieee_lexical(part, last));
            // The name must denote exactly this segment.
            match parsed(&name) {
                Some(DRange::Float(range)) if range.lo as u128 == from && range.hi as u128 == to - 1 && !range.nan => {}
                _ => return Err("an IEEE cell that its facet name does not denote exactly"),
            }
            cells.push(Cell { name, rep: ieee_value(part, first), level: None, point: false });
        }
    }
    if intervals.iter().any(|range| range.nan) {
        let nan = if part == Partition::Float32 { f32::NAN.to_bits() as u64 } else { f64::NAN.to_bits() };
        cells.push(Cell { name: format!("__dt__val__{}", ieee_lexical(part, nan)), rep: ieee_value(part, nan), level: None, point: true });
    }
    Ok(cells)
}

/// Clauses of the cells of one partition in one group: each cell inside or
/// outside every atomic range of the group, each range of the partition
/// covered by its cells, and distinct cells disjoint.
fn emit_cells(
    cells: &[Cell],
    ranges: &[(&String, &DRange)],
    partition: Partition,
    out: &mut DataVocabulary,
    seen: &mut BTreeSet<String>,
) {
    for cell in cells {
        let fresh = seen.insert(cell.name.clone());
        for (name, range) in ranges {
            if **name == cell.name || !fresh && partition_of(range) != Some(partition) {
                continue;
            }
            match cell_member(cell, range) {
                Some(true) => out.extra.push(clause([cx(&cell.name)], [cx(name)])),
                Some(false) => out.extra.push(clause([cx(&cell.name), cx(name)], [])),
                None => {}
            }
        }
    }
    for (name, range) in ranges {
        if partition_of(range) != Some(partition) {
            continue;
        }
        let heads: Vec<&str> = cells.iter()
            .filter(|cell| cell_member(cell, range) == Some(true))
            .map(|cell| cell.name.as_str())
            .collect();
        if heads == [name.as_str()] {
            continue;
        }
        out.extra.push(clause([cx(name)], heads.iter().map(|head| cx(head)).collect::<Vec<_>>()));
    }
    for (index, left) in cells.iter().enumerate() {
        for right in &cells[index + 1..] {
            if left.point && right.point {
                continue; // value concepts: separated by the value relations
            }
            out.extra.push(clause([cx(&left.name), cx(&right.name)], []));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn set(list: &[&str]) -> BTreeSet<String> {
        list.iter().map(|name| name.to_string()).collect()
    }

    #[test]
    fn decimal_lexical_forms() {
        assert_eq!(decimal_lexical(&Rat::new(3, 2).unwrap()).as_deref(), Some("1.5"));
        assert_eq!(decimal_lexical(&Rat::new(-1, 8).unwrap()).as_deref(), Some("-0.125"));
        assert_eq!(decimal_lexical(&Rat::from_int(7)).as_deref(), Some("7"));
        assert_eq!(decimal_lexical(&Rat::new(1, 3).unwrap()), None);
    }

    #[test]
    fn intersection_with_complement_has_structure_and_cells() {
        let name = "__dt__c__DataIntersectionOf(DatatypeRestriction(xsd:integer xsd:minInclusive \"1\"^^xsd:integer xsd:maxInclusive \"9\"^^xsd:integer) DataComplementOf(DatatypeRestriction(xsd:integer xsd:minInclusive \"1\"^^xsd:integer xsd:maxInclusive \"8\"^^xsd:integer)))";
        let vocabulary = expand(&set(&[name]), None);
        assert!(vocabulary.undecided.is_empty(), "{:?}", vocabulary.undecided);
        assert_eq!(vocabulary.complements.len(), 1);
        assert!(vocabulary.boolean.contains(name));
        assert!(vocabulary.names.len() >= 4, "{:?}", vocabulary.names);
    }

    #[test]
    fn helly_cells_split_integers_from_decimals() {
        let names = set(&["__dt__integer",
            "__dt__c__DatatypeRestriction(xsd:decimal xsd:minInclusive \"1.2\"^^xsd:decimal xsd:maxInclusive \"3\"^^xsd:decimal)",
            "__dt__c__DatatypeRestriction(xsd:decimal xsd:minInclusive \"0\"^^xsd:decimal xsd:maxInclusive \"1.8\"^^xsd:decimal)"]);
        let vocabulary = expand(&names, None);
        assert!(vocabulary.undecided.is_empty(), "{:?}", vocabulary.undecided);
        assert!(vocabulary.names.contains("__dt__c__DataIntersectionOf(DatatypeRestriction(xsd:decimal xsd:minExclusive \"1.2\"^^xsd:decimal xsd:maxExclusive \"1.8\"^^xsd:decimal) DataComplementOf(xsd:integer))"),
            "{:?}", vocabulary.names);
    }

    #[test]
    fn ieee_cells_isolate_shared_endpoints() {
        let names = set(&[
            "__dt__c__DatatypeRestriction(xsd:float xsd:minInclusive \"1.0\"^^xsd:float xsd:maxInclusive \"2.0\"^^xsd:float)",
            "__dt__c__DatatypeRestriction(xsd:float xsd:minInclusive \"2.0\"^^xsd:float xsd:maxInclusive \"3.0\"^^xsd:float)"]);
        let vocabulary = expand(&names, None);
        assert!(vocabulary.undecided.is_empty(), "{:?}", vocabulary.undecided);
        assert!(vocabulary.names.contains("__dt__val__\"2e0\"^^xsd:float"), "{:?}", vocabulary.names);
    }

    #[test]
    fn undecided_facets_and_literals_are_reported() {
        let names = set(&["__dt__c__DatatypeRestriction(xsd:string xsd:pattern \"x.*\")",
            "__dt__c__DatatypeRestriction(xsd:dateTime xsd:minInclusive \"2020-01-01T00:00:00Z\"^^xsd:dateTime)",
            "__dt__val__\"maybe\"^^xsd:boolean",
            "__dt__c__DatatypeRestriction(ex:custom ex:facet \"1\")",
            "__dt__val__\"2020-01-01\"^^xsd:date"]);
        let vocabulary = expand(&names, None);
        let reported: BTreeSet<&str> = vocabulary.undecided.iter().map(|(_, name)| name.as_str()).collect();
        assert_eq!(reported.len(), 3, "{:?}", vocabulary.undecided);
    }
}
