//! The OWL 2 `xsd:dateTime` value space with the XSD 1.1 order, for facet
//! intervals and ordered cells (docs/DATATYPES.md, "dateTime bounds as
//! ordered cells").
//!
//! A `dateTime` value is either *timezoned* (a point on the time line with a
//! timezone offset of -14:00 to +14:00; identity keeps the offset, so one
//! instant carries 1681 distinct values) or *untimezoned* (a local time).
//! XSD 1.1 (part 2, 3.3.7 and D.2.1) orders two timezoned values by their
//! instants and two untimezoned values by their local times. A timezoned
//! value `P` and an untimezoned `Q` compare only when they are more than
//! fourteen hours apart: `P < Q` iff `P < Q - 14h` and `P > Q` iff
//! `P > Q + 14h` (reading `Q`'s local time as UTC); they are never equal.
//!
//! The four bound facets denote `{x | x ≥ b}` and the like under this
//! partial order. Every such set, and every intersection of them, is a pair
//! of intervals: one over the instants of the timezoned values (`zoned`) and
//! one over the local times of the untimezoned values (`local`). A bound `b`
//! with a timezone restricts `zoned` by `b` itself and `local` strictly by
//! `b ± 14h`; an untimezoned bound restricts `local` by `b` and `zoned`
//! strictly by `b ± 14h`. Both axes are dense (seconds carry arbitrary
//! decimal fractions), so interval inclusion and disjointness decide the
//! value sets exactly.
use crate::frontend::datetime_value::{self, DateTimeValue};

/// Fourteen hours in seconds: the largest timezone offset.
pub(crate) const ZONE_SPREAD: i128 = 14 * 3600;
/// Distinct timezoned values at one instant: the offsets -840 to +840 minutes.
pub(crate) const VALUES_PER_INSTANT: u128 = 1681;

/// A point of one axis: whole seconds since the epoch of `datetime_value`
/// (`0000-03-01T00:00:00`) and the decimal digits of the fraction, without
/// trailing zeros. The derived order is the numeric order: the seconds
/// first, then the digit strings lexicographically, which orders fractions
/// in `[0, 1)` correctly when neither has trailing zeros.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct TimePoint {
    pub(crate) secs: i128,
    pub(crate) frac: String,
}

impl TimePoint {
    fn shift(&self, by: i128) -> Option<TimePoint> {
        Some(TimePoint { secs: self.secs.checked_add(by)?, frac: self.frac.clone() })
    }
}

/// The axis and the position of a value: `(true, instant)` for a timezoned
/// value, `(false, local time)` for an untimezoned one.
pub(crate) fn timeline(value: &DateTimeValue) -> Option<(bool, TimePoint)> {
    let local = value.day.checked_mul(86400)?.checked_add(i128::from(value.second))?;
    Some(match value.offset {
        Some(minutes) => (true, TimePoint { secs: local.checked_sub(i128::from(minutes) * 60)?, frac: value.fraction.clone() }),
        None => (false, TimePoint { secs: local, frac: value.fraction.clone() }),
    })
}

/// An interval of one axis; `present = false` is the empty axis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Axis {
    pub(crate) present: bool,
    pub(crate) min: Option<(TimePoint, bool)>,
    pub(crate) max: Option<(TimePoint, bool)>,
}

impl Axis {
    pub(crate) fn full() -> Self { Axis { present: true, min: None, max: None } }
    pub(crate) fn none() -> Self { Axis { present: false, min: None, max: None } }

    pub(crate) fn is_empty(&self) -> bool {
        !self.present || match (&self.min, &self.max) {
            (Some((lo, lo_in)), Some((hi, hi_in))) => lo > hi || (lo == hi && !(*lo_in && *hi_in)),
            _ => false,
        }
    }

    /// The single point of a closed degenerate interval.
    pub(crate) fn point(&self) -> Option<&TimePoint> {
        match (&self.min, &self.max) {
            (Some((lo, true)), Some((hi, true))) if self.present && lo == hi => Some(lo),
            _ => None,
        }
    }

    pub(crate) fn contains(&self, p: &TimePoint) -> bool {
        self.present
            && self.min.as_ref().is_none_or(|(lo, inc)| if *inc { lo <= p } else { lo < p })
            && self.max.as_ref().is_none_or(|(hi, inc)| if *inc { p <= hi } else { p < hi })
    }

    /// Keep the tighter lower bound; at equal points the exclusive one.
    fn tighten_min(&mut self, bound: (TimePoint, bool)) {
        let tighter = match &self.min {
            None => true,
            Some((cur, inc)) => *cur < bound.0 || (*cur == bound.0 && *inc && !bound.1),
        };
        if tighter { self.min = Some(bound); }
    }

    fn tighten_max(&mut self, bound: (TimePoint, bool)) {
        let tighter = match &self.max {
            None => true,
            Some((cur, inc)) => bound.0 < *cur || (*cur == bound.0 && *inc && !bound.1),
        };
        if tighter { self.max = Some(bound); }
    }

    pub(crate) fn intersect(&self, other: &Axis) -> Axis {
        let mut out = Axis { present: self.present && other.present, min: self.min.clone(), max: self.max.clone() };
        if let Some(bound) = &other.min { out.tighten_min(bound.clone()); }
        if let Some(bound) = &other.max { out.tighten_max(bound.clone()); }
        out
    }

    /// `self ⊆ other` on a dense axis.
    pub(crate) fn subset(&self, other: &Axis) -> bool {
        if self.is_empty() {
            return true;
        }
        if other.is_empty() {
            return false;
        }
        let lower = match (&other.min, &self.min) {
            (None, _) => true,
            (Some(_), None) => false,
            (Some((o, o_in)), Some((s, s_in))) => s > o || (s == o && (*o_in || !*s_in)),
        };
        let upper = match (&other.max, &self.max) {
            (None, _) => true,
            (Some(_), None) => false,
            (Some((o, o_in)), Some((s, s_in))) => s < o || (s == o && (*o_in || !*s_in)),
        };
        lower && upper
    }

    /// Number of values: 0, `per_point` for a point, otherwise infinite.
    fn size(&self, per_point: u128) -> u128 {
        if self.is_empty() { 0 } else if self.point().is_some() { per_point } else { u128::MAX }
    }
}

/// A `dateTime` facet interval (or `xsd:dateTime`, `xsd:dateTimeStamp`, and
/// their intersections with `DataComplementOf(xsd:dateTimeStamp)`) as its two
/// axes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TimeRange {
    pub(crate) zoned: Axis,
    pub(crate) local: Axis,
}

impl TimeRange {
    pub(crate) fn date_time() -> Self { TimeRange { zoned: Axis::full(), local: Axis::full() } }
    pub(crate) fn stamp() -> Self { TimeRange { zoned: Axis::full(), local: Axis::none() } }
    pub(crate) fn untimezoned() -> Self { TimeRange { zoned: Axis::none(), local: Axis::full() } }

    /// Apply one bound facet (XSD 1.1 order, see the module comment).
    pub(crate) fn restrict(&mut self, facet: &str, bound: &DateTimeValue) -> Option<()> {
        let (zoned, p) = timeline(bound)?;
        let (same, other) = if zoned { (&mut self.zoned, &mut self.local) } else { (&mut self.local, &mut self.zoned) };
        // On the other axis the bound moves by fourteen hours and is strict.
        match facet {
            "minInclusive" => { same.tighten_min((p.clone(), true)); other.tighten_min((p.shift(ZONE_SPREAD)?, false)); }
            "minExclusive" => { same.tighten_min((p.clone(), false)); other.tighten_min((p.shift(ZONE_SPREAD)?, false)); }
            "maxInclusive" => { same.tighten_max((p.clone(), true)); other.tighten_max((p.shift(-ZONE_SPREAD)?, false)); }
            "maxExclusive" => { same.tighten_max((p.clone(), false)); other.tighten_max((p.shift(-ZONE_SPREAD)?, false)); }
            _ => return None,
        }
        Some(())
    }

    pub(crate) fn intersect(&self, other: &TimeRange) -> TimeRange {
        TimeRange { zoned: self.zoned.intersect(&other.zoned), local: self.local.intersect(&other.local) }
    }

    pub(crate) fn contains(&self, value: &DateTimeValue) -> Option<bool> {
        let (zoned, p) = timeline(value)?;
        Some(if zoned { self.zoned.contains(&p) } else { self.local.contains(&p) })
    }

    pub(crate) fn is_empty(&self) -> bool { self.zoned.is_empty() && self.local.is_empty() }

    pub(crate) fn subset(&self, other: &TimeRange) -> bool {
        self.zoned.subset(&other.zoned) && self.local.subset(&other.local)
    }

    pub(crate) fn disjoint(&self, other: &TimeRange) -> bool { self.intersect(other).is_empty() }

    /// Number of values (`u128::MAX` = infinite).
    pub(crate) fn size(&self) -> u128 {
        let zoned = self.zoned.size(VALUES_PER_INSTANT);
        let local = self.local.size(1);
        if zoned == u128::MAX || local == u128::MAX { u128::MAX } else { zoned + local }
    }

    /// The literal of a range that is a single untimezoned value.
    pub(crate) fn single_value(&self) -> Option<String> {
        if !self.zoned.is_empty() {
            return None;
        }
        self.local.point().and_then(|p| lexical(p, false))
    }
}

/// Lexical form of an axis point: `zoned` adds `Z` (the instant read in UTC).
/// `None` when the point leaves the years the parser accepts.
pub(crate) fn lexical(p: &TimePoint, zoned: bool) -> Option<String> {
    let day = p.secs.div_euclid(86400);
    let second = p.secs.rem_euclid(86400);
    // Inverse of the civil-day numbering of `datetime_value::parse` (days
    // since 0000-03-01 in 400-year eras).
    let era = day.div_euclid(146097);
    let doe = day - era * 146097;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = yoe + era * 400 + i128::from(m <= 2);
    let year_text = if year < 0 { format!("-{:04}", -year) } else { format!("{year:04}") };
    let fraction = if p.frac.is_empty() { String::new() } else { format!(".{}", p.frac) };
    let text = format!("{year_text}-{m:02}-{d:02}T{:02}:{:02}:{:02}{fraction}{}",
        second / 3600, second / 60 % 60, second % 60, if zoned { "Z" } else { "" });
    // The text must parse back to the same point.
    let value = datetime_value::parse(&text, false)?;
    (timeline(&value)? == (zoned, p.clone())).then_some(text)
}

/// A digit string strictly between the fractions `0.lo` and `0.hi`
/// (`hi = None` is `1`), without trailing zeros; `lo < hi`.
fn fraction_between(lo: &str, hi: Option<&str>) -> String {
    match hi {
        Some(hi) if hi.starts_with(lo) => {
            // `hi = lo ++ rest` with `rest` nonzero: go below its first
            // nonzero digit.
            let rest = &hi[lo.len()..];
            let zeros = rest.bytes().take_while(|b| *b == b'0').count();
            format!("{lo}{}5", "0".repeat(zeros + 1))
        }
        _ => format!("{lo}5"),
    }
}

/// A point strictly between `lo` and `hi` (`None` = unbounded); `lo < hi`.
pub(crate) fn point_between(lo: Option<&TimePoint>, hi: Option<&TimePoint>) -> Option<TimePoint> {
    match (lo, hi) {
        (None, None) => Some(TimePoint { secs: 0, frac: String::new() }),
        (Some(a), None) => Some(TimePoint { secs: a.secs.checked_add(1)?, frac: String::new() }),
        (None, Some(b)) => Some(TimePoint { secs: b.secs.checked_sub(1)?, frac: String::new() }),
        (Some(a), Some(b)) => {
            let whole = TimePoint { secs: a.secs.checked_add(1)?, frac: String::new() };
            if whole < *b {
                return Some(whole);
            }
            // `b` lies in `(a.secs, a.secs + 1]`.
            let hi = if b.secs == a.secs { Some(b.frac.as_str()) } else { None };
            let point = TimePoint { secs: a.secs, frac: fraction_between(&a.frac, hi) };
            (a < &point && &point < b).then_some(point)
        }
    }
}

/// A value at an axis point (offset `+00:00` on the zoned axis).
pub(crate) fn value_at(p: &TimePoint, zoned: bool) -> DateTimeValue {
    DateTimeValue {
        day: p.secs.div_euclid(86400),
        second: p.secs.rem_euclid(86400) as u32,
        fraction: p.frac.clone(),
        offset: zoned.then_some(0),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(text: &str) -> DateTimeValue { datetime_value::parse(text, false).unwrap() }

    fn range(facets: &[(&str, &str)]) -> TimeRange {
        let mut r = TimeRange::date_time();
        for (facet, bound) in facets { r.restrict(facet, &v(bound)).unwrap(); }
        r
    }

    #[test]
    fn lexical_round_trips() {
        for text in ["2004-12-27T06:00:00", "0000-01-01T00:00:00", "-0044-03-15T12:30:00.25", "1999-12-31T23:59:59.999",
            "2000-02-29T00:00:00", "123456-07-08T09:10:11"] {
            let (zoned, p) = timeline(&v(text)).unwrap();
            assert_eq!(lexical(&p, zoned).as_deref(), Some(text));
        }
        let (zoned, p) = timeline(&v("2000-01-01T05:00:00+05:00")).unwrap();
        assert!(zoned);
        assert_eq!(lexical(&p, true).as_deref(), Some("2000-01-01T00:00:00Z"));
    }

    #[test]
    fn fourteen_hour_rule() {
        // An untimezoned lower bound: timezoned values count only beyond 14 hours.
        let r = range(&[("minExclusive", "2004-12-27T06:00:00")]);
        assert_eq!(r.contains(&v("2004-12-27T07:45:00")), Some(true));
        assert_eq!(r.contains(&v("2004-12-27T06:00:00")), Some(false));
        assert_eq!(r.contains(&v("2004-12-27T20:00:00Z")), Some(false));
        assert_eq!(r.contains(&v("2004-12-27T20:00:00.001Z")), Some(true));
        assert_eq!(r.contains(&v("2004-12-28T10:00:01+14:00")), Some(true));
        // A timezoned upper bound: untimezoned values below 14 hours earlier.
        let r = range(&[("maxInclusive", "2020-01-01T00:00:00Z")]);
        assert_eq!(r.contains(&v("2020-01-01T00:00:00+01:00")), Some(true));
        assert_eq!(r.contains(&v("2019-12-31T10:00:00")), Some(false));
        assert_eq!(r.contains(&v("2019-12-31T09:59:59")), Some(true));
        // `[t, t]` with a timezone holds every offset at that instant and no
        // untimezoned value.
        let point = range(&[("minInclusive", "2020-01-01T00:00:00Z"), ("maxInclusive", "2020-01-01T00:00:00Z")]);
        assert_eq!(point.size(), VALUES_PER_INSTANT);
        assert!(point.local.is_empty());
        assert_eq!(point.contains(&v("2020-01-01T05:30:00+05:30")), Some(true));
        // Crossed bounds are empty.
        assert!(range(&[("minInclusive", "2020-01-02T00:00:00"), ("maxInclusive", "2020-01-01T00:00:00")]).is_empty());
        let untimezoned_point = range(&[("minInclusive", "2020-01-01T00:00:00"), ("maxInclusive", "2020-01-01T00:00:00")]);
        assert_eq!(untimezoned_point.size(), 1);
        assert_eq!(untimezoned_point.single_value().as_deref(), Some("2020-01-01T00:00:00"));
    }

    #[test]
    fn points_between_are_strict() {
        let p = |secs, frac: &str| TimePoint { secs, frac: frac.to_string() };
        for (a, b) in [(p(0, ""), p(1, "")), (p(0, "5"), p(0, "51")), (p(0, "5"), p(0, "5001")), (p(0, "999"), p(1, "")),
            (p(-3, "25"), p(7, ""))] {
            let m = point_between(Some(&a), Some(&b)).unwrap();
            assert!(a < m && m < b, "{a:?} {m:?} {b:?}");
            assert!(!m.frac.ends_with('0'));
        }
    }
}
