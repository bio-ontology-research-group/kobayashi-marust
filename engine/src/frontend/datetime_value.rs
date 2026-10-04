//! Exact XML Schema dateTime identity for supported Gregorian lexical forms.
//! Keep the timezone component: equal instants need not be identical OWL values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct DateTimeValue {
    pub(super) day: i128,
    pub(super) second: u32,
    pub(super) fraction: String,
    pub(super) offset: Option<i16>,
}

pub(super) fn parse(text: &str, require_timezone: bool) -> Option<DateTimeValue> {
    let text = text.trim_matches([' ', '\t', '\r', '\n']);
    if !text.is_ascii() { return None; }
    let (date, time) = text.split_once('T')?;
    let mut fields = date.rsplitn(3, '-');
    let day_text = fields.next()?;
    let month_text = fields.next()?;
    let year_text = fields.next()?;
    let digits = year_text.strip_prefix('-').unwrap_or(year_text);
    if digits.len() < 4 || !digits.bytes().all(|b| b.is_ascii_digit())
        || (digits.len() > 4 && digits.starts_with('0')) { return None; }
    let year: i64 = year_text.parse().ok()?;
    if year == 0 && year_text.starts_with('-') { return None; }
    let two = |s: &str| -> Option<u32> {
        if s.len() != 2 || !s.bytes().all(|b| b.is_ascii_digit()) { return None; }
        s.parse().ok()
    };
    let month = two(month_text)?;
    let day = two(day_text)?;
    let leap = year % 4 == 0 && (year % 100 != 0 || year % 400 == 0);
    let days = match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 => if leap { 29 } else { 28 },
        _ => return None,
    };
    if day == 0 || day > days { return None; }
    let (clock, offset) = if let Some(clock) = time.strip_suffix('Z') {
        (clock, Some(0))
    } else if time.len() >= 6 && matches!(time.as_bytes()[time.len()-6], b'+' | b'-') {
        let zone = &time[time.len()-6..];
        if zone.as_bytes()[3] != b':' { return None; }
        let hour = two(&zone[1..3])?;
        let minute = two(&zone[4..])?;
        if hour > 14 || minute > 59 || (hour == 14 && minute != 0) { return None; }
        let value = (hour * 60 + minute) as i16;
        (&time[..time.len()-6], Some(if zone.starts_with('-') { -value } else { value }))
    } else { (time, None) };
    if require_timezone && offset.is_none() { return None; }
    let (clock, fraction) = clock.split_once('.').map_or((clock, ""), |(a,b)| (a,b));
    if clock.len() != 8 || clock.as_bytes()[2] != b':' || clock.as_bytes()[5] != b':' {
        return None;
    }
    if (!fraction.is_empty() && !fraction.bytes().all(|b| b.is_ascii_digit()))
        || time.contains('.') && fraction.is_empty() { return None; }
    let hour = two(&clock[..2])?;
    let minute = two(&clock[3..5])?;
    let second = two(&clock[6..])?;
    let fraction = fraction.trim_end_matches('0').to_string();
    if hour > 24 || minute > 59 || second > 59
        || (hour == 24 && (minute != 0 || second != 0 || !fraction.is_empty())) { return None; }
    // Gregorian civil-day numbering with Euclidean eras, including BCE years.
    let adjusted = i128::from(year) - i128::from(month <= 2);
    let era = adjusted.div_euclid(400);
    let within = adjusted - era * 400;
    let shifted = i128::from(month) + if month > 2 { -3 } else { 9 };
    let ordinal = (153 * shifted + 2) / 5 + i128::from(day) - 1;
    let mut day = era * 146097 + within * 365 + within / 4 - within / 100 + ordinal;
    if hour == 24 { day += 1; }
    Some(DateTimeValue { day, second: (hour % 24) * 3600 + minute * 60 + second, fraction, offset })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn identity_normalizes_clock_but_retains_timezone() {
        assert_eq!(parse("2000-02-29T24:00:00.000Z", false), parse("2000-03-01T00:00:00+00:00", false));
        let a = parse("1956-06-25T04:00:00-05:00", false).unwrap();
        let b = parse("1956-06-25T10:00:00+01:00", false).unwrap();
        assert_ne!(a, b);
        assert_eq!(a.day * 86400 + i128::from(a.second) - i128::from(a.offset.unwrap()) * 60,
            b.day * 86400 + i128::from(b.second) - i128::from(b.offset.unwrap()) * 60);
        assert_ne!(parse("2000-01-01T00:00:00", false), parse("2000-01-01T00:00:00Z", false));
    }
    #[test]
    fn lexical_limits_and_leap_days_are_checked() {
        for text in ["1900-02-29T00:00:00", "2001-04-31T00:00:00", "2000-01-01T24:00:01", "2000-01-01T00:00:00+14:01", "2000-01-01T00:00:00."] {
            assert!(parse(text, false).is_none(), "{text}");
        }
        assert!(parse("2000-02-29T00:00:00", false).is_some());
        assert!(parse("2000-02-29T00:00:00", true).is_none());
        assert!(parse("2000-02-29T00:00:00Z", true).is_some());
    }
}
