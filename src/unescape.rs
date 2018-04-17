// Stolen and modified from https://github.com/saghm/unescape-rs (MIT licensed)

use std::collections::VecDeque;

use std::char;

macro_rules! try_option {
    ($o:expr) => {
        match $o {
            Some(s) => s,
            None => return None,
        }
    }
}

// Takes in a string with backslash escapes written out with literal backslash characters and
// converts it to a string with the proper escaped characters.
pub fn unescape(s: &str) -> Option<String> {
    let mut queue: VecDeque<_> = String::from(s).chars().collect();
    let mut s = String::new();

    while let Some(c) = queue.pop_front() {
        if c != '\\' {
            s.push(c);
            continue;
        }

        match queue.pop_front() {
            Some('n') => s.push('\n'),
            Some('0') => s.push('\0'),
            Some('t') => s.push('\t'),
            Some('\"') => s.push('\"'),
            Some('\\') => s.push('\\'),
            Some('u') => s.push(try_option!(unescape_unicode(&mut queue))),
            _ => return None,
        };
    }

    Some(s)
}

fn unescape_unicode(queue: &mut VecDeque<char>) -> Option<char> {
    let mut s = String::new();

    for _ in 0..4 {
        s.push(try_option!(queue.pop_front()));
    }

    let u = try_option!(u32::from_str_radix(&s, 16).ok());
    char::from_u32(u)
}
