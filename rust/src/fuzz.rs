//! P3 JSON-line fuzz oracle adapter. Parsing is outside the numerical kernel.
use crate::{Message, coefficient, evaluate};
use serde_json::{Value, json};

// Match P3's integer spelling before serde_json erases number-token details.
// Strings may contain these characters; the JSON parser checks all other syntax.
fn integer_tokens_only(line: &str) -> bool {
    let mut quoted = false;
    let mut escaped = false;
    let mut previous = b' ';
    for byte in line.bytes() {
        if quoted {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                quoted = false;
            }
        } else if byte == b'"' {
            quoted = true;
        } else if byte == b'.'
            || (matches!(byte, b'e' | b'E') && previous.is_ascii_digit())
            || (byte == b'0' && previous == b'-')
        {
            return false;
        }
        previous = byte;
    }
    true
}

fn parse_message(j: &Value) -> Option<Message> {
    let axes = j.get("coefficients")?.as_array()?;
    if axes.len() != 3 {
        return None;
    }
    let parse_axis = |a: &Value| -> Option<Vec<i32>> {
        a.as_array()?
            .iter()
            .map(|q| i32::try_from(q.as_i64()?).ok())
            .collect()
    };
    Some(Message {
        day_offset: u16::try_from(j.get("day_offset")?.as_u64()?).ok()?,
        second_of_day: u32::try_from(j.get("second_of_day")?.as_u64()?).ok()?,
        validity_code: u8::try_from(j.get("validity_code")?.as_u64()?).ok()?,
        coefficients: [
            parse_axis(&axes[0])?,
            parse_axis(&axes[1])?,
            parse_axis(&axes[2])?,
        ],
    })
}

fn execute(j: &Value) -> Option<Value> {
    if j.get("version")?.as_u64()? != 3 {
        return None;
    }
    match j.get("operation")?.as_str()? {
        "coefficient" => {
            let q = i32::try_from(j.get("coefficient")?.as_i64()?).ok()?;
            Some(json!({"ok": true, "result": coefficient(q).to_bits().to_string()}))
        }
        "evaluate" => {
            let m = parse_message(j.get("message")?)?;
            let time = j.get("time")?.as_u64()?;
            Some(match evaluate(&m, time) {
                Ok(p) => json!({"ok": true, "result": p.map(|v| v.to_bits().to_string())}),
                Err(e) => json!({"ok": false, "error": e.code()}),
            })
        }
        _ => None,
    }
}

pub fn respond(line: &str) -> Value {
    if !integer_tokens_only(line) {
        return json!({"ok": false, "error": "invalidProtocol"});
    }
    serde_json::from_str::<Value>(line)
        .ok()
        .and_then(|j| execute(&j))
        .unwrap_or_else(|| json!({"ok": false, "error": "invalidProtocol"}))
}
