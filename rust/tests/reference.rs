use ephemeris_reference::fuzz::respond;
use ephemeris_reference::{
    Message, ReceiverError, WIDTHS, coefficient, duration_ticks, evaluate, start_tick,
};
use serde_json::json;

#[test]
fn every_field_boundary() {
    let mut m = Message {
        day_offset: 16383,
        second_of_day: 86399,
        validity_code: 7,
        coefficients: std::array::from_fn(|_| WIDTHS.iter().map(|w| -(1i32 << (w - 1))).collect()),
    };
    assert!(evaluate(&m, start_tick(&m)).is_ok());
    for axis in 0..3 {
        for (i, width) in WIDTHS.iter().enumerate() {
            m.coefficients[axis][i] = 1i32 << (width - 1);
            assert_eq!(
                evaluate(&m, start_tick(&m)),
                Err(ReceiverError::CoefficientOutOfRange)
            );
            m.coefficients[axis][i] -= 1;
            assert!(evaluate(&m, start_tick(&m)).is_ok());
        }
    }
}

#[test]
fn protocol_rejects_invalid_version_and_carrier_overflow() {
    for request in [
        json!({"version": 2, "operation": "evaluate"}),
        json!({"version": 3, "operation": "coefficient", "coefficient": 2147483648i64}),
        json!({"version": 3, "operation": "coefficient", "coefficient": -2147483649i64}),
        json!({"version": 3, "operation": "coefficient", "coefficient": true}),
    ] {
        assert_eq!(
            respond(&request.to_string()),
            json!({"ok": false, "error": "invalidProtocol"})
        );
    }
    assert_eq!(
        respond("{"),
        json!({"ok": false, "error": "invalidProtocol"})
    );
}

fn fixture() -> Message {
    let mut m = Message {
        day_offset: 0,
        second_of_day: 43200,
        validity_code: 2,
        coefficients: std::array::from_fn(|_| vec![0; 11]),
    };
    m.coefficients[0][0] = 3200;
    m.coefficients[0][1] = 640;
    m
}
#[test]
fn line_and_inclusive_endpoints() {
    let m = fixture();
    let start = start_tick(&m);
    let duration = duration_ticks(&m);
    for (offset, x) in [(0, 80.0), (duration / 2, 100.0), (duration, 120.0)] {
        assert_eq!(evaluate(&m, start + offset), Ok([x, 0.0, 0.0]));
    }
    assert_eq!(evaluate(&m, start - 1), Err(ReceiverError::OutsideValidity));
    assert_eq!(
        evaluate(&m, start + duration + 1),
        Err(ReceiverError::OutsideValidity)
    );
}
#[test]
fn precedence_and_shape() {
    let mut m = fixture();
    m.coefficients[0].clear();
    m.day_offset = u16::MAX;
    assert_eq!(evaluate(&m, 0), Err(ReceiverError::InvalidDayOffset));
    m.day_offset = 0;
    assert_eq!(
        evaluate(&m, 0),
        Err(ReceiverError::CoefficientCountMismatch)
    );
}
#[test]
fn conversion_extremes() {
    for q in [i32::MIN, -1, 0, 1, i32::MAX] {
        assert_eq!(coefficient(q).to_bits(), (f64::from(q) / 32.0).to_bits());
    }
}
