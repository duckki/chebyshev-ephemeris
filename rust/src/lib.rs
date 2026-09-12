//! Bounded binary64 receiver corresponding to Lean Implementation.Float.
//! Inputs describe a trajectory segment; evaluate returns XYZ meters at a query
//! tick. All arithmetic uses f64 and bounded integers, with no rational certificates.

pub mod fuzz;
pub const WIDTHS: [u32; 11] = [30, 28, 25, 21, 19, 17, 14, 12, 9, 7, 5];
pub const EPOCH_ORIGIN_TICK: u64 = 212630443200000000;

#[derive(Clone, Debug)]
pub struct Message {
    pub day_offset: u16,
    pub second_of_day: u32,
    pub validity_code: u8,
    // Variable lengths permit the same malformed-shape rejection as Lean.Array.
    // Validation precedes all indexing; working storage is always [f64; 11].
    pub coefficients: [Vec<i32>; 3],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReceiverError {
    InvalidDayOffset,
    InvalidSecondOfDay,
    InvalidValidityCode,
    CoefficientCountMismatch,
    CoefficientOutOfRange,
    OutsideValidity,
    NonfiniteComputation,
}

impl ReceiverError {
    pub fn code(self) -> &'static str {
        match self {
            Self::InvalidDayOffset => "invalidDayOffset",
            Self::InvalidSecondOfDay => "invalidSecondOfDay",
            Self::InvalidValidityCode => "invalidValidityCode",
            Self::CoefficientCountMismatch => "coefficientCountMismatch",
            Self::CoefficientOutOfRange => "coefficientOutOfRange",
            Self::OutsideValidity => "outsideValidity",
            Self::NonfiniteComputation => "nonfiniteComputation",
        }
    }
}

pub fn start_tick(m: &Message) -> u64 {
    // Even the full u16/u32 carriers keep this sum below 2^64.
    EPOCH_ORIGIN_TICK + u64::from(m.day_offset) * 86400000000 + u64::from(m.second_of_day) * 1000000
}

pub fn duration_ticks(m: &Message) -> u64 {
    u64::from(m.validity_code) * 1800000000
}

pub fn validate_query(m: &Message, time: u64) -> Result<(), ReceiverError> {
    use ReceiverError::*;
    if m.day_offset >= 16384 {
        return Err(InvalidDayOffset);
    }
    if m.second_of_day >= 86400 {
        return Err(InvalidSecondOfDay);
    }
    if m.validity_code == 0 || m.validity_code > 7 {
        return Err(InvalidValidityCode);
    }
    if m.coefficients.iter().any(|axis| axis.len() != 11) {
        return Err(CoefficientCountMismatch);
    }
    for axis in &m.coefficients {
        for (q, width) in axis.iter().zip(WIDTHS) {
            let bound = 1i32 << (width - 1);
            if *q < -bound || *q >= bound {
                return Err(CoefficientOutOfRange);
            }
        }
    }
    let start = start_tick(m);
    if time < start || time - start > duration_ticks(m) {
        return Err(OutsideValidity);
    }
    Ok(())
}

pub fn coefficient(q: i32) -> f64 {
    let value = if q < 0 {
        -f64::from((-(q + 1)) as u32 + 1)
    } else {
        f64::from(q as u32)
    };
    value / 32.0
}

fn finite(value: f64) -> Result<f64, ReceiverError> {
    if value.is_finite() {
        Ok(value)
    } else {
        Err(ReceiverError::NonfiniteComputation)
    }
}

pub fn evaluate(m: &Message, time: u64) -> Result<[f64; 3], ReceiverError> {
    validate_query(m, time)?;
    let elapsed = time - start_tick(m);
    let ratio = finite(elapsed as f64 / duration_ticks(m) as f64)?;
    let scaled = finite(2.0 * ratio)?;
    let argument = finite(scaled - 1.0)?;
    let mut basis = [0.0; 11];
    for i in 0..11 {
        basis[i] = if i == 0 {
            1.0
        } else if i == 1 {
            argument
        } else {
            let twice_x = finite(2.0 * argument)?;
            let product = finite(twice_x * basis[i - 1])?;
            finite(product - basis[i - 2])?
        };
    }
    let mut result = [0.0; 3];
    for (axis, total) in m.coefficients.iter().zip(&mut result) {
        for i in 0..11 {
            let product = finite(coefficient(axis[i]) * basis[i])?;
            *total = finite(*total + product)?;
        }
    }
    Ok(result)
}
