# Paper and Lean specification

B25 is Bury, Zajdel, and Sośnica (2025), *Design of the broadcast ephemerides for
the Lunar Communication and Navigation Services system*, Progress in Earth and
Planetary Science 12, 20. [Publisher and PDF](https://doi.org/10.1186/s40645-024-00676-1).
Page references use the publisher's 18-page PDF: §2.3 and Eq. (4), page 6;
Eq. (5)/Table 3, page 7; Table 6, page 11; §3.3, pages 13–15; Figure 8,
page 15; conclusions, page 16. Those source passages were checked against the
PDF, including visual inspection of the tables and Figure 8.

Read this guide alongside [Definitions/](../Ephemeris/Definitions). Then continue
with the [Lean implementation and proof status](lean-implementation.md).

The component evaluates the decoded Chebyshev polynomial. The published
allocation informs the project's [decoded input contract](paper-and-spec.md#decoded-input-contract).
Fitting, upstream quantization, velocity, and adaptive compression are separate
work. The paper describes least-squares fitting but does not supply a complete
fitting-solver algorithm. The [format review](references/paper-message-format.md) distinguishes
published facts from project numerical-input decisions. Satellite serialization
is outside this receiver.

## Source definitions and numeric domains

`Definitions/` contains source translations, explicit paper interpretations, and
our adopted decoded-input contract. `Message` keeps published field allocation,
external machine-number interpretations, and the project's selected profile,
bounded tick arithmetic, and validation policy in explicitly labeled sections.
The final section of `PositionReconstruction` applies the paper interpretation
to that input using ideal real arithmetic.
Review project choices against the contract below, separately from paper claims.
Every numerical function in the paper algorithm uses concrete real arithmetic;
the degree and indices are natural numbers. The mathematical source is deterministic.
Transmission precision and receiver arithmetic precision are different questions: Table 6 fixes the former,
while binary64 is our choice for the latter.

Declaration names below are local to the linked module, whose namespace matches
its file path. Shared types (`Frame`, `XYZ`, `Message`, `ReceiverError`) remain
directly under `Ephemeris`; operations on them use the type namespace.

| File / declarations | Source | Interpretation to review |
|---|---|---|
| [Coordinates](../Ephemeris/Definitions/Coordinates.lean): `Frame`, `XYZ` | B25 §2.3 / Table 3 | Coordinate families and X/Y/Z record. The generic component container does not select numeric arithmetic or a message format. |
| [PositionReconstruction](../Ephemeris/Definitions/PositionReconstruction.lean): `chebyshevT` | Eq. (4) | Real recurrence, natural indices, standard initial values |
| Same: `equation5Printed` | Eq. (5) as printed | Sum starts at one; preserved separately from the adopted full sum |
| Same: `startEpoch`, `printedThresholdRhs`, `normalizeEpoch` | Table 3 | Full Julian-date day base plus seconds; literal printed threshold; affine real epoch mapping |
| [PositionReconstruction](../Ephemeris/Definitions/PositionReconstruction.lean): `table3Basis`, `table3Coordinate`, `table3Position` | Table 3 under I2–I4 | Ascending array recurrence and sum from zero, with zero initial accumulator |
| Same: `endEpoch`, `normalizedEpoch` | Table 3 under I1–I4 | Complete start plus validity; real day/second/hour arguments. `reconstruct` composes normalization and `table3Position` directly. |
| [Correctness/Real](../Ephemeris/Implementation/Correctness/Real.lean): `polynomialBasis`, `polynomialCoordinate`, `polynomialPosition` | Eq. (4), Table 3, Mathlib Chebyshev | Project correctness interpretation: independent real polynomial evaluation and finite sums; embed natural indices into Mathlib's integer indices; full weight on a_0 |
| [Message](../Ephemeris/Definitions/Message.lean), published allocation section: `dayBits`, `secondBits`, `validityBits`, `validityFractionBits`, `coefficientFractionBits`, `referenceDayTwice`, `coordinateBits`, `oneHourCoefficientWidths` | Table 6, Figure 8 blue `11_1.0_1.0` | Published widths, scales, epoch origin, and 187-bit coordinate allocation; no invented packing rules |
| [Message](../Ephemeris/Definitions/Message.lean): `Message`, `ReceiverError`, profile constants, `validate`, tick arithmetic, `validateQuery` | Project FP1/FP2/FP3 below, informed by Table 6 and Figure 8 | One bounded decoded-input record; selected signedness, metadata domain, query ticks, and error precedence. Guards are colocated with the contract and are not claimed as paper pseudocode. |
| [PositionReconstruction](../Ephemeris/Definitions/PositionReconstruction.lean), ideal Message interpretation section | Table 3 applied to project FP1/FP2/FP3 | Exact real interpretation of fixed-point coefficients, metadata, and query ticks; ideal unchecked reconstruction and checked evaluation |
| [Binary64Value](../Ephemeris/Definitions/Binary64Value.lean): `unpackedToRational`, `toRational`, `toReal`, `floatToRational` | Pinned Lean unpacked float and binary64 model | Exact stored value: signed mantissa times 2^exponent; rational then real interpretation. Nonfinite values map to none; signed zeros share a numeric value but differ in bits. |
| [Message](../Ephemeris/Definitions/Message.lean), machine-number section: `uint64ToBinary64`, `int32ToBinary64` | Pinned Lean unsigned/signed types and float conversions | External integer-to-binary64 conversions. Exact field interpretations use Lean's `toNat` and `toInt` directly. Widths/time units for this application are project decisions. |

The remaining mathematical views have different review roles: `chebyshevT`
translates Eq. (4), Table 3 loops describe the algorithm, and `Correctness/Real`
uses independent Mathlib polynomials and finite sums as its comparison target. Their agreement is proved,
so collapsing them into aliases would remove a useful specification check.
The real Message adapter composes the source loop and time normalization directly.

Source formulas use defaulted list/array access to be total. Message validation
requires all eleven coefficient entries to exist; loop reasoning establishes
that earlier basis entries exist. Defaults do not authorize malformed inputs.
Likewise, total real division outside the supported interval is not an accepted
receiver behavior.

Pinned sources (Lean/Mathlib v4.33.1):
[Mathlib Chebyshev](https://github.com/leanprover-community/mathlib4/blob/v4.33.1/Mathlib/RingTheory/Polynomial/Chebyshev.lean),
[unpacked constructors](https://github.com/leanprover/lean4/blob/v4.33.1/src/Init/Data/Float/Model/Unpacked/Basic.lean),
[sign interpretation](https://github.com/leanprover/lean4/blob/v4.33.1/src/Init/Data/Float/Model/Unpacked/Sign.lean),
[binary64 format](https://github.com/leanprover/lean4/blob/v4.33.1/src/Init/Data/Float/Model/Format/Basic.lean),
[unpacking](https://github.com/leanprover/lean4/blob/v4.33.1/src/Init/Data/Float/Model/Unpacked/Pack/Basic.lean),
[Float.Model](https://github.com/leanprover/lean4/blob/v4.33.1/src/Init/Data/Float/Model/Float.lean),
[native Float boundary](https://github.com/leanprover/lean4/blob/v4.33.1/src/Init/Data/Float/Float.lean),
[unsigned interpretations](https://github.com/leanprover/lean4/blob/v4.33.1/src/Init/Data/UInt/BasicAux.lean),
[unsigned arithmetic](https://github.com/leanprover/lean4/blob/v4.33.1/src/Init/Data/UInt/Basic.lean),
and [signed integers](https://github.com/leanprover/lean4/blob/v4.33.1/src/Init/Data/SInt/Basic.lean).
Float.Model canonicalizes NaNs; arbitrary NaN payload preservation is not claimed.
Native Float's basic arithmetic, unsigned conversions, and finite checks have
logical bodies using that model. Native [signed conversion](https://github.com/leanprover/lean4/blob/v4.33.1/src/Init/Data/SInt/Float.lean)
is opaque in this version. Our coefficient implementation therefore constructs
the magnitude with bounded integer operations and uses modeled UInt32.toFloat.
Literal constants use Lean's [OfScientific definitions](https://github.com/leanprover/lean4/blob/v4.33.1/src/Init/Data/OfScientific.lean).
The explicit software specification calls model operations directly; native
execution is compared with it, not used to implement the oracle.

## Source interpretations I1–I4

| ID | Printed source | Working interpretation and consequence |
|---|---|---|
| I1 | Table 3's second row assigns `xnmJDmin` again; its RHS is `xnmJDImin + Validity/24`. The mapping then uses `xnmJDmax`. | Define the end as **complete start + validity/24**. This both supplies the missing end variable and includes the seconds offset. Keeping the printed RHS as the end would differ whenever seconds are nonzero, and can put the end before the start. |
| I2 | Inside the loop indexed by `i`, Table 3 uses `T_(n-1)` and `T_(n-2)`. | Use array entries `T[i-1]` and `T[i-2]`, following Eq. (4). |
| I3 | Eq. (5) begins at `i=1`, while Table 3 and Table 6 begin at `i=0`. | Adopt Table 3's full sum, including `a_0`. Preserve the printed Eq. (5) separately. The relationship to prove is **Table 3 sum = `a_0` + printed Eq. (5) sum**, not equality of the two sums. There is no half-weight on `a_0`. |
| I4 | Table 3 accumulates with `XYZ += ...` without an explicit initialization. | Initialize each coordinate accumulator to zero. |

The printed fragments and interpreted real loops occupy the first two attributed
sections of `Definitions/PositionReconstruction.lean`, in one module namespace.
We do not claim equivalence to a literal execution of all of
Table 3: the printed text does not supply a coherent fully initialized algorithm.
Proofs can establish consistency with Eq. (4) and the chosen Table 3 semantics;
review must still decide whether I1–I4 match the intended engineering behavior.


## Decoded input contract

The receiver contracts are numbered by responsibility:

| Contract | Scope |
| --- | --- |
| FP1 | Fixed profile and number representation |
| FP2 | Validation and bounded execution |
| FP3 | Real meanings, binary64 semantics, and native execution |
| FP4 | Upstream quantization guidance, outside the implemented receiver |

FP1–FP3 define the implemented receiver. FP4 documents a quantization policy for
upstream producers. B25 Table 6
and Figure 8 supply the allocation and scale; the project selects the signed
ranges, accepted metadata, query ticks, and evaluation arithmetic below.
There is one concrete `Message`, containing decoded integer fields, defined with
its shared validation policy in [Definitions/Message](../Ephemeris/Definitions/Message.lean).

This component does not encode or decode a satellite bitstream. The published
bit widths constrain values and error analysis; byte order, padding, packet
framing, and a complete communications standard are outside its scope.

## FP1: fixed profile and number representation

- Degree 10: exactly 11 coefficients on each axis, ordered a_0 through a_10.
- Coordinate family: celestial lunocentric, as in B25 Section 3.3's fitting study.
  A service must identify the precise frame realization and time scale externally.
- Every coefficient is a signed two's-complement integer `q`, including the sign
  in its allocated bit width. Its decoded value is exactly `q / 32` meters.
- Coefficient widths are `30, 28, 25, 21, 19, 17, 14, 12, 9, 7, 5`, on each axis.
  These are transcribed from Figure 8's blue `11_1.0_1.0` scenario and sum to 187.
  They are not 187 bits per coefficient or a floating mantissa/exponent encoding.
- A width `w` accepts `-2^(w-1) <= q < 2^(w-1)`. Decoded coefficients fit Int32.
  The largest coefficient field spans -16,777,216 through 16,777,215.96875 meters.

The published allocation studies several window/degree choices. This profile
selects one allocation; it does not claim that every orbit segment fits these
ranges or achieves the paper's empirical reconstruction accuracy. Other widths
or degrees require a separately identified profile.

| Field | Bits | Meaning | Valid decoded integers |
|---|---:|---|---|
| Day offset | 14 | Unsigned days after JD 2461000.5 | 0..16383 |
| Second of day | 17 | Unsigned seconds after that day base | 0..86399; remaining codes invalid |
| Validity | 3 | Unsigned half-hours | 1..7; zero invalid |
| X coefficients | 187 | Signed integers / 32 meters | Per-coefficient signed ranges above |
| Y coefficients | 187 | Signed integers / 32 meters | Same |
| Z coefficients | 187 | Signed integers / 32 meters | Same |

We choose the direct validity encoding, with no bias or special code: `1 = 0.5 h`,
`2 = 1 h`, ..., `7 = 3.5 h`. Four-hour cases mentioned elsewhere in the paper
are outside this profile. Degree, frame, and profile identity are not extra bits
silently added to Table 6's allocation; the service configuration identifies them.

## FP2: validation and bounded execution

The record uses UInt16 day offset, UInt32 seconds, UInt8 validity, and three arrays
of Int32 coefficients. These carriers are wider than some accepted fields.
Validate host integers before conversion; silently truncating an incoming value
into a carrier can conceal an invalid input. Native Python/Rust boundaries must
enforce the same ranges.

Validation checks day, seconds, validity, all three coefficient counts, then
coefficient ranges in X/Y/Z and index order. Query-window checks follow message
validation. Real and Float evaluators both call `Message.validateQuery`.
Rust stores `i32` input vectors so malformed lengths can be rejected; its working
arrays have fixed sizes. Python copies inputs into tuples and enforces the same
carrier, field-range, and shape requirements.

## FP3: real meanings, binary64 semantics, and native execution

The real evaluator interprets coefficient integer q as `(q : Real) / 32`.
The `modelCoefficient` definition in `Correctness/Float` uses
`Float.Model.ofInt32 q / Float.Model.ofUInt8 32`. All Int32 integers and their
q/32 values are exactly representable in binary64; `CoefficientDecodingExact`
states that fact and is proved in [CoefficientDecoding](../Ephemeris/Proofs/Float/CoefficientDecoding.lean).

`Implementation/Float` executes native `Float` arithmetic. Lean v4.33.1 defines
its basic arithmetic and unsigned conversions through `Float.Model` logically,
while compiled code uses native operations. Its `Int32.toFloat` is opaque, so
our conversion uses the modeled UInt32 conversion: for negative q, compute
`-(q+1)` in Int32, add one in UInt32, convert, and negate the float. Each integer
step fits even at Int32's minimum. Positive q converts directly; divide by 32.0
afterward. `CoefficientModelsAgree` specifies correspondence with the direct
model conversion. This helper is an implementation choice, not a paper formula.

The [binary64 kernel](../Ephemeris/Implementation/Float/ReconstructionKernel.lean)
defines normalization, recurrence, summation, and validation once. Native
and model instantiations reuse Lean's arithmetic typeclasses and provide local
`Backend` instances for coefficient decoding, UInt64 conversion, and finiteness.
The model backend lives in Correctness/Float and shares the kernel's control flow,
while the real source and optional Rational evaluator retain separate algorithms.
These operation classes assume no algebraic laws and carry no correctness proofs.

`EvaluationModelsAgree` requires identical result bits and errors between native
Float evaluation (interpreted with `toModel`) and software-model evaluation.
The software oracle actually runs `Implementation.Correctness.Float.modelEvaluate`; converting a native
result afterward would not independently test its arithmetic.

Time lowering uses UInt64 microseconds from JD zero:

```text
start    = 212630443200000000 + dayOffset * 86400000000 + secondOfDay * 1000000
duration = validityCode * 1800000000
```

The accepted metadata bounds keep these operations, including the end epoch,
within UInt64. Query ticks use the same axis. Normalization subtracts ticks before
float conversion. Division, the Chebyshev recurrence, and accumulation are rounded
operations; the accuracy contract requires combined error of at most 10 micrometers
per coordinate. This bound is proved for the shared kernel and native backend; see
[proof status](lean-implementation.md#proof-status).
Approximation of an arbitrary real query time to microsecond ticks is a separate
input error, not included in evaluation of that exact tick.

The primary bound is `Implementation.Correctness.Float.UniformAccuracy tolerance`:
every valid fixed-point message and in-window query succeeds within that tolerance
of real evaluation of the same message. There is no arbitrary-float input profile
or generic message parameter in the receiver. Real, Rational, and Float all
accept this same Message and tick; ℝ, ℚ, and binary64 are working interpretations
of those integer fields.

Accuracy of the software semantics is an intermediate theorem in the proof layer.
The proof combines that bound with native/model correspondence
to establish `UniformAccuracy (1 / 100000)` for the Lean Float implementation. Runtime
agreement with Lean's modeled primitive operations remains an execution assumption supported
by conformance tests; it is not a proof of a compiler or processor.

## FP4: upstream quantization policy

The receiver accepts already-quantized integers and does not round or clip inputs.
A future real-to-grid quantizer should use nearest multiples of 1/32 meter, with
ties to an even scaled integer and rejection of an out-of-range result.
This is a documentation-only proposal. There is no quantizer implementation,
Lean quantization contract, or quantization theorem in the current code. Its input
error and polynomial fitting error would need separate justification.


Proof completion is tracked in [Lean implementation](lean-implementation.md#proof-status).
