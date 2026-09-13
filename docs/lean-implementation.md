# Lean implementations and correctness

Review the [paper specification and decoded input](paper-and-spec.md) first.
The primary path evaluates one `Message` with two arithmetic interpretations:
ideal real arithmetic and native binary64. The paper supplies the polynomial
algorithm; the bounded representation, guards, operation schedule, and error
contracts are project definitions.

## Review boundaries

| Location | Review responsibility |
| --- | --- |
| [Definitions/](../Ephemeris/Definitions) | Review paper/source translations, the ideal real interpretation, and the explicitly labeled project decoded-input contract and guards. |
| [Implementation/](../Ephemeris/Implementation) | Inspect runtime code and representation choices. |
| [Implementation/Correctness/](../Ephemeris/Implementation/Correctness) | Inspect mathematical meanings, theorem statements, assumptions, and independent software-model execution. |
| [Proofs/](../Ephemeris/Proofs) | Run Lean and the axiom audit. Manual proof-script review is not required. |
| [Tests/](../Ephemeris/Tests), [FuzzOracle/](../Ephemeris/FuzzOracle) | Light review of regression expectations, oracle construction, and which implementation each target executes. |

`Ephemeris/` contains only directories; [Ephemeris.lean](../Ephemeris.lean) is the
public entry point. It imports the primary path and its completed proofs.
Definitions do not depend on Implementation. Runtime categories do not import
siblings, Correctness, proofs, or tooling, even transitively. Shared
input guards live with the contract in Definitions/Message and serve all three
evaluators. Exact rational arithmetic lives in Rational/PositionReconstruction; relationships live
in Correctness. There are no per-directory import aggregators.

## Primary implementation and correctness map

Each module uses its file path as its namespace, with no extra nested namespace.
The exceptions are shared types directly under `Ephemeris` and their operations
under the type namespace (`Message.validateQuery`, `XYZ.map`). Names in the table
are local to the linked module unless qualified.

The final section of Definitions/PositionReconstruction is the non-executable
ideal Message model; Implementation/Float contains the shared binary64 kernel and
its native backend. Both the ideal model and native backend expose unchecked
`reconstruct` and checked `evaluate`, accepting `Message` and a `UInt64` query tick.
`Message.validateQuery` supplies common guards. Real results use `ℝ` and are
noncomputable mathematical values; Float results use native `Float`.

| Requirement / module | Declarations and review responsibility |
|---|---|
| FP1, FP2, FP3 / [Message](../Ephemeris/Definitions/Message.lean) | `Message`; profile constants `coefficientWidths`, `degree`, `frame`; `coefficientFits`, `validate`; bounded `epochOriginTick`, `startTick`, `durationTicks`, `validateQuery` |
| FP3 / [Ideal real interpretation](../Ephemeris/Definitions/PositionReconstruction.lean), ideal Message section | `coefficient`, `timeToReal`, `referenceDay`, `secondOfDay`, `validityHours`, `coefficients`: exact interpretations of integer fields; `reconstruct`, `evaluate`: source application and shared checks |
| FP3 / [Binary64 kernel](../Ephemeris/Implementation/Float/ReconstructionKernel.lean) | `Backend`, `finite`, `normalizedEpoch`, `basis`, `coordinate`, `reconstruct`, `evaluate`: shared operation schedule, finite checks, fixed loops, and Message validation; no algebraic laws or proof fields |
| FP3 / [Float](../Ephemeris/Implementation/Float/PositionReconstruction.lean) | `coefficient` and a local `Backend Float` instance: native conversion and classification; `finite`, `normalizedEpoch`, `basis`, `coordinate`, `reconstruct`, `evaluate`: concrete native wrappers around the shared kernel |
| FP1, FP2, FP3 / [Correctness/Message](../Ephemeris/Implementation/Correctness/Message.lean) | Independent `CoefficientFits`, `ValidMessage`, and exact `InWindow`, used in the Real and Float contracts |
| N1, FP2, FP3 / [Correctness/Real](../Ephemeris/Implementation/Correctness/Real.lean) | `polynomialBasis`, `polynomialCoordinate`, `polynomialPosition`: independent comparison semantics; loop/polynomial agreement for every normalized argument (`SourceAlgorithmCorrect`), independent Message `position`, checked `EvaluationCorrect`, and `QueryInterpretationCorrect` |
| FP3 / [Correctness/Float](../Ephemeris/Implementation/Correctness/Float.lean), model execution | `modelCoefficient` and local model instances: software binary64 conversion, literals, and classification; `modelFinite`, `modelNormalizedEpoch`, `modelBasis`, `modelCoordinate`, `modelReconstruct`, `modelEvaluate`: the same kernel instantiated with Float.Model |
| FP3 / [Correctness/Float](../Ephemeris/Implementation/Correctness/Float.lean) | `CoefficientDecodingExact`, `CoefficientModelsAgree`, `EvaluationModelsAgree`, `UniformAccuracy`: model decoding, native/model bits and errors, supported-domain success, and coordinatewise error against real evaluation of the same message/query |
| N3 / [Correctness/PositionAccuracy](../Ephemeris/Implementation/Correctness/PositionAccuracy.lean) | Shared `RealWithin` and `Binary64Within`: real coordinatewise bounds and finite float output interpretation |
| FP2 / [Message](../Ephemeris/Definitions/Message.lean) | `ReceiverError`: shared project error codes; each implementation uses its specified subset |
| Representation helper / [Definitions/Coordinates](../Ephemeris/Definitions/Coordinates.lean) | Componentwise `XYZ.map`; colocated with its record by project layout policy, not attributed to the paper. No arithmetic or message-precision policy. |

The five correctness modules separate active review questions: Message validity,
Real source consistency, Float execution/accuracy, Rational refinement, and shared
PositionAccuracy relations. `Real.lean` compares the paper loops in Definitions
with an independent polynomial sum.
`SourceAlgorithmCorrect` states that agreement directly for any normalized
argument; query interpretation is a separate claim.

Natural-valued `startTickNat` and `durationTicksNat` helpers, the internal
`tickArithmeticCorrect` bridge, and the validation lemmas live in
[Proofs/Message](../Ephemeris/Proofs/Message.lean). Validation and error-composition
lemmas state their propositions directly in Proofs.
The public `InWindow` relation contains its exact mathematical interval directly,
so reviewing accepted queries does not require reading proof helpers.
`CoefficientFits` remains in Correctness because it is part of `ValidMessage`.

The real and rational interpretations derive the epoch origin and fixed-point
scales from the published constants in `Definitions.Message`. `ValidMessage`
uses the published day and validity bit widths. Validation, query interpretation,
and coefficient-decoding proofs connect the bounded implementation constants to
these source definitions. The second-of-day domain remains the stricter 0..86399
range selected by the input contract.

## Validation and arithmetic

The [decoded input contract](paper-and-spec.md#decoded-input-contract) is authoritative.
Validation rejects inputs in this order:

| Check | Error |
| --- | --- |
| Day offset is below 16384 | `invalidDayOffset` |
| Second of day is below 86400 | `invalidSecondOfDay` |
| Validity code is in 1..7 | `invalidValidityCode` |
| All three axes have eleven coefficients | `coefficientCountMismatch` |
| Coefficients fit their assigned signed widths, in axis/index order | `coefficientOutOfRange` |
| Query lies in the inclusive interval | `outsideValidity` |
| Each used floating intermediate is finite | `nonfiniteComputation` (Float only) |

These are project requirements, not claims that the paper specifies errors.
Invalid external integers must be rejected before converting into Lean/Rust
carriers; silently truncating them would change the input being checked.

Float subtracts integer ticks before conversion, then separately rounds division,
multiplication by two, and subtraction of one. It constructs eleven Chebyshev
basis values, decodes each coefficient as q/32, and accumulates each coordinate
in increasing index order. Preserve the stated grouping: no fused multiply-add,
reassociation, or alternative summation without a new numerical argument.

The native signed-conversion helper constructs an unsigned magnitude because
Lean v4.33.1's `Int32.toFloat` is opaque. Its correspondence with signed model conversion is proved for every Int32, including
the minimum negative value.
The [model execution](../Ephemeris/Implementation/Correctness/Float.lean) definitions
execute `Float.Model` operations independently. Their internal big-number operations
are proof/oracle machinery, not the implementation recipe for Python or Rust.
There are no runtime error radii in the primary Float evaluator.

The [shared kernel](../Ephemeris/Implementation/Float/ReconstructionKernel.lean)
parameterizes only the binary64 operation schedule. It reuses Lean's `Add`, `Sub`,
`Mul`, `Div`, and `OfNat` typeclasses, plus a three-field `Backend` class for decoded
coefficients, UInt64 conversion, and finiteness. Each concrete module declares a
local backend instance; the model module also supplies its local numeric-literal
instance. Public `abbrev` specializations retain concrete Float/Float.Model APIs.
There are no field/ring assumptions or global backend instances. Inline kernel
definitions expose the selected operations to native code generation.
The real source interpretation and optional Rational evaluator remain separate.

The model oracle shares control flow with the native backend while executing
software arithmetic independently. It does not derive its answer from a native
result. Shared scheduling errors require the separate mathematical contracts;
native/model differential agreement alone cannot detect them.

## Proof status

**The native Float evaluator has proved native/model correspondence, supported-domain
success, and a 10-micrometer per-coordinate error bound.** The proofs apply to the
shared binary64 kernel and its concrete backends.
The model accuracy bound is stated directly as an intermediate theorem in
`Proofs/Float/UniformAccuracy`; `UniformAccuracy` is the public accuracy contract.

The [audit](../Ephemeris/Tests/ProofAudit.lean) checks 33 named theorem entry points
and permits only `propext`, `Classical.choice`, and `Quot.sound`. It checks the
complete axiom dependencies of those declarations. Building a proposition
definition alone does not prove it.

| Obligation | Status |
| --- | --- |
| Real source loops equal independent Chebyshev polynomial semantics | Proved |
| Message validation exactly matches field ranges and shape | Proved |
| Query validation exactly matches message validity and the inclusive interval | Proved |
| Bounded tick arithmetic agrees with natural-number arithmetic without wraparound | Proved |
| Checked real evaluation returns the specified position exactly on valid queries | Proved |
| Integer tick interval agrees with the paper's real Julian-date interval | Proved |
| Native Float normalization agrees with explicit software-model normalization | Proved |
| `CoefficientDecodingExact` | Proved for every Int32 carrier |
| `CoefficientModelsAgree` | Proved for every Int32 carrier |
| `EvaluationModelsAgree` for the complete Float evaluator | Proved for every message/query, including invalid inputs |
| Software-model success and accuracy within 10 micrometers per coordinate | Proved as an intermediate theorem |
| `UniformAccuracy (1 / 100000)` for native Float | Proved |

The uniform accuracy contract requires **10 micrometers per coordinate**, finite
results and success for every supported message/query. It compares absolute error
in meters against real evaluation of the same integer message and tick. Fitting error, upstream
quantization, tick-grid approximation, frame/time-scale conversions, and physical
orbit accuracy are separate obligations. FP4 documents a future quantization policy;
no quantizer implementation or placeholder Lean contract is included.

[CoefficientDecoding](../Ephemeris/Proofs/Float/CoefficientDecoding.lean) proves
small-integer normalization, normal binary64 packing/unpacking, the bounded signed
conversion (including Int32 minimum), and exact division by 32. These facts derive
from the pinned model definitions; no generic rounding axiom or finite enumeration
of coefficient inputs is used.

[PositionReconstruction](../Ephemeris/Proofs/Float/PositionReconstruction.lean) proves
primitive correspondence through both loops, all three coordinates, and the shared
validation branches. It establishes equality of the complete
native Lean and model results, including errors. This is separate from Python/Rust
source equivalence.

[UniformAccuracy](../Ephemeris/Proofs/Float/UniformAccuracy.lean) proves the model
bound and transfers it to the native evaluator. Its numerical dependencies are:

| Proof module | Fact or obligation | Status |
| --- | --- | --- |
| [Binary64Rounding](../Ephemeris/Proofs/Float/Binary64Rounding.lean) | Conservative one-ulp bounds derived from the pinned model's shifts, rounding, and packing; covers signed zero, subnormals, and mantissa carry | Proved |
| [Binary64Arithmetic](../Ephemeris/Proofs/Float/Binary64Arithmetic.lean) | Addition, subtraction, and multiplication produce finite results within explicit error bounds when the exact operation meets the stated magnitude limit | Proved |
| [Binary64Division](../Ephemeris/Proofs/Float/Binary64Division.lean) | Natural integers below 2^53 convert exactly; the normalization quotient has error at most 2^-51 for 0 ≤ n ≤ d < 2^53 and d > 0 | Proved |
| [EpochNormalization](../Ephemeris/Proofs/Float/EpochNormalization.lean) | Valid tick normalization succeeds, matches the paper's real epoch interpretation within 3·2^-50, and has its real reference in [-1,1] | Proved |
| [ChebyshevBasis](../Ephemeris/Proofs/Float/ChebyshevBasis.lean) | The eleven-entry loop succeeds; basis error at index i is at most 3^i·2^-43, using Mathlib's real Chebyshev bound | Proved |
| [CoordinateReconstruction](../Ephemeris/Proofs/Float/CoordinateReconstruction.lean) | Ascending accumulation succeeds; individual coefficient widths bound the total per-axis error by 10^-5 meters | Proved |

All radii and rational interpretations in this analysis are proof machinery.
The bound is stated in `Implementation/Correctness/Float.lean`. The concrete
rounding bridge is proved directly using Lean's `Float.Model` and Mathlib. No rounding axiom
or exhaustive enumeration of input messages substitutes for the proof. The
[library assessment](references/floating-point-library-assessment.md) records the
available libraries and the proof approach used here.

## Optional rational reference

[Rational/PositionReconstruction](../Ephemeris/Implementation/Rational/PositionReconstruction.lean)
uses concrete `ℚ` arithmetic to evaluate the **same `Message` and `UInt64` tick**
as Real and Float. Its inputs retain degree 10, the selected coefficient widths,
q/32-meter coefficients, and the shared `Message.validateQuery` checks. There is
no separate rational input type, arbitrary-degree receiver API, or error policy.
Rational is optional execution, outside the primary Real/Float import graph.

The fields and tick have exact rational interpretations, so this path needs no
real-to-rational approximation layer. It computes the full Julian-date mapping
exactly, following the real source; Float uses bounded elapsed ticks and rounds
its operations. Rational's unbounded fractions are reference arithmetic, not
instructions for the shipped Float implementations.

[Correctness/Rational](../Ephemeris/Implementation/Correctness/Rational.lean) has
two public contracts in the `Ephemeris.Implementation.Correctness.Rational` namespace:

| Contract | Meaning |
| --- | --- |
| `ReconstructionCorrect` | Cast the computed rational XYZ to reals: it equals `Definitions.PositionReconstruction.reconstruct` on the identical Message and tick. The unchecked identity also covers totalized division and missing-coefficient defaults outside the accepted domain. |
| `EvaluationCorrect` | Cast only successful coordinates in the checked result: the entire `Except` equals `Definitions.PositionReconstruction.evaluate`, including every rejection. Rational therefore inherits its supported-domain success and error behavior. |

[Proofs/Rational](../Ephemeris/Proofs/Rational) holds recurrence, loop, and cast
lemmas. Exact refinement reuses the real source's proof of agreement with
independent Chebyshev polynomials. The real interval mapping theorem lives
with the [real proofs](../Ephemeris/Proofs/Real/PositionReconstruction.lean) and
covers arbitrary real scalar parameters.

The [Python rational port](python-implementation.md#optional-rational-reference)
also shares the bounded Message with Float. The Rational oracle accepts the same
P3 `evaluate` requests as the Float oracles; successful outputs are exact fraction
pairs.

Shared error relations are in
[PositionAccuracy](../Ephemeris/Implementation/Correctness/PositionAccuracy.lean),
with their composition lemma in
[Proofs/ErrorComposition](../Ephemeris/Proofs/ErrorComposition.lean). Upstream real-input
quantization requires a separate implementation and error bound.

## Setup

Install Lean's `elan` toolchain manager and use the pinned toolchain. From the
repository root, fetch the Mathlib build cache and build all default targets:

```sh
make
```

`make cache` fetches the cache without building the project. Downloads stay in
the ignored `.lake/mathlib-cache/` directory; set `MATHLIB_CACHE_DIR` to override it.
Subsequent checks normally need only `lake build`. The default targets include
836 executable checks: 337 message/tick checks, 394 independent/native/model Float
checks, 33 stored-binary64 interpretation checks, and 72 optional Rational Message checks.
They also build the Rational and Float oracles, using the same bounded P3 input schema.

See the [development guide](development.md#formatting-and-linting) for the pinned
LeanFmt dependency, formatting commands, and Lean lint checks.

Continue with the [Python](python-implementation.md) and [Rust](rust-implementation.md)
ports. Their source correspondence is tested rather than formally proved; shared
comparison methods and evidence limits are in [fuzzing](fuzzing.md).
