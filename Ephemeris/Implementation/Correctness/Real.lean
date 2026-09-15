import Ephemeris.Definitions.PositionReconstruction
import Mathlib.RingTheory.Polynomial.Chebyshev
import Ephemeris.Implementation.Correctness.Message

/-!
# Consistency of the ideal real number specification

These reviewable statements connect the paper's loops to independent polynomial
semantics and the decoded Message to its checked real meaning. They validate the
source interpretation used by Float correctness; there is no separate Real runtime.
Keeping these claims separate avoids hiding source-consistency assumptions in proofs.
-/

/-!
## Independent real-polynomial interpretation of the source equations

Sources: B25 Equation (4) and Table 3; Mathlib's
`Polynomial.Chebyshev.T` supplies an independent polynomial representation.
The coefficient convention is Table 3's full sum from zero, without halving `a_0`.

N1: these mathematical outputs are real-valued, including irrational inputs.
Mathlib's polynomial is indexed by integers; B25 uses nonnegative degrees, so
`polynomialBasis` embeds `Nat` indices into `ℤ`. The use of `ℝ` interprets the source's
continuous mathematics; B25 does not specify exact rational or IEEE arithmetic.

Project input requirements are separate in `Implementation.Correctness.Message`.
See `docs/paper-and-spec.md` for the source-to-definition mapping.
-/

namespace Ephemeris.Implementation.Correctness.Real
open Ephemeris.Definitions.PositionReconstruction
      Ephemeris.Implementation.Correctness.Message

/-- B25 Equation (4), represented independently by Mathlib's Chebyshev polynomial
and polynomial evaluation. This definition does not call the executable recurrence. -/
noncomputable def polynomialBasis (i : Nat) (x : ℝ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (i : ℤ)).eval x

/-- B25 Table 3's mathematical coordinate sum `Σ (i=0..n), a_i T_i(x)`.
Unlike the receiver's loops, this uses a finite sum of evaluated polynomials.
The caller must supply n+1 coefficients; zero defaults only make the formula total.
The concrete Message validator enforces the selected profile shape. -/
noncomputable def polynomialCoordinate (n : Nat) (a : List ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), a.getD i 0 * polynomialBasis i x

/-- B25 Table 3's three coordinate sums at an already normalized epoch. -/
noncomputable def polynomialPosition (n : Nat) (a : XYZ (List ℝ)) (x : ℝ) : XYZ ℝ :=
  ⟨
    polynomialCoordinate n a.x x,
    polynomialCoordinate n a.y x,
    polynomialCoordinate n a.z x
  ⟩

/-- N1: B25's interpreted real loops equal the independent polynomial sum for
any degree, coefficients, and normalized argument. Epoch interpretation is separate. -/
def SourceAlgorithmCorrect : Prop :=
  ∀ n coefficients x,
    table3Position n coefficients x = polynomialPosition n coefficients x

/-- FP3: exact source meaning of a Message, using independent polynomial sums. -/
noncomputable def position (m : Message) (time : UInt64) : XYZ ℝ :=
  polynomialPosition Message.degree.toNat (coefficients m)
    (normalizedEpoch (referenceDay m) (secondOfDay m) (validityHours m) (timeToReal time))

/-- FP2/FP3: real evaluation succeeds exactly for valid messages/queries and
returns their polynomial meaning. This includes rejection completeness. -/
def EvaluationCorrect : Prop :=
  ∀ m time result,
    evaluate m time = .ok result
    ↔ ValidMessage m ∧ InWindow m time ∧ result = position m time

/-- FP3: the exact tick interval means the same interval as the paper's day units. -/
def QueryInterpretationCorrect : Prop :=
  ∀ m time,
    ValidMessage m
    → (InWindow m time
        ↔ startEpoch (referenceDay m) (secondOfDay m) ≤ timeToReal time
          ∧ timeToReal time ≤ endEpoch (referenceDay m) (secondOfDay m) (validityHours m))

end Ephemeris.Implementation.Correctness.Real
