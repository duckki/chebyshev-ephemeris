import Ephemeris.Implementation.Correctness.Rational
import Ephemeris.Implementation.Correctness.Real

/-! Exact agreement of B25 Equation (4) with Mathlib's Chebyshev polynomials. -/

namespace Ephemeris.Proofs.Rational.ChebyshevRecurrence

/-- Proof-only recursive form of the rational array loop. -/
def rationalChebyshevT (x : ℚ) : Nat → ℚ
  | 0 => 1
  | 1 => x
  | n + 2 => 2 * x * rationalChebyshevT x (n + 1) - rationalChebyshevT x n

/-- Proof/test interpretation of the printed Eq. (5) sum without `a_0`.
The literal real source remains Definitions.PositionReconstruction.equation5Printed. -/
def rationalEquation5Sum (n : Nat) (a : List ℚ) (x : ℚ) : ℚ :=
  ((List.range n).map fun j => a.getD (j + 1) 0 * rationalChebyshevT x (j + 1)).sum

theorem chebyshevT_eq_basis (i : Nat) (x : ℚ)
    : (rationalChebyshevT x i : ℝ)
      = Implementation.Correctness.Real.polynomialBasis i (x : ℝ) := by
  induction i using Nat.twoStepInduction with
  | zero => simp [rationalChebyshevT, Implementation.Correctness.Real.polynomialBasis]
  | one => simp [rationalChebyshevT, Implementation.Correctness.Real.polynomialBasis]
  | more n ih₀ ih₁ =>
      simp only [rationalChebyshevT, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat,
        ih₀, ih₁, Implementation.Correctness.Real.polynomialBasis, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
        Polynomial.Chebyshev.T_add_two, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_ofNat, Polynomial.eval_X]

theorem equation4Correct
    : ∀ (i : Nat) (x : ℚ),
        (rationalChebyshevT x i : ℝ)
        = Implementation.Correctness.Real.polynomialBasis i (x : ℝ) :=
  chebyshevT_eq_basis

end Ephemeris.Proofs.Rational.ChebyshevRecurrence
