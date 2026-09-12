import Ephemeris.Proofs.Rational.ChebyshevRecurrence

/-! Loop invariants for the Table 3 array construction and coordinate sums. -/

namespace Ephemeris.Proofs.Rational.ReconstructionLoops
open Ephemeris.Proofs.Rational.ChebyshevRecurrence

private def basisStep (x : ℚ) (T : Array ℚ) (i : Nat) : Array ℚ :=
  if i = 0 then
    T.push 1
  else if i = 1 then
    T.push x
  else
    T.push (2 * x * T.getD (i - 1) 0 - T.getD (i - 2) 0)

private theorem basis_as_fold (n : Nat) (x : ℚ)
    : Implementation.Rational.PositionReconstruction.table3Basis n x
      = (List.range (n + 1)).foldl (basisStep x) #[] := by
  simp only [Implementation.Rational.PositionReconstruction.table3Basis, beq_iff_eq]
  simp only [← apply_ite (fun a : Array ℚ => (pure (ForInStep.yield a) : Id _))]
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, ← List.range_eq_range']
  unfold basisStep
  simp only [Array.getD_eq_getD_getElem?]

private theorem basis_step_prefix (x : ℚ) (k : Nat)
    : basisStep x (((List.range k).map (rationalChebyshevT x)).toArray) k
      = ((List.range (k + 1)).map (rationalChebyshevT x)).toArray := by
  rw [List.range_succ, List.map_append]
  cases k with
  | zero => simp [basisStep, rationalChebyshevT]
  | succ k =>
      cases k with
      | zero => simp [basisStep, rationalChebyshevT]
      | succ k => simp [basisStep, Array.getD, rationalChebyshevT]

private theorem basis_fold_prefix (x : ℚ) (k : Nat)
    : (List.range k).foldl (basisStep x) #[]
      = ((List.range k).map (rationalChebyshevT x)).toArray := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
      simpa only [List.range_succ] using basis_step_prefix x k

theorem table3Basis_eq_prefix (n : Nat) (x : ℚ)
    : Implementation.Rational.PositionReconstruction.table3Basis n x
      = ((List.range (n + 1)).map (rationalChebyshevT x)).toArray := by
  rw [basis_as_fold, basis_fold_prefix]

theorem table3BasisCorrect
    : ∀ (n : Nat) (x : ℚ),
        (Implementation.Rational.PositionReconstruction.table3Basis n x).size = n + 1
        ∧ ∀ i,
            i ≤ n
            → (Implementation.Rational.PositionReconstruction.table3Basis n x).getD i 0
              = rationalChebyshevT x i := by
  intro n x
  rw [table3Basis_eq_prefix]
  constructor
  · simp
  · intro i hi
    simp [Array.getD, Nat.lt_succ_of_le hi]

private theorem fold_sum {α : Type} [AddMonoid α] (f : Nat → α) (k : Nat) (v : α)
    : (List.range k).foldl (fun acc i => acc + f i) v
      = v + ((List.range k).map f).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp [List.range_succ, List.foldl_append, ih, add_assoc]

theorem table3Coordinate_eq_sum (n : Nat) (a : List ℚ) (T : Array ℚ)
    : Implementation.Rational.PositionReconstruction.table3Coordinate n a T
      = ((List.range (n + 1)).map fun i => a.getD i 0 * T.getD i 0).sum := by
  simp only [Implementation.Rational.PositionReconstruction.table3Coordinate]
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    ← List.range_eq_range', fold_sum]

theorem table3Coordinate_basis_sum (n : Nat) (a : List ℚ) (x : ℚ)
    : Implementation.Rational.PositionReconstruction.table3Coordinate n a
        (Implementation.Rational.PositionReconstruction.table3Basis n x)
      = ((List.range (n + 1)).map fun i => a.getD i 0 * rationalChebyshevT x i).sum := by
  rw [table3Coordinate_eq_sum, table3Basis_eq_prefix]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  simp [Array.getD, hi]

theorem equation5Table3Relation
    : ∀ (n : Nat) (a : List ℚ) (x : ℚ),
        Implementation.Rational.PositionReconstruction.table3Coordinate n a
          (Implementation.Rational.PositionReconstruction.table3Basis n x)
        = a.getD 0 0 + rationalEquation5Sum n a x := by
  intro n a x
  rw [table3Coordinate_basis_sum]
  simp [List.range_succ_eq_map, List.map_map, rationalChebyshevT,
    rationalEquation5Sum, Function.comp_def]

end Ephemeris.Proofs.Rational.ReconstructionLoops
