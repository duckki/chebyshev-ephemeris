import Ephemeris.Proofs.Float.ChebyshevBasis
import Ephemeris.Proofs.Float.CoordinateReconstruction
import Ephemeris.Proofs.Float.PositionReconstruction

/-! Uniform accuracy of the primary bounded binary64 receiver. The bound measures
arithmetic error against real evaluation of the same decoded message; orbit fitting,
coefficient quantization, frame selection, and native Python/Rust execution are
separate from this statement. -/

namespace Ephemeris.Proofs.Float.UniformAccuracy
open Ephemeris.Proofs.Float.ChebyshevBasis Ephemeris.Proofs.Float.CoefficientDecoding
      Ephemeris.Proofs.Float.CoordinateReconstruction
      Ephemeris.Proofs.Float.EpochNormalization
      Ephemeris.Proofs.Float.PositionReconstruction

private theorem reconstruct_success (m : Message) (time : UInt64) (x : Float.Model)
    (values : Array Float.Model) (px py pz : Float.Model)
    (hn : Implementation.Correctness.Float.modelNormalizedEpoch m time = some x)
    (hb : Implementation.Correctness.Float.modelBasis x = some values)
    (hpx
      : Implementation.Correctness.Float.modelCoordinate m.coefficients.x values
        = some px)
    (hpy
      : Implementation.Correctness.Float.modelCoordinate m.coefficients.y values
        = some py)
    (hpz
      : Implementation.Correctness.Float.modelCoordinate m.coefficients.z values
        = some pz)
    : Implementation.Correctness.Float.modelReconstruct m time
      = some (⟨px, py, pz⟩ : XYZ Float.Model) := by
  unfold Implementation.Correctness.Float.modelReconstruct Implementation.Float.ReconstructionKernel.reconstruct
  dsimp only [Implementation.Correctness.Float.modelNormalizedEpoch,
    Implementation.Correctness.Float.modelBasis,
    Implementation.Correctness.Float.modelCoordinate] at hn hb hpx hpy hpz
  rewrite [Option.bind_eq_bind, hn, Option.bind_some,
    Option.bind_eq_bind, hb, Option.bind_some,
    hpx, Option.bind_some,
    hpy, Option.bind_some,
    hpz, Option.bind_some]
  rfl

private theorem evaluation_success (m : Message) (time : UInt64) (p : XYZ Float.Model)
    (hquery : Message.validateQuery m time = .ok ())
    (hrec : Implementation.Correctness.Float.modelReconstruct m time = some p)
    : Implementation.Correctness.Float.modelEvaluate m time = .ok p := by
  unfold Implementation.Correctness.Float.modelEvaluate Implementation.Float.ReconstructionKernel.evaluate
  dsimp only [Implementation.Correctness.Float.modelReconstruct] at hrec
  simp [hquery, hrec]

private theorem source_coordinate_sum (integers : Array Int32)
    (hsize : integers.size = 11) (X : ℝ)
    : Definitions.PositionReconstruction.table3Coordinate 10
        (integers.toList.map Definitions.PositionReconstruction.coefficient)
        (Definitions.PositionReconstruction.table3Basis 10 X)
      = ((List.range 11).map
          fun i =>
            Definitions.PositionReconstruction.coefficient (integers.getD i 0)
            * Definitions.PositionReconstruction.chebyshevT X i).sum := by
  rewrite [Ephemeris.Proofs.Real.PositionReconstruction.table3Coordinate_basis_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hi : i < 11 := List.mem_range.mp hi
  simp [List.getD, Array.getD, hsize, hi]

/-- Every supported query succeeds in the concrete binary64 model and is within
10 micrometers per axis of real evaluation of the same fixed-point message. -/
theorem modelUniformAccuracy (m : Message) (time : UInt64)
    (hm : Implementation.Correctness.Message.ValidMessage m)
    (ht : Implementation.Correctness.Message.InWindow m time)
    : ∃ result,
        Implementation.Correctness.Float.modelEvaluate m time = .ok result
        ∧ Implementation.Correctness.PositionAccuracy.Binary64Within result
            (Definitions.PositionReconstruction.reconstruct m time) (1 / 100000) := by
  let X := Definitions.PositionReconstruction.normalizedEpoch (Definitions.PositionReconstruction.referenceDay m)
    (Definitions.PositionReconstruction.secondOfDay m) (Definitions.PositionReconstruction.validityHours m)
    (Definitions.PositionReconstruction.timeToReal time)
  obtain ⟨x, u, hn, hu, hX, ex⟩ := normalized_epoch_error m time hm ht
  obtain ⟨values, hb, _, hv⟩ := basis_error x u X hu hX ex
  have hT := chebyshev_bound X hX
  have hax := hm.2.2.2.2 m.coefficients.x (by simp)
  have hay := hm.2.2.2.2 m.coefficients.y (by simp)
  have haz := hm.2.2.2.2 m.coefficients.z (by simp)
  obtain ⟨px, rx, hpx, hrx, ex⟩ := coordinate_error m.coefficients.x values X hT hax.2 hv
  obtain ⟨py, ry, hpy, hry, ey⟩ := coordinate_error m.coefficients.y values X hT hay.2 hv
  obtain ⟨pz, rz, hpz, hrz, ez⟩ := coordinate_error m.coefficients.z values X hT haz.2 hv
  refine Exists.intro (⟨px, py, pz⟩ : XYZ Float.Model) ?_
  constructor
  · have hquery : Message.validateQuery m time = .ok () := by
      apply (Ephemeris.Proofs.Message.queryValidationCorrect m time).mpr
      exact ⟨hm, ht⟩
    have hrec : Implementation.Correctness.Float.modelReconstruct m time = some (⟨px, py, pz⟩ : XYZ Float.Model) :=
      reconstruct_success m time x values px py pz hn hb hpx hpy hpz
    exact evaluation_success m time _ hquery hrec
  · unfold Implementation.Correctness.PositionAccuracy.Binary64Within
    rw [hrx, hry, hrz]
    change 0 ≤ (1 : ℝ)/100000 ∧ _
    refine ⟨by norm_num, ?_, ?_, ?_⟩
    · simpa only [Definitions.PositionReconstruction.reconstruct,
        Definitions.PositionReconstruction.table3Position, Definitions.PositionReconstruction.coefficients, XYZ.map, Message.degree,
        UInt16.toNat_ofNat, Nat.reduceMod,
        source_coordinate_sum _ hax.1] using ex
    · simpa only [Definitions.PositionReconstruction.reconstruct,
        Definitions.PositionReconstruction.table3Position, Definitions.PositionReconstruction.coefficients, XYZ.map, Message.degree,
        UInt16.toNat_ofNat, Nat.reduceMod,
        source_coordinate_sum _ hay.1] using ey
    · simpa only [Definitions.PositionReconstruction.reconstruct,
        Definitions.PositionReconstruction.table3Position, Definitions.PositionReconstruction.coefficients, XYZ.map, Message.degree,
        UInt16.toNat_ofNat, Nat.reduceMod,
        source_coordinate_sum _ haz.1] using ez

/-- The native Lean Float receiver inherits the proved model bound through the
complete operation-by-operation correspondence theorem. -/
theorem uniformAccuracy : Implementation.Correctness.Float.UniformAccuracy (1 / 100000) :=
  uniformAccuracy_of_modelAccuracy _ (by norm_num) modelUniformAccuracy

end Ephemeris.Proofs.Float.UniformAccuracy
