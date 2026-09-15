import Ephemeris.Proofs.CoefficientDecoding

/-! Complete native/model correspondence for coefficients, normalization, both loops,
and checked evaluation. This does not establish a real rounding bound. -/

namespace Ephemeris.Proofs.PositionReconstruction
open Ephemeris.Proofs.CoefficientDecoding
@[simp]
private theorem model_add (a b : Float) : (a + b).toModel = a.toModel + b.toModel := rfl

@[simp]
private theorem model_zero : (Float.ofNat 0).toModel = Float.Model.ofNat 0 := by decide

@[simp]
private theorem model_div (a b : Float) : (a / b).toModel = a.toModel / b.toModel := rfl

@[simp]
private theorem model_mul (a b : Float) : (a * b).toModel = a.toModel * b.toModel := rfl

@[simp]
private theorem model_sub (a b : Float) : (a - b).toModel = a.toModel - b.toModel := rfl

@[simp]
private theorem model_two : (Float.ofNat 2).toModel = Float.Model.ofNat 2 := by decide

@[simp]
private theorem model_one : (Float.ofNat 1).toModel = Float.Model.ofNat 1 := by decide

theorem finite_agree (v : Float)
    : (Implementation.PositionReconstruction.finite v).map Float.toModel
      = Implementation.Correctness.Float.modelFinite v.toModel := by
  change (if v.toModel.isFinite then some v else none).map Float.toModel =
    (if v.toModel.isFinite then some v.toModel else none)
  split <;> rfl

theorem normalizedEpochModelsAgree (m : Message) (time : UInt64)
    : (Implementation.PositionReconstruction.normalizedEpoch m time).map Float.toModel
      = Implementation.Correctness.Float.modelNormalizedEpoch m time := by
  unfold Implementation.PositionReconstruction.normalizedEpoch Implementation.Correctness.Float.modelNormalizedEpoch
  simp only [Option.bind_eq_bind, Option.map_bind]
  change _ = (Implementation.Correctness.Float.modelFinite (((time - Message.startTick m).toFloat /
    (Message.durationTicks m).toFloat).toModel)).bind _
  rw [← finite_agree, Option.bind_map]
  congr 1
  funext ratio
  simp only [Function.comp_apply, Option.map_bind]
  change _ = (Implementation.Correctness.Float.modelFinite ((2.0 * ratio).toModel)).bind _
  rw [← finite_agree, Option.bind_map]
  congr 1
  funext scaled
  exact finite_agree (scaled - 1.0)

private def mapStep (f : α → β) : ForInStep α → ForInStep β
  | .done a => .done (f a)
  | .yield a => .yield (f a)

private theorem forIn_map_option (xs : List ι) (f : α → β)
    (step : ι → α → Option (ForInStep α)) (step' : ι → β → Option (ForInStep β))
    (h : ∀ i a, (step i a).map (mapStep f) = step' i (f a)) (a : α)
    : (forIn xs a step).map f = forIn xs (f a) step' := by
  induction xs generalizing a with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.forIn_cons, Option.bind_eq_bind, Option.map_bind]
      rw [← h, Option.bind_map]
      congr 1
      funext state
      cases state <;> simp [mapStep, ih]

private theorem model_getD (values : Array Float) (i : Nat) (fallback : Float)
    : (values.map Float.toModel).getD i fallback.toModel
      = (values.getD i fallback).toModel := by
  simp [Array.getD_eq_getD_getElem?, Option.getD_map]

theorem basisModelsAgree (argument : Float)
    : (Implementation.PositionReconstruction.basis argument).map (Array.map Float.toModel)
      = Implementation.Correctness.Float.modelBasis argument.toModel := by
  have hfinite := finite_agree
  unfold Implementation.PositionReconstruction.basis Implementation.Correctness.Float.modelBasis
  dsimp only [OfNat.ofNat]
  simp only [bind_pure, Option.bind_eq_bind, Option.map_bind]
  rw [← hfinite, Option.bind_map]
  congr 1
  funext x
  simp only [Function.comp_def, Std.Legacy.Range.forIn_eq_forIn_range']
  conv_rhs => rw [← Array.map_empty (f := Float.toModel)]
  apply forIn_map_option
  intro i values
  split
  next _ => simp [mapStep]
  next _ =>
    split
    next _ => simp [mapStep]
    next _ =>
      simp only [← model_zero, model_getD, ← model_two, ← model_mul, ← model_sub,
        ← hfinite, Option.bind_map, Option.map_bind, Function.comp_def,
        mapStep, Option.map_some, pure, Pure.pure, Array.map_push]

theorem coordinateModelsAgree (integers : Array Int32) (values : Array Float)
    : (Implementation.PositionReconstruction.coordinate integers values).map Float.toModel
      = Implementation.Correctness.Float.modelCoordinate integers
          (values.map Float.toModel) := by
  have hfinite := finite_agree
  unfold Implementation.PositionReconstruction.coordinate Implementation.Correctness.Float.modelCoordinate
  dsimp only [OfNat.ofNat]
  simp only [bind_pure, Std.Legacy.Range.forIn_eq_forIn_range', ← model_zero]
  apply forIn_map_option
  intro i result
  simp only [model_getD, ← coefficientModelsAgree (integers.getD i (Int32.ofNat 0)), ← model_mul, ← model_add,
    ← hfinite, Option.bind_eq_bind, Option.bind_map, Option.map_bind,
    Function.comp_def, mapStep, Option.map_some, pure, Pure.pure]

theorem reconstructModelsAgree (m : Message) (time : UInt64)
    : (Implementation.PositionReconstruction.reconstruct m time).map
        (XYZ.map Float.toModel)
      = Implementation.Correctness.Float.modelReconstruct m time := by
  unfold Implementation.PositionReconstruction.reconstruct Implementation.Correctness.Float.modelReconstruct
  simp only [← normalizedEpochModelsAgree, ← basisModelsAgree, ← coordinateModelsAgree,
    Option.bind_eq_bind, Option.bind_map, Option.map_bind, Function.comp_def,
    Option.map_some, pure, Pure.pure, XYZ.map]

theorem evaluationModelsAgree
    : Implementation.Correctness.Float.EvaluationModelsAgree := by
  intro m time
  unfold Implementation.PositionReconstruction.evaluate Implementation.Correctness.Float.modelEvaluate
  have hrec := reconstructModelsAgree m time
  rw [← hrec]
  cases hv : Message.validateQuery m time with
  | error e => rfl
  | ok _ =>
      cases Implementation.PositionReconstruction.reconstruct m time <;> rfl

/-- Transfer a separately proved software bound through complete correspondence.
Complete native/model correspondence is proved above; the numerical bound remains
a separate obligation. -/
theorem uniformAccuracy_of_modelAccuracy (tolerance : ℝ)
    (htolerance : 0 ≤ tolerance)
    (accuracy
      : ∀ m time,
          Implementation.Correctness.Message.ValidMessage m
          → Implementation.Correctness.Message.InWindow m time
          → ∃ result,
              Implementation.Correctness.Float.modelEvaluate m time = .ok result
              ∧ Implementation.Correctness.PositionAccuracy.Binary64Within result
                  (Definitions.PositionReconstruction.reconstruct m time) tolerance)
    : Implementation.Correctness.Float.UniformAccuracy tolerance := by
  refine ⟨htolerance, ?_⟩
  intro m time hm ht
  obtain ⟨result, hresult, hbound⟩ := accuracy m time hm ht
  have heq := evaluationModelsAgree m time
  rw [hresult] at heq
  cases hnative : Implementation.PositionReconstruction.evaluate m time with
  | error e => simp [hnative, Except.map] at heq
  | ok p =>
      have hp : XYZ.map Float.toModel p = result := by
        simpa only [hnative, Except.map, Except.ok.injEq] using heq
      refine ⟨p, rfl, ?_⟩
      simpa only [hp] using hbound

end Ephemeris.Proofs.PositionReconstruction
