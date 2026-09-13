import Init.Data.Float.Float
import Ephemeris.Implementation.Float.ReconstructionKernel

/-! FP3: native binary64 evaluation of the authoritative fixed-point Message.
Native arithmetic instances and a local decoding/classification backend
instantiate the shared binary64 reconstruction schedule. All arithmetic executes native Float operations with bounded integer
conversions; the Float.Model backend is defined separately in Correctness/Float.
The native runtime does not execute that backend. -/

namespace Ephemeris.Implementation.Float.PositionReconstruction

/-- FP3: exact coefficient decoding for these signed integer widths. -/
def coefficient (q : Int32) : Float :=
  -- Int32.toFloat is opaque in Lean v4.33.1. UInt32.toFloat has a logical model.
  -- For q < 0, -(q+1) fits Int32 even at its minimum; +1 then fits UInt32.
  let value := if q < 0 then -((-(q + 1)).toUInt32 + 1).toFloat else q.toUInt32.toFloat
  value / 32.0

/-- FP3: native conversion and classification for the shared binary64 schedule. -/
local instance : ReconstructionKernel.Backend Float where
  coefficient := coefficient
  ofUInt64 := UInt64.toFloat
  isFinite := Float.isFinite

/-- FP3: reject nonfinite native values. -/
abbrev finite := ReconstructionKernel.finite (α := Float)

/-- FP3: bounded elapsed ticks, with separately rounded native operations. -/
abbrev normalizedEpoch := ReconstructionKernel.normalizedEpoch (α := Float)

/-- FP3 / B25 Table 3: the shared eleven-entry recurrence using native Float. -/
abbrev basis := ReconstructionKernel.basis (α := Float)

/-- FP3 / B25 Table 3: the shared ascending sum using native Float. -/
abbrev coordinate := ReconstructionKernel.coordinate (α := Float)

/-- FP3: unchecked native reconstruction of the same Message and query tick. -/
abbrev reconstruct := ReconstructionKernel.reconstruct (α := Float)

/-- FP2/FP3: common validation and native reconstruction. -/
abbrev evaluate := ReconstructionKernel.evaluate (α := Float)

end Ephemeris.Implementation.Float.PositionReconstruction
