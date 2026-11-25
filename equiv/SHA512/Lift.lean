import impl.SHA512
import spec.Functions

/-!
# Lifting impl `UInt64` containers to spec `BitVec 64` containers

Parallel to `equiv/SHA256/Lift.lean` at 64-bit width.  The
implementation uses `Vector UInt64` for working state and message
block; the spec's `SHA512` namespace uses `Vector (BitVec 64)` of the
same shape (under the `HashValue` / `Block` scoped notations from
`spec/Functions.lean`). -/

open scoped SHS.SHA512

open SHS.SHA512

namespace SHS.Equiv.SHA512.Lift

/-! ## Lifting maps -/

/-- Lift the implementation's working state (eight `UInt64`s) to the
spec's `HashValue` (a `Vector` of eight `BitVec 64`s). -/
def toSpecState (s : Impl.State) : HashValue :=
  s.map UInt64.toBitVec

/-- Lift the implementation's message block (sixteen `UInt64`s) to the
spec's `Block` (a `Vector` of sixteen `BitVec 64`s). -/
def toSpecBlock (b : Impl.Block) : Block :=
  b.map UInt64.toBitVec

/-! ## Indexing

Bridge spec-side indexing on a lifted container to the implementation's
bounds-checked `_[i]` access.  Phrased over `Fin n` so the bound is
automatic. -/

theorem getElem!_toSpecBlock (b : Impl.Block) (i : Fin 16) :
    (toSpecBlock b)[i.val]! = b[i].toBitVec := by
  simp [toSpecBlock, getElem!_pos]

end SHS.Equiv.SHA512.Lift
