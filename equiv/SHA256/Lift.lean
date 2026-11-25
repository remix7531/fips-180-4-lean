import impl.SHA256
import spec.Functions

/-!
# Lifting impl `UInt32` containers to spec `BitVec 32` containers

The implementation uses sized vectors of `UInt32` for the working state
(`Impl.State = Vector UInt32 8`) and message block (`Impl.Block =
Vector UInt32 16`).  The spec, in the SHA-256 namespace, uses
`Vector (BitVec 32) 8` and `Vector (BitVec 32) 16` (under the
`HashValue` and `Block` notations from `spec/Functions.lean`).

The lifting maps are pointwise applications of `UInt32.toBitVec`.
The block indexing lemma uses a finite index for its bound.
-/

open scoped SHS.SHA256

open SHS.SHA256

namespace SHS.Equiv.SHA256.Lift

/-! ## Lifting maps -/

/-- Lift the implementation's working state (eight `UInt32`s) to the
spec's `HashValue` (a `Vector` of eight `BitVec 32`s). -/
def toSpecState (s : Impl.State) : HashValue :=
  s.map UInt32.toBitVec

/-- Lift the implementation's message block (sixteen `UInt32`s) to the
spec's `Block` (a `Vector` of sixteen `BitVec 32`s). -/
def toSpecBlock (b : Impl.Block) : Block :=
  b.map UInt32.toBitVec

/-! ## Indexing

Bridge spec-side indexing on a lifted container to the implementation's
bounds-checked `_[i]` access.  Phrased over `Fin n` so the bound is
automatic. -/

theorem getElem!_toSpecBlock (b : Impl.Block) (i : Fin 16) :
    (toSpecBlock b)[i.val]! = b[i].toBitVec := by
  simp [toSpecBlock, getElem!_pos]

end SHS.Equiv.SHA256.Lift
