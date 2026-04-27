import impl.SHA256
import spec.HashAlgorithms

/-!
# Lifting impl `UInt32` containers to spec `BitVec 32` containers

The implementation uses sized vectors of `UInt32` for the working state
(`Impl.State = Vector UInt32 8`) and message block (`Impl.Block =
Vector UInt32 16`).  The spec uses `Array (BitVec 32)` (under the
`HashValue` and `Block` notations from `spec/HashAlgorithms.lean`),
indexed by the panicking accessor `_[i]!`.

This file defines the lifting maps `toSpecState` / `toSpecBlock` and
proves the size and indexing facts the equivalence proof relies on.
The four lemmas are all `@[simp]` so that downstream `simp` calls can
freely commute lifting with size queries and indexing.
-/

open scoped SHS.SHA256

open SHS.SHA256

namespace SHS.Equiv.SHA256.Lift

/-! ## Lifting maps -/

/-- Lift the implementation's working state (eight `UInt32`s) to the
spec's `HashValue` (an `Array` of eight `BitVec 32`s). -/
def toSpecState (s : Impl.State) : HashValue :=
  s.toArray.map UInt32.toBitVec

/-- Lift the implementation's message block (sixteen `UInt32`s) to the
spec's `Block` (an `Array` of sixteen `BitVec 32`s). -/
def toSpecBlock (b : Impl.Block) : Block :=
  b.toArray.map UInt32.toBitVec

/-! ## Size simp lemmas

Both lifting maps preserve size; downstream `simp` uses these to
discharge bounds for `getElem!` accesses. -/

@[simp] theorem size_toSpecState (s : Impl.State) : (toSpecState s).size = 8 := by
  simp [toSpecState]

@[simp] theorem size_toSpecBlock (b : Impl.Block) : (toSpecBlock b).size = 16 := by
  simp [toSpecBlock]

/-! ## Indexing simp lemmas

Bridge the spec's panicking `_[i]!` access on a lifted container to the
implementation's bounds-checked `_[i]` access.  Phrased over `Fin n` so
the bound is automatic. -/

@[simp] theorem getElem!_toSpecState (s : Impl.State) (i : Fin 8) :
    (toSpecState s)[i.val]! = s[i].toBitVec := by
  simp [toSpecState, getElem!_pos, Array.getElem_map, Vector.getElem_toArray]

@[simp] theorem getElem!_toSpecBlock (b : Impl.Block) (i : Fin 16) :
    (toSpecBlock b)[i.val]! = b[i].toBitVec := by
  simp [toSpecBlock, getElem!_pos, Array.getElem_map, Vector.getElem_toArray]

/-! ## Initial-state bridge -/

/-- The impl's initial hash value `H256_256` lifts to the spec's `H0_256`. -/
@[simp] theorem toSpecState_H256_256 :
    toSpecState Impl.H256_256 = SHS.SHA256.H0_256 := by
  unfold toSpecState Impl.H256_256 SHS.SHA256.H0_256
  simp [Array.map]

end SHS.Equiv.SHA256.Lift
