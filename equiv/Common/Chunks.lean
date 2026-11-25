import spec.Setup

/-! # Common: chunking lemmas

The specification parses bit messages by consecutive chunks. The implementation
slices bytes by position. The bridge below exposes each full chunk as a list
slice indexed by `drop` and `take`. -/

namespace SHS.Equiv.Chunks

/-- Finished chunks are a prefix of every result of the accumulator. -/
private theorem toChunks_go_append_finished {α : Type _} (width : Nat) (items : List α)
    (finished : Array (List α)) :
    listChunks.go width items finished = finished.toList ++ listChunks.go width items #[] := by
  cases items with
  | nil => simp [listChunks.go]
  | cons item rest =>
    simp only [listChunks.go, List.splitAt_eq]
    rw [toChunks_go_append_finished width (rest.drop width) (finished.push (item :: rest.take width)),
      toChunks_go_append_finished width (rest.drop width) (#[].push (item :: rest.take width))]
    simp [List.append_assoc]
termination_by items.length
decreasing_by
  all_goals
    simp only [List.length_drop, List.length_cons]
    omega

/-- Unfold the first chunk of a list with length at least `n`. -/
theorem toChunks_cons_step {α : Type _} (n : Nat) (hn : 0 < n) (L : List α)
    (hLen : n ≤ L.length) :
    listChunks n L = (L.take n) :: listChunks n (L.drop n) := by
  cases n with
  | zero => omega
  | succ width =>
    cases L with
    | nil => simp at hLen
    | cons item rest =>
      change listChunks.go width (item :: rest) #[] =
        (item :: rest.take width) :: listChunks (width + 1) (rest.drop width)
      rw [listChunks.go, List.splitAt_eq, toChunks_go_append_finished]
      simp only [Array.toList_push, List.nil_append, List.singleton_append]
      cases rest.drop width <;> simp [listChunks, listChunks.go]

/-- When the list length is a multiple of the chunk width, each chunk is a full slice. -/
theorem toChunks_eq_drop_take {α : Type _} (n : Nat) (hn : 0 < n) (L : List α)
    (k : Nat) (hLen : L.length = n * k) :
    listChunks n L = (List.range k).map (fun i => (L.drop (i*n)).take n) := by
  induction k generalizing L with
  | zero =>
    have h0 : L.length = 0 := by simpa using hLen
    have : L = [] := List.length_eq_zero_iff.mp h0
    subst this
    simp [listChunks]
  | succ k ih =>
    have hLen' : n ≤ L.length := by rw [hLen, Nat.mul_succ]; omega
    rw [toChunks_cons_step n hn L hLen']
    have hDrop : (L.drop n).length = n * k := by
      rw [List.length_drop, hLen, Nat.mul_succ]; omega
    rw [ih (L.drop n) hDrop]
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map]
    congr 1
    · simp
    apply List.map_congr_left
    intro i _
    simp only [Function.comp]
    rw [show (i + 1) * n = n + i * n from by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]]
    rw [← List.drop_drop]

end SHS.Equiv.Chunks
