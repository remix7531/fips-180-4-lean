/-! # Interleaving a schedule fold with a round fold -/

namespace SHS.Equiv.FusedFold

/-- Updating the schedule and running each round in turn agrees with running the rounds
against the completed schedule when updates preserve earlier round inputs. -/
theorem foldl_update_then_round {Schedule State : Type _}
    (update : Nat → Schedule → Schedule) (round : Schedule → Nat → State → State)
    (earlier_round : ∀ (schedule : Schedule) (written read : Nat) (state : State),
      read < written → round (update written schedule) read state = round schedule read state)
    (n : Nat) (initialSchedule : Schedule) (initialState : State) :
    let finalSchedule := Fin.foldl n (fun schedule i => update i.val schedule) initialSchedule
    Fin.foldl n (fun (acc : Schedule × State) i =>
      let schedule := update i.val acc.1
      (schedule, round schedule i.val acc.2)) (initialSchedule, initialState) =
      (finalSchedule, Fin.foldl n (fun state i => round finalSchedule i.val state)
        initialState) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ k ih =>
    simp only [Fin.foldl_succ_last, Fin.val_castSucc, Fin.val_last]
    rw [ih]
    let partialSchedule := Fin.foldl k (fun schedule i => update i.val schedule) initialSchedule
    have earlierFold :
        Fin.foldl k (fun state i => round (update k partialSchedule) i.val state) initialState =
          Fin.foldl k (fun state i => round partialSchedule i.val state) initialState := by
      refine congrArg (fun step => Fin.foldl k step initialState) ?_
      funext state i
      exact earlier_round partialSchedule k i.val state i.isLt
    rw [earlierFold]

end SHS.Equiv.FusedFold
