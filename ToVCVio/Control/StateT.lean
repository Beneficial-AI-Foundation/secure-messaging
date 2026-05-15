import ToMathlib.Control.StateT

/-!
# `StateT.run` rewrites

Small rewrites for `StateT` computations that first read the current state with
`get`, then choose the rest of the computation from that state.
-/

namespace StateT

universe u v

variable {m : Type u → Type v} {σ α : Type u}

/-- Reading the current state before choosing the next `StateT` computation
substitutes the initial state: `(do let t ← get; f t).run s = (f s).run s`.

This packages the common `StateT.run_bind`/`StateT.run_get` simplification. -/
@[simp]
lemma run_get_bind [Monad m] [LawfulMonad m]
    (f : σ → StateT σ m α) (s : σ) :
    (do let t ← (get : StateT σ m σ); f t).run s = (f s).run s := by
  simp [StateT.run_bind, StateT.run_get]

/-- If a state-dependent guard is false at the initial state, the computation
that first reads the state and branches on the guard reduces to the else branch. -/
lemma run_get_bind_ite_eq_else_of_pred_false [Monad m] [LawfulMonad m]
    (cond : σ → Bool) (thenBranch : σ → StateT σ m α) (elseBranch : StateT σ m α)
    (s : σ) (h_pred : cond s = false) :
    (do let t ← (get : StateT σ m σ);
        if cond t then thenBranch t else elseBranch).run s =
      elseBranch.run s := by
  rw [run_get_bind]
  simp [h_pred]

end StateT
