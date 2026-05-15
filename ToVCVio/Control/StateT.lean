import ToMathlib.Control.StateT

/-!
# `StateT.run` lemmas

Rewrites for `StateT` computations of the form `do let s ← get; …`.
-/

namespace StateT

universe u v

variable {m : Type u → Type v} {σ α : Type u}

/-- For `f : σ → StateT σ m α` (a pure function returning a stateful
computation), `(do let t ← get; f t).run s = (f s).run s`. Step by step:

1. Both sides start running from state `s : σ`.
2. `let t ← get` binds `t : σ` to the current state, which is `s`, so `t = s`.
3. The pure substitution `f t = f s` then yields the monadic computation
   `f s : StateT σ m α`, which runs from `s` — i.e. the RHS.

Fuses `StateT.run_bind`, `StateT.run_get`, and `pure_bind` into one
simp-rewrite. -/
@[simp]
lemma run_get_bind [Monad m] [LawfulMonad m]
    (f : σ → StateT σ m α) (s : σ) :
    (do let t ← (get : StateT σ m σ); f t).run s = (f s).run s := by
  simp [StateT.run_bind, StateT.run_get]

/-- For `cond s = false`,
`(do let t ← get; if cond t then thenBranch t else elseBranch).run s =`
`elseBranch.run s`.
Discharges the false branch when rewriting state-conditional `StateT`
computations. -/
lemma run_get_bind_ite_eq_else_of_pred_false [Monad m] [LawfulMonad m]
    (cond : σ → Bool) (thenBranch : σ → StateT σ m α) (elseBranch : StateT σ m α)
    (s : σ) (h_pred : cond s = false) :
    (do let t ← (get : StateT σ m σ);
        if cond t then thenBranch t else elseBranch).run s =
      elseBranch.run s := by
  rw [run_get_bind]
  simp [h_pred]

end StateT
