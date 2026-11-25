/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# State maps through `QueryImpl.extendState`

`QueryImpl.extendState so aux` runs `so` on a base state and updates an auxiliary component with
`aux`. If a map `φ` of base states carries the steps of `so₁` to the steps of `so₂`, and the two
updates `aux₁` and `aux₂` agree along `φ`, then `φ` on the base component carries the steps of
the extended implementations (`extendState_run_map_eq`). Every outcome of an extended step is
an outcome of the base step with the update (`mem_support_extendState_run`).
-/

@[expose] public section

namespace QueryImpl

universe u v

variable {ι : Type u} {spec : OracleSpec ι} {σ τ Q : Type u} {m : Type u → Type v} [Monad m]
  [LawfulMonad m]

/-- Let `φ` carry the step of `so₁` from `s` to the step of `so₂` from `φ s`, and let the updates
agree along `φ`. Then `φ` on the base component carries the extended step from `(s, q)` to the
extended step from `(φ s, q)`. -/
theorem extendState_run_map_eq (so₁ : QueryImpl spec (StateT σ m))
    (so₂ : QueryImpl spec (StateT τ m))
    (aux₁ : (t : spec.Domain) → σ → spec.Range t → σ → Q → Q)
    (aux₂ : (t : spec.Domain) → τ → spec.Range t → τ → Q → Q) (φ : σ → τ)
    (t : spec.Domain) (s : σ) (q : Q)
    (h : Prod.map id φ <$> (so₁ t).run s = (so₂ t).run (φ s))
    (haux : ∀ u s', aux₂ t (φ s) u (φ s') q = aux₁ t s u s' q) :
    Prod.map id (Prod.map φ id) <$> ((so₁.extendState aux₁) t).run (s, q) =
      ((so₂.extendState aux₂) t).run (φ s, q) := by
  simp only [extendState_apply, ← h, map_bind, map_pure, bind_map_left, Prod.map_fst,
    Prod.map_snd, id_eq, haux]
  rfl

/-- Every outcome of an extended step from `(s, q)` is an outcome `y` of the base step from `s`,
with the update `aux` on the auxiliary component. -/
theorem mem_support_extendState_run {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ Q : Type} (so : QueryImpl spec (StateT σ (OracleComp spec')))
    (aux : (t : spec.Domain) → σ → spec.Range t → σ → Q → Q) (t : spec.Domain) (s : σ) (q : Q)
    {z} (hz : z ∈ support ((so.extendState aux t).run (s, q))) :
    ∃ y ∈ support ((so t).run s), z = (y.1, (y.2, aux t s y.1 y.2 q)) := by
  rw [QueryImpl.extendState_apply] at hz
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hz
  exact hz

end QueryImpl
