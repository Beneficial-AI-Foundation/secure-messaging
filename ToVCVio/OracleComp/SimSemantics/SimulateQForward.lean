/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.ProbComp
import ToMathlib.Control.StateT

/-!
# Forwarding a lifted base computation through an identity-left `add` handler

A reduction's oracle handler is often an `add` of an *identity* handler on the base spec
(`unifSpec`) and a "real" handler on the forwarded spec. When such a handler is `simulateQ`'d on a
computation living purely on the base spec (lifted in via `liftComp`/`liftM`), the real handler is
never consulted and the computation passes through unchanged.

`simulateQ_id'_liftTarget_add_liftComp` packages VCVio's `QueryImpl.simulateQ_add_liftM_left` into
the exact `liftM`-base shape the EtM enc-hop forwarders consume (the upstream lemma does not match
syntactically: the lifted query enters the combined spec in one step, not as a lift of an
`OracleComp unifSpec`).
-/

open OracleComp OracleSpec

namespace OracleComp

/-- Forwarding through an identity-left `add` handler: `simulateQ` of
`(id' unifSpec).liftTarget _ + h`
on a base-spec computation `ob` lifted into `unifSpec + specR` returns `ob` lifted into the state
monad — the right handler `h` is never consulted. -/
theorem simulateQ_id'_liftTarget_add_liftComp
    {ιR : Type} {specR : OracleSpec ιR} {τ : Type}
    (h : QueryImpl specR (StateT τ ProbComp)) {β : Type} (ob : ProbComp β) :
    simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT τ ProbComp) + h)
        (liftM ob : OracleComp (unifSpec + specR) β)
      = (liftM ob : StateT τ ProbComp β) := by
  simp [QueryImpl.simulateQ_add_liftM_left]

/-- Forward a base computation lifted through an inner `StateT` and run at state `s`. -/
theorem simulateQ_id'_liftTarget_add_run_liftComp
    {ιR : Type} {specR : OracleSpec ιR} {σ τ : Type}
    (h : QueryImpl specR (StateT τ ProbComp)) {β : Type} (ob : ProbComp β) (s : σ) :
    simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT τ ProbComp) + h)
        ((liftM ob : StateT σ (OracleComp (unifSpec + specR)) β).run s)
      = (liftM ((fun x => (x, s)) <$> ob) : StateT τ ProbComp (β × σ)) := by
  have hrun :
      (liftM ob : StateT σ (OracleComp (unifSpec + specR)) β).run s =
        (liftM ((fun x => (x, s)) <$> ob) : OracleComp (unifSpec + specR) (β × σ)) := by
    change (liftM (liftM ob : StateT σ ProbComp β) :
      StateT σ (OracleComp (unifSpec + specR)) β).run s = _
    simp [StateT.run_monadLift, map_eq_bind_pure_comp]
  rw [hrun]
  exact simulateQ_id'_liftTarget_add_liftComp h ((fun x => (x, s)) <$> ob)

end OracleComp
