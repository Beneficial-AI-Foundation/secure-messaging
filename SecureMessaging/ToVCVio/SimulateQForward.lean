/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.ProbComp

/-!
# Forwarding a lifted base computation through an identity-left `add` handler (missing VCVio brick)

A reduction's oracle handler is often an `add` of an *identity* handler on the base spec
(`unifSpec`) and a "real" handler on the forwarded spec. When such a handler is `simulateQ`'d on a
computation that lives purely on the base spec (lifted in via `liftComp`/`liftM`), the real handler
is never consulted and the computation passes through unchanged.

This is the engine behind the EtM proof's repeated `hfwd` helpers (the IND$-CPA reduction's
`oracleEncrypt` forwarder in both the `hg3` and `hg2` enc-hop sub-proofs). It is a thin packaging of
`QueryImpl.simulateQ_add_liftComp_left` + `simulateQ_id'`.

TODO(upstream): contribute to VCVio alongside `OracleComp/SimSemantics/Append.lean`.
-/

open OracleComp OracleSpec

namespace ToVCVio

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
  rw [show (liftM ob : OracleComp (unifSpec + specR) β)
        = OracleComp.liftComp ob (unifSpec + specR) from rfl,
      QueryImpl.simulateQ_add_liftComp_left]
  simp

end ToVCVio
