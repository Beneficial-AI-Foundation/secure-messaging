/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.SourceUse
import SecureMessaging.SCKA.Security.LeakageGuard

/-!
# Success of local sends in the sampling games

For every KEM and local state, each ordinary or leaking Opp-UniKEM send
returns a successful local output. Game-level leakage guards may still
reject that output. This distinction lets the one-use proof show that an
ordinary first send installs its source sample, while an accepted leaking
first send exposes the selected epoch and terminates the stopped game.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}

/-- For every KEM and local A-state, `none` has zero support
in the ordinary send computation: each branch returns a protocol output. -/
theorem sendA_none_not_mem_support
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (s : StA onoff Sym) :
    none ∉ support (sendA base onoff ecEk s) := by
  cases hd : s.dkA <;> cases hp : s.ekA <;> cases ha : s.ack.ekRec <;>
    simp [sendA, hd, hp, ha]

/-- For every KEM and leakage witness and local A-state, `none` has zero support
in the leaking send computation: each branch returns a protocol output. -/
theorem sendArleak_none_not_mem_support
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (leak : base.OnOffRandLeak onoff)
    (s : StA onoff Sym) :
    none ∉ support (sendArleak base onoff ecEk leak s) := by
  cases hd : s.dkA <;> cases hp : s.ekA <;> cases ha : s.ack.ekRec <;>
    simp [sendArleak, hd, hp, ha]

/-- For every KEM and local B-state, `none` has zero support
in the ordinary send computation: each branch returns a protocol output. -/
theorem sendB_none_not_mem_support
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : StB onoff Sym) :
    none ∉ support (sendB base onoff ecCt0 ecCt1 s) := by
  cases hc0 : s.ct0 <;> cases hp : s.ekA <;> cases hc1 : s.ct1 <;>
    cases hst : s.stCt <;> cases ha : s.ack.ctRec <;>
    simp [sendB, hc0, hp, hc1, hst, ha]

/-- For every KEM and leakage witness and local B-state, `none` has zero support
in the leaking send computation: each branch returns a protocol output. -/
theorem sendBrleak_none_not_mem_support
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : base.OnOffRandLeak onoff)
    (s : StB onoff Sym) :
    none ∉ support (sendBrleak base onoff ecCt0 ecCt1 leak s) := by
  cases hc0 : s.ct0 <;> cases hp : s.ekA <;> cases hc1 : s.ct1 <;>
    cases hst : s.stCt <;> cases ha : s.ack.ctRec <;>
    simp [sendBrleak, hc0, hp, hc1, hst, ha]

end oppUniKemCKA.Security.Embedding.Sampling
