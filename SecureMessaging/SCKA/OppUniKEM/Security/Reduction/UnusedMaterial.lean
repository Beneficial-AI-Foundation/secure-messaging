/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.SamplingStages

/-!
# Material discarded by fresh sampling stages

A sampling stage reads only the components that it pins. Once online
sampling is fresh, the stored online output has no effect on any query.
Once both encapsulation phases are fresh, the stored offline output is
irrelevant as well. These equalities remove unused components when combining
the three phase-deferral results under `sampleMaterial`.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For every epoch and mode, changing only the stored online component
leaves the entire `onlineFresh` oracle implementation unchanged. -/
theorem oracle_onlineFresh_on_irrelevant
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool) (online : (onoff.C₁ × K) × leak.OnRand) :
    oracle base onoff ecEk ecCt0 ecCt1 leak .onlineFresh { m with on := online } e b =
      oracle base onoff ecEk ecCt0 ecCt1 leak .onlineFresh m e b := by
  rfl

/-- For every epoch and mode, changing only the stored offline component
leaves the entire `encapsFresh` oracle implementation unchanged. -/
theorem oracle_encapsFresh_off_irrelevant
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool) (offline : (onoff.St × onoff.C₀) × leak.OffRand) :
    oracle base onoff ecEk ecCt0 ecCt1 leak .encapsFresh { m with off := offline } e b =
      oracle base onoff ecEk ecCt0 ecCt1 leak .encapsFresh m e b := by
  rfl

/-- For every epoch and mode, changing only the stored online component
leaves the entire `encapsFresh` oracle implementation unchanged. -/
theorem oracle_encapsFresh_on_irrelevant
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool) (online : (onoff.C₁ × K) × leak.OnRand) :
    oracle base onoff ecEk ecCt0 ecCt1 leak .encapsFresh { m with on := online } e b =
      oracle base onoff ecEk ecCt0 ecCt1 leak .encapsFresh m e b := by
  rfl

end oppUniKemCKA.Security.Embedding.Sampling
