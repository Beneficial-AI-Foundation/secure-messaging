/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OnlineOracle
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OfflineSampling
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.KeygenSampling
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.UnusedMaterial

/-!
# From pinned hybrids to ordinary auxiliary executions

**Statement.** Assume deterministic decapsulation and correct erasure
codes. For every selected epoch, mode, and adversary, averaging complete
material in the stopped pinned hybrid gives the stopped ordinary auxiliary
experiment with the same challenge mode.

**Proof.** Expand `sampleMaterial` into key generation, offline sampling,
and online sampling at their sampled inputs. Defer these in reverse order:
`OnlineOracle`, `OfflineSampling`, and `KeygenSampling` justify the three
steps. The fully fresh stage is the ordinary auxiliary oracle. This removes
all supplied private material from the hybrid comparison.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Assume deterministic decapsulation and correct erasure codes. For every
selected epoch, mode, adversary, and arbitrary reference material `m₀`,
averaging the stopped pinned hybrid over complete material gives exactly
the stopped fully fresh stage from the protocol's initial state. -/
theorem pinnedHybrid_eq_fresh
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (m₀ : Material leak) (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym) :
    Pr[= true | do
      let m ← sampleMaterial leak
      optionRun (hybridStopped base onoff ecEk ecCt0 ecCt1 leak m e b) adv
        (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] =
    Pr[= true | optionRun
      (Sampling.stopped base onoff ecEk ecCt0 ecCt1 leak .fresh m₀ e b) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] := by
  trans Pr[= true | do
    let kg ← leak.keygenRleak
    let off ← leak.encapsOffRleak
    optionRun (Sampling.stopped base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { m₀ with keygen := kg, off := off } e b) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff)]
  · simp only [sampleMaterial, bind_assoc, pure_bind]
    apply probOutput_bind_congr
    intro kg hkg
    apply probOutput_bind_congr
    intro off hoff
    obtain ⟨online, hon⟩ : (support (leak.encapsOnRleak off.1.1 kg.1.1)).Nonempty := by
      simp [Set.nonempty_iff_ne_empty, ← probFailure_eq_one_iff]
    let m : Material leak := ⟨kg, off, online⟩
    have hm : m ∈ support (sampleMaterial leak) := by
      simp only [sampleMaterial, mem_support_bind_iff, mem_support_pure_iff]
      exact ⟨kg, hkg, off, hoff, online, hon, rfl⟩
    exact hybridStopped_online_deferred base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak m hm e b adv _
      (reachableInv_init base onoff ecEk ecCt0 ecCt1 ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos)
      (pinnedSources_initial base onoff leak m e)
  trans Pr[= true | do
    let kg ← leak.keygenRleak
    optionRun (Sampling.stopped base onoff ecEk ecCt0 ecCt1 leak
      .encapsFresh { m₀ with keygen := kg } e b) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff)]
  · apply probOutput_bind_congr
    intro kg _
    exact Sampling.stopped_offline_deferred base onoff ecEk ecCt0 ecCt1 leak
      { m₀ with keygen := kg } e b adv _
  · exact Sampling.stopped_keygen_deferred base onoff ecEk ecCt0 ecCt1 leak m₀ e b adv _

/-- Assume deterministic decapsulation and correct erasure codes. For every
selected epoch, mode, and adversary, the material-averaged stopped pinned
hybrid equals the stopped auxiliary oracle with mode `adjacentMode e b`. -/
theorem pinnedHybrid_eq_auxiliary
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff) (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym) :
    Pr[= true | do
      let m ← sampleMaterial leak
      optionRun (hybridStopped base onoff ecEk ecCt0 ecCt1 leak m e b) adv
        (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] =
    Pr[= true | optionRun
      (stopOnState (idealSecurityImpl base onoff hDet ecEk ecCt0 ecCt1 leak (adjacentMode e b))
        (fun s => decide (e ∈ s.exposed))) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] := by
  obtain ⟨m₀, _⟩ : (support (sampleMaterial leak)).Nonempty := by
    simp [Set.nonempty_iff_ne_empty, ← probFailure_eq_one_iff]
  rw [pinnedHybrid_eq_fresh base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak m₀ e b adv]
  unfold Sampling.stopped
  rw [Sampling.oracle_fresh_eq_ideal base onoff hDet ecEk ecCt0 ecCt1 leak m₀ e b]

/-- Assume deterministic decapsulation and correct erasure codes. For every
positive selected epoch `e`, adversary, and KEM branch bit `b`, the explicit
reduction's branch has the acceptance probability of the stopped auxiliary
hybrid with mode `adjacentMode e (!b)`. The negation converts the KEM bit
convention (true means real) to the SCKA convention (true means random). -/
theorem fixedBranch_eq_auxiliary
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff) (e : ℕ) (he : 0 < e)
    (b : Bool) (adv : SecurityAdversary leak Sym) :
    Pr[= true | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv e b] =
    Pr[= true | optionRun
      (stopOnState (idealSecurityImpl base onoff hDet ecEk ecCt0 ecCt1 leak
        (adjacentMode e (!b))) (fun s => decide (e ∈ s.exposed))) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] := by
  rw [fixedBranch_eq_pinnedHybrid base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak adv e he b]
  exact pinnedHybrid_eq_auxiliary base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak e (!b) adv

end oppUniKemCKA.Security.Embedding
