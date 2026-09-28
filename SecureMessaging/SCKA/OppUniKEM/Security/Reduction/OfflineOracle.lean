/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OfflineFresh

/-!
# Offline sampling in the full security oracle

For every query and input state, averaging the selected offline material
in the `onlineFresh` stage gives the query distribution of `encapsFresh`.
B's sends use the local comparisons in `OfflineFresh`; the remaining game
operations have the same computation for every offline sample. Both games
retain the leakage guard and apply identical response/state bookkeeping.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For every query, material value, selected epoch, mode, and input state,
averaging offline material in the `onlineFresh` stage gives the joint
response/state distribution of the `encapsFresh` stage. -/
theorem oracle_sample_offline_eq_fresh
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    𝒟[(do
      let offline ← leak.encapsOffRleak
      (Sampling.oracle base onoff ecEk ecCt0 ecCt1 leak
        .onlineFresh { m with off := offline } e b t).run s)] =
    𝒟[(Sampling.oracle base onoff ecEk ecCt0 ecCt1 leak .encapsFresh m e b t).run s] := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · apply evalDist_ext
      intro z
      apply ToVCVio.probOutput_bind_of_const'
      intro offline _
      rfl
    · cases u
      simp only [Sampling.oracle,
        StateT.run_bind, StateT.run_get, pure_bind, SCKAScheme.sckaCorrectnessImpl,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      apply SCKAScheme.oracleSendA_sample_eq
      apply evalDist_ext
      intro z
      apply ToVCVio.probOutput_bind_of_const'
      intro offline _
      rfl
    · cases u
      simp only [Sampling.oracle,
        StateT.run_bind, StateT.run_get, pure_bind, SCKAScheme.sckaCorrectnessImpl,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      exact SCKAScheme.oracleSendB_sample_eq _ _ _ s
        (sendB_sample_offline_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s)
    · apply evalDist_ext
      intro z
      apply ToVCVio.probOutput_bind_of_const'
      intro offline _
      simp only [Sampling.oracle,
        StateT.run_bind, StateT.run_get, pure_bind, SCKAScheme.sckaCorrectnessImpl,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, SCKAScheme.oracleRecvA]
      cases hm : s.msgB n with
      | none => rfl
      | some out =>
        rcases out with ⟨msg, epoch⟩
        simp only
        rw [Sampling.recvA_eq_auxiliary base onoff ecEk ecCt0 ecCt1 leak .onlineFresh
          { m with off := offline } e s msg,
          Sampling.recvA_eq_auxiliary base onoff ecEk ecCt0 ecCt1 leak .encapsFresh m e s msg]
    · apply evalDist_ext
      intro z
      apply ToVCVio.probOutput_bind_of_const'
      intro offline _
      rfl
  · cases u
    simp only [Sampling.oracle,
      StateT.run_bind, StateT.run_get, pure_bind, Sampling.sendExposureA_eq]
    apply SCKAScheme.oracleSendArleak_sample_eq
    apply evalDist_ext
    intro z
    apply ToVCVio.probOutput_bind_of_const'
    intro offline _
    rfl
  · cases u
    simp only [Sampling.oracle,
      StateT.run_bind, StateT.run_get, pure_bind, Sampling.sendExposureB_eq]
    exact SCKAScheme.oracleSendBrleak_sample_eq _ _ _ _ s
      (sendBrleak_sample_offline_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s)
  all_goals
    apply evalDist_ext
    intro z
    apply ToVCVio.probOutput_bind_of_const'
    intro offline _
    rfl

end oppUniKemCKA.Security.Embedding
