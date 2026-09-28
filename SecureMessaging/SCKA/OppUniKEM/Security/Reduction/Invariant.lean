/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Support
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OracleReceive

/-!
# Transcript invariant for the honest intermediate game

**Assumptions.** Fix supported material `m`, selected epoch `e`, supplied
challenge key `kStar`, deterministic decapsulation, and correct erasure codes.

**Statement.** Every query preserves the conjunction of `reachableInv`
and `pinnedSources m e`. Thus the intermediate game has an honest transcript
whose selected source fields equal the fixed material whenever present.

**Proof.** Pinned sends have ordinary supported outputs, so the correctness
send lemmas apply. A receives with B's recorded key; the auxiliary receive
lemma preserves the transcript. B uses its original receive. Leaking sends
inherit preservation through their marginals, and challenges and corruptions
change only security bookkeeping. `SourcePreservation` supplies preservation
of the fixed source fields.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym]

/-- Assume supported material and correct erasure codes. For every state
satisfying transcript consistency and the fixed-source invariant, every
supported correctness-interface query in the pinned game preserves the
original transcript invariant. -/
theorem honestCorrectness_preserves_reachableInv
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s)
    (z : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.sckaCorrectnessImpl (honestScheme ecEk ecCt0 ecCt1 m e s) t).run s)) :
    reachableInv base onoff ecEk ecCt0 ecCt1 z.2 := by
  rcases t with ((((n | u) | u) | n) | n)
  · exact oracleUnif_preserves_reachableInv base onoff ecEk ecCt0 ecCt1 n s hs z hz
  · cases u
    exact oracleSendA_preserves_reachableInv base onoff hDet ecEk ecCt0 ecCt1 leak
      ecEk.ec.nchunk_pos () s hs z
      (oracleSendA_pinned_support base onoff hDet ecEk ecCt0 ecCt1 leak m hm e s z hz)
  · cases u
    exact oracleSendB_preserves_reachableInv base onoff hDet ecEk ecCt0 ecCt0.ec.nchunk_pos
      ecCt1 ecCt1.ec.nchunk_pos leak () s hs z
      (oracleSendB_pinned_support base onoff hDet ecEk ecCt0 ecCt1 leak
        m hm e s hs hsrc z hz)
  · apply oracleRecvAIdeal_preserves_reachableInv base onoff ecEk ecCt0 hCt0
      ecCt1 hCt1 leak n s hs z
    have heq :
        (SCKAScheme.oracleRecvA (honestScheme ecEk ecCt0 ecCt1 m e s) n).run s =
        (oracleRecvAIdeal base onoff ecEk ecCt0 ecCt1 leak n).run s := by
      change (SCKAScheme.oracleRecvA _ n).run s =
        (SCKAScheme.oracleRecvA (scheme (keyDecapsKEM base (s.keyB s.stA.t))
          (keyDecapsOnOff base onoff (s.keyB s.stA.t))
          (keyDecapsDet base (s.keyB s.stA.t)) ecEk ecCt0 ecCt1
          (keyDecapsLeak base onoff leak (s.keyB s.stA.t))) n).run s
      simp only [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind]
      cases hm : s.msgB n with
      | none => simp only
      | some entry =>
        rcases entry with ⟨msg, t⟩
        simp only
        rw [honest_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak m e s msg]
        rfl
    exact heq ▸ hz
  · exact oracleRecvB_preserves_reachableInv base onoff hDet ecEk hEk ecEk.ec.nchunk_pos
      ecCt0 ecCt1 leak n s hs z hz

/-- Assume supported material and correct erasure codes. For every challenge
key and full security query, transcript consistency and the source invariant
at the input imply transcript consistency at every supported successor. -/
theorem honestOracle_preserves_reachableInv [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ) (kStar : K)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s)
    (z : (securitySpec leak Sym).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((honestOracle base onoff ecEk ecCt0 ecCt1 leak m e kStar t).run s)) :
    reachableInv base onoff ecEk ecCt0 ecCt1 z.2 := by
  have hbook := fun state exposed (h : reachableInv base onoff ecEk ecCt0 ecCt1 state) =>
    reachableInv_with_security_bookkeeping h exposed state.challenged
  simp only [honestOracle, StateT.run_bind, StateT.run_get, pure_bind] at hz
  rcases t with (((((t | u) | u) | t) | u) | u)
  · exact honestCorrectness_preserves_reachableInv base onoff hDet ecEk hEk
      ecCt0 hCt0 ecCt1 hCt1 leak m hm e t s hs hsrc z hz
  · cases u
    apply SCKAScheme.oracleSendArleak_preservesInv_at
      (honestScheme ecEk ecCt0 ecCt1 m e s) sendExposureA _
      (reachableInv base onoff ecEk ecCt0 ecCt1) hbook s hs _ z hz
    · exact sendArleak_forget _ _ _ _
    · exact honestCorrectness_preserves_reachableInv base onoff hDet ecEk hEk
        ecCt0 hCt0 ecCt1 hCt1 leak m hm e SCKAScheme.sckaCorrectnessSpec.OSendA s hs hsrc
  · cases u
    apply SCKAScheme.oracleSendBrleak_preservesInv_at
      (honestScheme ecEk ecCt0 ecCt1 m e s) sendExposureB _
      (reachableInv base onoff ecEk ecCt0 ecCt1) hbook s hs _ z hz
    · exact sendBrleak_forget _ _ _ _ _
    · exact honestCorrectness_preserves_reachableInv base onoff hDet ecEk hEk
        ecCt0 hCt0 ecCt1 hCt1 leak m hm e SCKAScheme.sckaCorrectnessSpec.OSendB s hs hsrc
  · simp only [pinnedChallenge, StateT.run_bind, StateT.run_get, pure_bind] at hz
    repeat' split at hz
    all_goals
      simp only [StateT.run_pure, StateT.run_bind, StateT.run_map, StateT.run_set,
        StateT.run_monadLift, monadLift_self, bind_pure_comp, map_pure, Functor.map_map,
        mem_support_pure_iff, support_map, support_uniformSample,
        Set.image_univ, Set.mem_range] at hz
    all_goals
      first
      | obtain rfl := hz
      | obtain ⟨_, rfl⟩ := hz
    all_goals
      first
      | exact hs
      | exact reachableInv_with_security_bookkeeping hs _ _
  · exact SCKAScheme.oracleCorruptA_preservesInv (vulnA base onoff)
      (reachableInv base onoff ecEk ecCt0 ecCt1) hbook u s hs z hz
  · exact SCKAScheme.oracleCorruptB_preservesInv (vulnB base onoff)
      (reachableInv base onoff ecEk ecCt0 ecCt1) hbook u s hs z hz

/-- For every supported material value, epoch, and supplied challenge key,
the honest intermediate game preserves transcript consistency together
with `pinnedSources`, assuming deterministic decapsulation and correct
erasure codes. -/
theorem honestOracle_preserves_simulationInv [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ) (kStar : K) :
    QueryImpl.PreservesInv (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e kStar)
      (fun s => reachableInv base onoff ecEk ecCt0 ecCt1 s ∧ pinnedSources m e s) := by
  intro t s hs z hz
  exact ⟨honestOracle_preserves_reachableInv base onoff hDet ecEk hEk ecCt0 hCt0
    ecCt1 hCt1 leak m hm e kStar t s hs.1 hs.2 z hz,
    honestOracle_preserves_pinnedSources base onoff ecEk ecCt0 ecCt1 leak
      m e kStar t s hs.2 z hz⟩

end oppUniKemCKA.Security.Embedding
