/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Game
import SecureMessaging.SCKA.Security.Bookkeeping
import ToVCVio.OracleComp.QueryTracking.OneUseSampling

/-!
# Deferring the selected challenge key

**Parameters.** Fix selected epoch `e`, complete material `m`, a key sampler
`sample : ProbComp K`, and any adversary against the full security interface.

**Statement.** In the stopped honest intermediate game, drawing the supplied
challenge key once before execution has the same acceptance probability as
drawing it afresh at every query.

**Proof.** Only an eligible, available challenge at `e` reads the supplied
key. That query records `e` in `challenged`, and every subsequent query
preserves this membership. Thus the supplied key is read at most once.
The generic single-use sampling theorem applies to every initial state,
including those where the selected challenge is already exposed or answered.
-/

open OracleSpec OracleComp KEMScheme
open SCKAScheme.sckaSecuritySpec

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Test whether a query uses the selected challenge key: it must challenge
epoch `e`, pass both exposure and repetition guards, and have an available
recorded key at either party. -/
def usesChallengeKey {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (e : ℕ) (query : (SCKAScheme.sckaSecuritySpec Unit Unit Unit Unit Unit).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) : Bool :=
  match query with
  | OChall t => decide (t = e ∧ e ∉ s.exposed ∧ e ∉ s.challenged ∧
      ((s.keyA e).isSome ∨ (s.keyB e).isSome))
  | _ => false

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
variable (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
variable (ecEk : ErasureCodePayload PK Sym)
variable (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
variable (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)

/-- For every material value, selected epoch, supplied key, and epoch `u`,
each honest intermediate query preserves membership of `u` in `challenged`. -/
theorem honestOracle_preserves_challenged (m : Material leak) (e : ℕ) (kStar : K) (u : ℕ) :
    QueryImpl.PreservesInv (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e kStar)
      (fun s => u ∈ s.challenged) := by
  intro t s hs z hz
  simp only [honestOracle, StateT.run_bind, StateT.run_get, pure_bind] at hz
  rcases t with (((((t | a) | a) | t) | a) | a)
  · have h := (SCKAScheme.correctnessImpl_securitySets_eq _ t s z hz).2
    simpa only [h] using hs
  · have h := SCKAScheme.oracleSendArleak_challenged_eq sendExposureA _ a s z hz
    simpa only [h] using hs
  · have h := SCKAScheme.oracleSendBrleak_challenged_eq sendExposureB _ a s z hz
    simpa only [h] using hs
  · exact pinnedChallenge_preserves_challenged onoff e kStar u t s hs z hz
  · exact SCKAScheme.oracleCorruptA_preservesInv (vulnA base onoff)
      (fun s => u ∈ s.challenged) (fun _ _ h => h) a s hs z hz
  · exact SCKAScheme.oracleCorruptB_preservesInv (vulnB base onoff)
      (fun s => u ∈ s.challenged) (fun _ _ h => h) a s hs z hz

/-- For every query and state whose selected-challenge use test is false,
the honest intermediate query computation is equal for all supplied keys. -/
theorem honestOracle_eq_of_unused (m : Material leak) (e : ℕ) (k k' : K)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (h : usesChallengeKey e t s = false) :
    (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e k t).run s =
      (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e k' t).run s := by
  rcases t with (((((t | a) | a) | t) | a) | a)
  all_goals try rfl
  simp only [honestOracle, StateT.run_bind, StateT.run_get, pure_bind]
  exact pinnedChallenge_eq_of_unused onoff e t k k' s (of_decide_eq_false h)

/-- For every query and state whose selected-challenge use test is true,
every supported honest successor records the selected epoch in `challenged`. -/
theorem honestOracle_use_records_challenge (m : Material leak) (e : ℕ) (k : K)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (h : usesChallengeKey e t s = true)
    (z : (securitySpec leak Sym).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((honestOracle base onoff ecEk ecCt0 ecCt1 leak m e k t).run s)) :
    e ∈ z.2.challenged := by
  rcases t with (((((t | a) | a) | t) | a) | a)
  all_goals try simp only [usesChallengeKey, Bool.false_eq_true, decide_eq_true_eq] at h
  have h' : t = e ∧ e ∉ s.exposed ∧ e ∉ s.challenged ∧
      ((s.keyA e).isSome ∨ (s.keyB e).isSome) := h
  obtain ⟨ht, he, hc, hk⟩ := h'
  subst t
  simp only [honestOracle, StateT.run_bind, StateT.run_get, pure_bind] at hz
  rw [pinnedChallenge_selected onoff e k s (by simp [he, hc]) hk] at hz
  obtain rfl := (mem_support_pure_iff _ _).mp hz
  exact Finset.mem_insert_self _ _

/-- For every material value `m`, selected epoch `e`, sampler `sample`,
adversary `adv`, and initial state `s`, eager sampling of the supplied key
and resampling it at each stopped honest query give equal acceptance
probabilities. Each execution reads that key at most once. -/
theorem honestStopped_sample_key_eq (m : Material leak) (e : ℕ) (sample : ProbComp K)
    (adv : SecurityAdversary leak Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    Pr[= true | do
      let k ← sample
      optionRun (honestStopped base onoff ecEk ecCt0 ecCt1 leak m e k) adv s] =
    Pr[= true | optionRun
      (sampleEachQuery sample (honestStopped base onoff ecEk ecCt0 ecCt1 leak m e)) adv s] := by
  let : Inhabited K := Classical.inhabited_of_nonempty inferInstance
  apply optionRun_sample_once_eq_sampleEachQuery sample
    (honestStopped base onoff ecEk ecCt0 ecCt1 leak m e)
    (fun _ => True) (fun s => e ∈ s.challenged) (usesChallengeKey e)
  · intros; trivial
  · intro k t s _ hs z hz _
    change z ∈ support (do
      let out ← (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e k t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hz
    obtain ⟨out, hout, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    obtain rfl := (mem_support_pure_iff _ _).mp hz
    exact honestOracle_preserves_challenged base onoff ecEk ecCt0 ecCt1 leak m e k e
      t s hs out hout
  · intro t s _ h k k'
    change (do
      let out ← (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e k t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) = _
    rw [honestOracle_eq_of_unused base onoff ecEk ecCt0 ecCt1 leak m e k k' t s h]
    rfl
  · intro t s _ hs
    rcases t with (((((t | a) | a) | t) | a) | a)
    all_goals simp [usesChallengeKey, hs]
  · intro k t s _ h z hz _
    change z ∈ support (do
      let out ← (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e k t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hz
    obtain ⟨out, hout, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    obtain rfl := (mem_support_pure_iff _ _).mp hz
    exact honestOracle_use_records_challenge base onoff ecEk ecCt0 ecCt1 leak
      m e k t s h out hout
  · trivial

end oppUniKemCKA.Security.Embedding
