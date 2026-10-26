/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Endpoints
import SecureMessaging.SCKA.OppUniKEM.Security.IdealHybrids
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Game
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulation
import SecureMessaging.SCKA.Security
import ToVCVio.OracleComp.QueryTracking.OneUseSampling

/-!
# The reduction branch and the pinned hybrid

Fix a KEM `kem` with deterministic decapsulation, correct erasure codes for Opp-UniKEM, an SCKA
adversary `adv`, a positive epoch `e` at which the reduction embeds its IND-CPA challenge, and an
IND-CPA bit `b`. All experiments below run `adv` from the initial state, with both parties at
epoch `1` and empty message, key, exposure, and challenge tables.

- The ideal hybrid `H_i`, for `i : ℕ`, runs the SCKA security game for Opp-UniKEM, replacing A's
  decapsulation by B's recorded key for A's current epoch. Accepted challenges at epochs
  `1, …, i` return uniform keys; all other epochs return recorded keys
  (`idealEpochHybridExp`, `IdealHybrids`).
- Define `i_b := if b then e - 1 else e`. The pinned hybrid `P_e^b` samples the outputs and coins
  of key generation, offline encapsulation, and online encapsulation as KEM material `kemMat`,
  using the randomness-leaking samplers `leak` (`sampleMaterial leak`). It runs `H_{i_b}` with
  the outputs and coins of epoch `e` fixed to `kemMat`, returning `false` at the first query whose
  successor exposes `e`. In Lean this is the run using `stageStopped .pinned kemMat e (!b)`,
  averaged over `kemMat`.
- The reduction branch `𝓑_e^b := fixedBranch … adv e b` draws a fresh IND-CPA challenge, whose
  candidate key is the encapsulated key if `b = true` and an independent uniform key otherwise.
  It runs the same protocol, inserting the challenge public key and ciphertext at `e` and
  hiding their secret key, offline state, shared key, and coins. Accepted challenges at `e`
  return the candidate key; other challenges follow `H_{i_b}`. A permitted corruption or leaking
  send that would reveal a hidden value returns `false`.

Both `P_e^b` and `𝓑_e^b` return `adv`'s output on normal completion. Their acceptance probabilities
are equal (`fixedBranch_eq_pinnedHybrid`):

```text
Pr[𝓑_e^b = true] = Pr[P_e^b = true].
```

The mode bit in `stageStopped` is `!b`: `true` selects a uniform challenge key, whereas the
IND-CPA bit `true` selects the encapsulated key.
-/

open OracleSpec OracleComp KEMScheme
open SCKAScheme.sckaSecuritySpec

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
  (hDet : kem.DeterministicDecaps)
variable (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
variable (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
variable (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
variable (leak : kem.OnOffRandLeak onoff)

section

variable {kem onoff} in
/-- Whether `query` is an eligible challenge at epoch `e` from `s`, that is, a query whose answer
reads the key at `e`. -/
def usesChallengeKey
    (e : ℕ) (query : (SCKAScheme.sckaSecuritySpec Unit Unit Unit Unit Unit).Domain)
    (s : GameState onoff Sym) : Bool :=
  match query with
  | OChall t => decide (t = e ∧ e ∉ s.exposed ∧ e ∉ s.challenged ∧
      ((s.keyA e).isSome ∨ (s.keyB e).isSome))
  | _ => false

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Stage oracles: the security oracles over `stageScheme stage kemMat e s` at state `s`, with
challenges `challOf (adjacentMode e b)`; `stageOracle .pinned kemMat e b` is the pinned hybrid
before stopping. -/
def stageOracle (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (GameState onoff Sym) ProbComp) :=
  securityImplAt kem onoff leak (stageScheme ecEk ecCt0 ecCt1 stage kemMat e)
    (SCKAScheme.challOf (adjacentMode e b))

/-- `stageOracle stage kemMat e b`, answering `⊥` at the first query whose successor exposes `e`;
`stageStopped .pinned kemMat e b` is the pinned hybrid. -/
def stageStopped (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (OptionT (StateT
        (GameState onoff Sym) ProbComp)) :=
  stopOnState (stageOracle kem onoff ecEk ecCt0 ecCt1 leak stage kemMat e b)
    (fun s => decide (e ∈ s.exposed))

/-- No query of `honestOracle kemMat e kStar` removes an epoch from `challenged`. -/
private theorem honestOracle_preserves_challenged (kemMat : KEMMaterial leak) (e : ℕ) (kStar : K)
    (u : ℕ) :
    QueryImpl.PreservesInv (honestOracle kem onoff ecEk ecCt0 ecCt1 leak kemMat e kStar)
      (fun s => u ∈ s.challenged) := by
  intro t s hs res hres
  rw [honestOracle, securityImplAt_run] at hres
  exact SCKAScheme.securityImplOf_challenged_subset _ _ _ _ _
    (fun t s res hres => (SCKAScheme.correctnessImpl_securitySets_eq _ t s res hres).2)
    (pinnedChallenge_recordsChallenges onoff e kStar) t s res hres hs

/-- If `usesChallengeKey e t s = false`, the key does not affect how `honestOracle kemMat e k`
answers `t` from `s`. -/
private theorem honestOracle_eq_of_unused (kemMat : KEMMaterial leak) (e : ℕ) (k k' : K)
    (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym)
    (h : usesChallengeKey e t s = false) :
    (honestOracle kem onoff ecEk ecCt0 ecCt1 leak kemMat e k t).run s =
      (honestOracle kem onoff ecEk ecCt0 ecCt1 leak kemMat e k' t).run s := by
  rcases t with (((((t | a) | a) | t) | a) | a)
  all_goals try rfl
  simp only [securityImplAt, SCKAScheme.securityImplOf, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr, honestOracle, StateT.run_bind, StateT.run_get,
      pure_bind]
  exact pinnedChallenge_eq_of_unused onoff e t k k' s (of_decide_eq_false h)

/-- If `usesChallengeKey e t s = true`, every possible successor of
`honestOracle kemMat e k` on `t` from `s` has `e ∈ challenged`. -/
private theorem honestOracle_use_records_challenge (kemMat : KEMMaterial leak) (e : ℕ) (k : K)
    (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym)
    (h : usesChallengeKey e t s = true)
    (res : (securitySpec leak Sym).Range t ×
      GameState onoff Sym)
    (hres : res ∈ support ((honestOracle kem onoff ecEk ecCt0 ecCt1 leak kemMat e k t).run s)) :
    e ∈ res.2.challenged := by
  rcases t with (((((t | a) | a) | t) | a) | a)
  all_goals try simp only [usesChallengeKey, Bool.false_eq_true, decide_eq_true_eq] at h
  obtain ⟨ht, he, hc, hk⟩ := h
  subst t
  simp only [securityImplAt, SCKAScheme.securityImplOf, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr, honestOracle, StateT.run_bind, StateT.run_get,
      pure_bind] at hres
  rw [pinnedChallenge_selected onoff e k s (by simp [he, hc]) hk] at hres
  obtain rfl := (mem_support_pure_iff _ _).mp hres
  exact Finset.mem_insert_self _ _

end

section

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Under `reachableInv`, if every key B records at `e` is `kemMat.key`, then
`honestOracle kemMat e kemMat.key` and `stageOracle .pinned kemMat e false` answer every query with
the same computation. -/
private theorem honestOracle_eq_hybrid_real
    (kemMat : KEMMaterial leak) (e : ℕ) (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym)
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hm : ∀ k, s.keyB e = some k → k = kemMat.key) :
    (honestOracle kem onoff ecEk ecCt0 ecCt1 leak kemMat e kemMat.key t).run s =
      (stageOracle kem onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e false t).run s := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  all_goals try rfl
  simp only [securityImplAt, SCKAScheme.securityImplOf, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr, honestOracle, stageOracle, StateT.run_bind,
      StateT.run_get,
    pure_bind, SCKAScheme.challOf, adjacentMode_apply, Bool.false_eq_true, false_and, or_false]
  exact pinnedChallenge_eq_recorded onoff e kemMat.key t s
    (recorded_eq_key kem onoff ecEk ecCt0 ecCt1 leak kemMat e s hs hm)

include hDet hEk hCt0 hCt1 in
/-- With the key of `kemMat` at `e`, the stopped honest game has the acceptance probability of the
stopped pinned hybrid with mode bit `false`: for `kemMat ∈ support (sampleMaterial leak)`,
`Pr[optionRun (honestStopped kemMat e kemMat.key) adv s₀ = true] =
Pr[optionRun (stageStopped .pinned kemMat e false) adv s₀ = true]`. -/
theorem honestStopped_real_eq_hybrid
    (kemMat : KEMMaterial leak) (hm : kemMat ∈ support (sampleMaterial leak)) (e : ℕ)
    (adv : SecurityAdversary leak Sym) :
    Pr{let x ← (optionRun (honestStopped kem onoff ecEk ecCt0 ecCt1 leak kemMat e kemMat.key)
      adv (oppUniKemCKA.Reduction.Internal.initialGame kem onoff))}[x = true] =
    Pr{let x ← (optionRun (stageStopped kem onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e false)
      adv (oppUniKemCKA.Reduction.Internal.initialGame kem onoff))}[x = true] := by
  symm
  apply prEvent_optionRun_eq_of_state_map _ _ id
    (fun s => (reachableInv kem onoff ecEk ecCt0 ecCt1 s ∧ consistentMat kemMat e s) ∧
      ∀ k, s.keyB e = some k → k = kemMat.key)
  · intro t s hs res hres _
    change res ∈ support (do
      let out ← (honestOracle kem onoff ecEk ecCt0 ecCt1 leak kemMat e kemMat.key t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hres
    obtain ⟨out, hout, hres⟩ := (mem_support_bind_iff _ _ _).mp hres
    obtain rfl := (mem_support_pure_iff _ _).mp hres
    exact ⟨honestScheme_preserves_reachableInv_consistentMat kem onoff hDet ecEk hEk ecCt0 hCt0
      ecCt1 hCt1 leak kemMat hm e _ (pinnedChallenge_recordsChallenges onoff e kemMat.key)
      t s hs.1 out hout,
      honestScheme_preserves_keyB_eq kem onoff ecEk ecCt0 ecCt1 leak kemMat e _
        (pinnedChallenge_recordsChallenges onoff e kemMat.key) t s hs.2 out hout⟩
  · intro t s hs
    simp only [id_eq, Prod.map_id, id_map]
    change (do
      let out ← (stageOracle kem onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e false t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) =ᵈ _
    rw [← honestOracle_eq_hybrid_real kem onoff ecEk ecCt0 ecCt1 leak kemMat e t s hs.1.1 hs.2]
    rfl
  · exact ⟨⟨reachableInv_init kem onoff ecEk ecCt0 ecCt1
      ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos, consistentMat_initial kem onoff leak kemMat e⟩,
      keyB_eq_initial kem onoff leak kemMat e⟩

omit [DecidableEq K] [DecidableEq Sym] in
variable {kem} in
/-- Drawing the key at `e` uniformly turns the pinned challenge into the challenge of mode
`adjacentMode e true`: for `e > 0`, from every state,
`k ←$ K; pinnedChallenge e k t =ᵈ oracleChall (adjacentMode e true t) t`. -/
private theorem pinnedChallenge_sample_uniform
    (e : ℕ) (he : 0 < e) (t : ℕ)
    (s : GameState onoff Sym) :
    (do
      let k ← ($ᵗ K : ProbComp K)
      (pinnedChallenge onoff e k t).run s) =ᵈ
    (SCKAScheme.oracleChall (adjacentMode e true t)
      (StA onoff Sym) (StB onoff Sym) K (Message Sym) t).run s := by
  by_cases hg : t ∈ s.exposed ∨ t ∈ s.challenged
  · simp [OracleComp.EvalDistEq.map_const, pinnedChallenge, challengeWith,
      SCKAScheme.oracleChall, hg]
  · by_cases ht : t = e
    · subst t
      cases hA : s.keyA e <;> cases hB : s.keyB e <;>
        simp [OracleComp.EvalDistEq.map_const, pinnedChallenge, challengeWith,
          SCKAScheme.oracleChall, adjacentMode_apply, hg, hA, hB, he]
    · cases hA : s.keyA t <;> cases hB : s.keyB t <;> by_cases hr : 0 < t ∧ t < e <;>
        simp [OracleComp.EvalDistEq.bind_const, OracleComp.EvalDistEq.map_const, pinnedChallenge,
          challengeWith, SCKAScheme.oracleChall, adjacentMode_apply, hg, hA, hB, ht, hr]

/-- The query-level version of `honestStopped_random_eq_hybrid`: for `e > 0`, from every state,
`k ←$ K; honestOracle kemMat e k t =ᵈ stageOracle .pinned kemMat e true t`. -/
private theorem honestOracle_sample_uniform
    (kemMat : KEMMaterial leak) (e : ℕ) (he : 0 < e) (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym) :
    (do
      let k ← ($ᵗ K : ProbComp K)
      (honestOracle kem onoff ecEk ecCt0 ecCt1 leak kemMat e k t).run s) =ᵈ
    (stageOracle kem onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e true t).run s := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  all_goals
    first
    | simpa only [securityImplAt, SCKAScheme.securityImplOf, QueryImpl.add_apply_inl,
      QueryImpl.add_apply_inr, exposureA, exposureB, honestOracle, stageOracle, StateT.run_bind,
        StateT.run_get,
        pure_bind, SCKAScheme.challOf] using pinnedChallenge_sample_uniform onoff e he t s
    | simp only [securityImplAt, SCKAScheme.securityImplOf, QueryImpl.add_apply_inl,
      QueryImpl.add_apply_inr, honestOracle, stageOracle, StateT.run_bind,
        StateT.run_get,
        pure_bind]
      exact OracleComp.EvalDistEq.bind_const _ _

/-- With a uniform key at `e`, the stopped honest game has the acceptance probability of the stopped
pinned hybrid with mode bit `true`: for `e > 0` and every state `s`,
`Pr[k ←$ K; optionRun (honestStopped kemMat e k) adv s = true] =
Pr[optionRun (stageStopped .pinned kemMat e true) adv s = true]`. -/
theorem honestStopped_random_eq_hybrid
    (kemMat : KEMMaterial leak) (e : ℕ) (he : 0 < e)
    (adv : SecurityAdversary leak Sym)
    (s : GameState onoff Sym) :
    Pr{let x ← (do
      let k ← ($ᵗ K : ProbComp K)
      optionRun (honestStopped kem onoff ecEk ecCt0 ecCt1 leak kemMat e k) adv s)}[x = true] =
    Pr{let x ← (optionRun
        (stageStopped kem onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e true) adv s)}[x = true] :=
  stoppedRun_sample_once_eq ($ᵗ K) (honestOracle kem onoff ecEk ecCt0 ecCt1 leak kemMat e)
    (stageOracle kem onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e true) (fun s => decide (e ∈
      s.exposed))
    (fun _ => True) (fun s => e ∈ s.challenged) (usesChallengeKey e)
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun k _ t s _ hs res hres _ => honestOracle_preserves_challenged kem onoff ecEk ecCt0 ecCt1
      leak kemMat e k e t s hs res hres)
    (fun t s _ h k _ k' _ => ToVCVio.evalDistEq_of_eq
      (honestOracle_eq_of_unused kem onoff ecEk ecCt0 ecCt1 leak kemMat e k k' t s h))
    (fun t s _ hs => by
      rcases t with (((((t | a) | a) | t) | a) | a) <;> simp [usesChallengeKey, hs])
    (fun k _ t s _ h res hres _ => honestOracle_use_records_challenge kem onoff ecEk ecCt0 ecCt1
      leak kemMat e k t s h res hres)
    (fun t s _ => honestOracle_sample_uniform kem onoff ecEk ecCt0 ecCt1 leak kemMat e he t s)
    adv s trivial

include hDet hEk hCt0 hCt1 in
/-- For `e > 0`, `Pr[fixedBranch adv e b = true] =
Pr[kemMat ← sampleMaterial leak; optionRun (stageStopped .pinned kemMat e (!b)) adv s₀ = true]`;
the negation maps the IND-CPA bit (`true`: real key) to the mode bit (`true`: uniform key). -/
theorem fixedBranch_eq_pinnedHybrid
    (adv : SecurityAdversary leak Sym) (e : ℕ) (he : 0 < e) (b : Bool) :
    Pr{let x ← fixedBranch kem onoff ecEk ecCt0 ecCt1 leak adv e b}[x = true] =
    Pr{let x ← (do
      let kemMat ← sampleMaterial leak
      optionRun (stageStopped kem onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e (!b))
        adv (oppUniKemCKA.Reduction.Internal.initialGame kem onoff))}[x = true] := by
  rw [fixedBranch_eq_honestStopped kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1]
  simp only [map_bind]
  refine OracleComp.prEvent_bind_congr_of_support _ _ _ fun kemMat hm => ?_
  cases b
  · simpa only [map_bind, Bool.false_eq_true, ↓reduceIte, Bool.not_false] using
      honestStopped_random_eq_hybrid kem onoff ecEk ecCt0 ecCt1 leak kemMat e he adv _
  · simp only [Bool.not_true, ↓reduceIte, OracleComp.prEvent_bind_const]
    exact honestStopped_real_eq_hybrid kem onoff hDet ecEk hEk ecCt0 hCt0
      ecCt1 hCt1 leak kemMat hm e adv

end

/-! ## The fresh stage -/

/-- B's leaking send in `stageScheme .fresh kemMat e s` is that of Opp-UniKEM over `kem`. -/
theorem sendBrleak_fresh_eq [DecidableEq Sym]
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (stB : StB onoff Sym) :
    (stageScheme ecEk ecCt0 ecCt1 .fresh kemMat e s).sendBrleak stB =
    (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak).sendBrleak stB := by
  dsimp only [stageScheme, Stage.keygenFlag, Stage.offlineFlag, Stage.onlineFlag]
  simp only [scheme]
  cases hct0 : stB.ct0 <;> cases hek : stB.ekA <;> cases hct1 : stB.ct1 <;>
    cases hst : stB.stCt <;> cases hack : stB.ack.ctRec
  all_goals
    simp only [sendBrleak, hct0, hek, hct1]
    try dsimp only [Pinned.leakage]
    simp [hct0, hek, hct1, hst, hack, monad_norm]

/-- Ordinary-send version of `sendBrleak_fresh_eq`. -/
theorem sendB_fresh_eq [DecidableEq Sym]
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (stB : StB onoff Sym) :
    (stageScheme ecEk ecCt0 ecCt1 .fresh kemMat e s).sendB stB =
    (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak).sendB stB := by
  rw [scheme_sendB_eq_map_sendBrleak, scheme_sendB_eq_map_sendBrleak,
    sendBrleak_fresh_eq kem onoff hDet ecEk ecCt0 ecCt1 leak kemMat e s stB]

/-- The fully fresh stage is the ideal game of mode `adjacentMode e b`:
`stageOracle .fresh kemMat e b = idealSecurityImpl (adjacentMode e b)`. -/
theorem stageOracle_fresh_eq_ideal [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) :
    stageOracle kem onoff ecEk ecCt0 ecCt1 leak .fresh kemMat e b =
      idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (adjacentMode e b) := by
  funext t
  apply StateT.ext
  intro s
  simp only [securityImplAt, SCKAScheme.securityImplOf,
    stageOracle, StateT.run_bind, StateT.run_get,
      pure_bind]
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl]
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleSendA, stageScheme, Stage.keygenFlag, Stage.offlineFlag,
        Stage.onlineFlag, scheme, sendA, Pinned.kem, Pinned.onOff, Pinned.keygen,
        Bool.false_eq_true, ite_false]
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get, pure_bind]
      rw [sendB_fresh_eq kem onoff hDet ecEk ecCt0 ecCt1 leak kemMat e s _]
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind]
      cases hm : s.msgB n with
      | none =>
        simp only [oracleRecvAIdeal, schemeWithDecaps, SCKAScheme.oracleRecvA,
          StateT.run_bind, StateT.run_get, pure_bind, hm]
      | some entry =>
        rcases entry with ⟨msg, tsnd⟩
        simp only []
        rw [stageScheme_recvA_eq_ideal]
        simp only [oracleRecvAIdeal, schemeWithDecaps, SCKAScheme.oracleRecvA,
          StateT.run_bind, StateT.run_get, pure_bind, hm]
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleRecvB, stageScheme, scheme, recvB]
  · simp only [idealSecurityImpl, SCKAScheme.securityImplOf,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      SCKAScheme.oracleSendArleak, stageScheme, Stage.keygenFlag, Stage.offlineFlag,
      Stage.onlineFlag, scheme, sendArleak, Pinned.kem, Pinned.onOff, Pinned.leakage,
      Bool.false_eq_true, ite_false]
  · simp only [idealSecurityImpl, SCKAScheme.securityImplOf,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      SCKAScheme.oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind]
    rw [sendBrleak_fresh_eq kem onoff hDet ecEk ecCt0 ecCt1 leak kemMat e s _]
  · rfl
  · rfl
  · rfl

end oppUniKemCKA.Security.Embedding
