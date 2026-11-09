/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.OppUniKEM.Security.IdealHybrids
public import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Game
public import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulation
public import ToVCVio.OracleComp.QueryTracking.OneUseSampling

/-!
# The fixed branch and the pinned hybrid

Fix a KEM `kem` with deterministic decapsulation, correct erasure codes for Opp-UniKEM, an SCKA
adversary `adv`, a positive epoch `e` at which the reduction embeds its IND-CPA challenge, and a
version `x ∈ {real, random}`: a challenge at `e` returns the real key in `real` and an
independent uniform key in `random`. All experiments below run `adv` from the initial state, with
both parties at epoch `1`, empty message and key tables, and empty exposure and challenge sets.

- The ideal hybrid `H_i`, for `i : ℕ`, runs the SCKA security game for Opp-UniKEM, replacing A's
  decapsulation by B's recorded key for A's current epoch. Eligible challenges at epochs
  `1, …, i` return uniform keys; all other eligible challenges return recorded keys
  (`idealEpochHybridExp`, `IdealHybrids`).
- The pinned hybrid `P_e^x` draws KEM material `kemMat ← sampleMaterial leak`: the outputs and
  coins of key generation, offline encapsulation, and online encapsulation. It runs `H_{e-1}` in
  `real` and `H_e` in `random` with the outputs and coins of epoch `e` fixed to `kemMat`,
  returning `false` at the first exposure of `e` by a permitted corruption or leaking send
  (`stageStopped .pinned kemMat e false` for `real`, `… true` for `random`, averaged over
  `kemMat`).
- The fixed branch `𝓑_e^x` (`fixedBranch … adv e true` for `real`, `… false` for `random`)
  draws a fresh IND-CPA challenge, whose candidate key is the encapsulated key in `real` and an
  independent uniform key in `random`. It runs the same protocol, inserting the challenge public
  key and ciphertext at `e` and hiding their secret key, offline state, shared key, and coins.
  Eligible challenges at `e` return the candidate key; other challenges at `t` return a uniform
  key if `0 < t < e` and the recorded key otherwise. A permitted corruption or leaking send that
  would reveal a hidden value returns `false`.

Both `P_e^x` and `𝓑_e^x` return `adv`'s output on normal completion. Their acceptance
probabilities are equal (`fixedBranch_eq_pinnedHybrid`):

```text
Pr[𝓑_e^x = true] = Pr[P_e^x = true].
```
-/

@[expose] public section

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

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Security oracles pinning the phases specified by `stage` at `e`, with A using B's recorded
key. An eligible challenge at `t` returns a uniform key iff
`0 < t ∧ (t < e ∨ (t = e ∧ b = true))`, and the recorded key otherwise. -/
def stageOracle (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (GameState onoff Sym) ProbComp) :=
  SCKAScheme.modeImpl (stageScheme ecEk ecCt0 ecCt1 stage kemMat e) (exposureA kem onoff leak)
    (exposureB kem onoff leak) (SCKAScheme.adjacentMode e b)

/-- The stage oracle stopped at the first exposure of `e`, where a stopped run returns `false`.
The fully pinned case gives the pinned hybrid `P_e^x`, with `b = true` for version `random`. -/
def stageStopped (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (OptionT (StateT
        (GameState onoff Sym) ProbComp)) :=
  stopOnState (stageOracle kem onoff ecEk ecCt0 ecCt1 leak stage kemMat e b)
    (fun s => decide (e ∈ s.exposed))

end

section

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- In a transcript-consistent state (`reachableInv`), if B's recorded key at `e`, when present,
is `kemMat.key`, answering challenges at `e` with `kemMat.key` or the recorded key gives the same
query computation. -/
private theorem honestOracle_eq_hybrid_real
    (kemMat : KEMMaterial leak) (e : ℕ) (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym)
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hm : ∀ k, s.keyB e = some k → k = kemMat.key) :
    (honestOracle kem onoff ecEk ecCt0 ecCt1 leak kemMat e kemMat.key t).run s =
      (stageOracle kem onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e false t).run s := by
  have h := SCKAScheme.securityImplAt_pinnedChallenge_eq_recorded e kemMat.key
    (honestScheme ecEk ecCt0 ecCt1 kemMat e) (exposureA kem onoff leak) (exposureB kem onoff leak)
    t s (recorded_eq_key kem onoff ecEk ecCt0 ecCt1 leak kemMat e s hs hm)
  rw [honestOracle, stageOracle]
  exact h

include hDet hEk hCt0 hCt1 in
/-- For any possible honest material `kemMat`, answering challenges at `e` with `kemMat.key` or
the recorded key gives the same acceptance probability from the initial state. Both games pin
epoch `e` to `kemMat` and return `false` at the first exposure of `e`. -/
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
      ecCt1 hCt1 leak kemMat hm e _ (SCKAScheme.pinnedChallenge_recordsChallenges e kemMat.key)
      t s hs.1 out hout,
      honestScheme_preserves_keyB_eq kem onoff ecEk ecCt0 ecCt1 leak kemMat e _
        (SCKAScheme.pinnedChallenge_recordsChallenges e kemMat.key) t s hs.2 out hout⟩
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

/-- For `e > 0`, drawing a uniform challenge key before the run or at the eligible challenge
at `e` gives the same acceptance probability from every state. Both games pin epoch `e` to
`kemMat` and return `false` at the first exposure of `e`. -/
theorem honestStopped_random_eq_hybrid
    (kemMat : KEMMaterial leak) (e : ℕ) (he : 0 < e)
    (adv : SecurityAdversary leak Sym)
    (s : GameState onoff Sym) :
    Pr{let x ← (do
      let k ← ($ᵗ K : ProbComp K)
      optionRun (honestStopped kem onoff ecEk ecCt0 ecCt1 leak kemMat e k) adv s)}[x = true] =
    Pr{let x ← (optionRun
        (stageStopped kem onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e true) adv s)}[x = true] := by
  have h := SCKAScheme.stoppedRun_pinnedChallenge_sample_eq e
    (honestScheme ecEk ecCt0 ecCt1 kemMat e) (exposureA kem onoff leak) (exposureB kem onoff leak)
    he adv s
  unfold stoppedRun at h
  unfold honestStopped stageStopped honestOracle stageOracle
  exact h

include hDet hEk hCt0 hCt1 in
/-- For `e > 0` and the initial game state `s₀`, `Pr[fixedBranch adv e b = true] =
Pr[kemMat ← sampleMaterial leak; optionRun (stageStopped .pinned kemMat e (!b)) adv s₀ = true]`,
that is, `Pr[𝓑_e^x = true] = Pr[P_e^x = true]`, where version `real` is `fixedBranch … true` and
`stageStopped … false`. -/
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
  dsimp only [stageScheme, stageKem, stageOnOff, stageDet, stageLeak,
    Stage.keygenFlag, Stage.offlineFlag, Stage.onlineFlag]
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

/-- The fully fresh stage is the ideal game of mode `adjacentMode e b` (`SCKA.Security.Hybrids`):
`stageOracle .fresh kemMat e b = idealSecurityImpl (adjacentMode e b)`. -/
theorem stageOracle_fresh_eq_ideal [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) :
    stageOracle kem onoff ecEk ecCt0 ecCt1 leak .fresh kemMat e b =
      idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (SCKAScheme.adjacentMode e b) := by
  funext t
  apply StateT.ext
  intro s
  simp only [SCKAScheme.modeImpl, SCKAScheme.securityImplAt, SCKAScheme.securityImplOf,
    stageOracle, StateT.run_bind, StateT.run_get,
      pure_bind]
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl]
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleSendA, stageScheme, stageKem, Stage.keygenFlag,
        scheme, sendA, Pinned.kem, Pinned.keygen,
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
      SCKAScheme.oracleSendArleak, stageScheme, stageLeak, Stage.keygenFlag,
      scheme, sendArleak, Pinned.leakage,
      Bool.false_eq_true, ite_false]
  · simp only [idealSecurityImpl, SCKAScheme.securityImplOf,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      SCKAScheme.oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind]
    rw [sendBrleak_fresh_eq kem onoff hDet ecEk ecCt0 ecCt1 leak kemMat e s _]
  · rfl
  · rfl
  · rfl

end oppUniKemCKA.Security.Embedding
