/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.HybridGame
import SecureMessaging.SCKA.Security
import ToVCVio.OracleComp.QueryTracking.OneUseSampling

/-!
# Deferring the challenge-epoch samples

**Setting.** Let
- `adv` be an SCKA adversary against Opp-UniKEM;
- `e : ℕ` be the epoch at which the reduction embeds the KEM IND-CPA challenge;
- `b : Bool` be the ideal challenge mode at `e`: uniform key for `true`, recorded key for `false`.

Assume that the KEM has deterministic decapsulation and the three erasure codes are correct.

**Challenge mode.** Define `μ := adjacentMode e b` (`IdealHybrids`). For every epoch `t`,

```text
μ(t) = true ↔ 0 < t ∧ (t < e ∨ (t = e ∧ b = true)).
```

An accepted challenge at epoch `t` returns a uniform key if `μ(t) = true`, and the recorded key
otherwise.

**Experiments.** Both run `adv` from their respective empty initial states at epoch `1`, replacing
A's decapsulation by B's recorded key for A's current epoch. Let
- `R := fixedBranch adv e (!b)` (`Simulator`) sample a fresh KEM challenge and embed its public
  key and ciphertext at `e`, hiding its secret key, offline state, shared key, and coins.
  An accepted challenge at `e` returns its candidate key: uniform if `b = true`, encapsulated
  if `b = false`; other challenges follow `μ`. A permitted corruption or leaking send that
  would reveal a hidden value stops the run with output `false`.
- `I` run the SCKA security oracles with challenge mode `μ` (`idealSecurityImpl μ`, `Endpoints`),
  returning `false` at the first query that exposes `e`.

Both return the output of `adv` on normal completion.

**Main result.** For `e > 0` (`fixedBranch_eq_ideal`):

```text
Pr[R = true] = Pr[I = true].
```
-/

open OracleSpec OracleComp KEMScheme
open SCKAScheme.sckaSecuritySpec SCKAScheme.sckaCorrectnessSpec

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
  (hDet : kem.DeterministicDecaps)
variable (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
variable (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
variable (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
variable (leak : kem.OnOffRandLeak onoff)

/-! ## Online encapsulation: from `.pinned` to `.onlineFresh` -/

variable {kem onoff} in
/-- Predicate on B's state `stB` stating that B's next send runs online encapsulation (`sendB`). -/
abbrev onlineReady
    (stB : StB onoff Sym) : Prop :=
  stB.ack.ctRec = true ∧ stB.ekA.isSome ∧ stB.ct1.isNone ∧
    (stB.ct0.isNone ∨ stB.stCt.isSome)

variable {kem onoff leak} in
/-- Predicate on a query `t` and a game state `s` stating that `t` runs B's online encapsulation of
epoch `e` from `s` (`hit` of the online deferral). -/
def usesOnline (e : ℕ) (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym) : Bool :=
  match t with
  | OCorrectness OSendB =>
    decide (s.stB.t = e ∧ onlineReady s.stB)
  | OSendBrleak =>
    decide ((s.stB.t = e ∧ onlineReady s.stB) ∧ e ∉ s.challenged)
  | _ => false

/-- Single use of the online sample: once B holds the key of epoch `e` (`(s.keyB e).isSome`), no
query runs B's online encapsulation of `e`, in states satisfying `reachableInv`. -/
theorem usesOnline_eq_false_of_used
    (e : ℕ) (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym)
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s) (hk : (s.keyB e).isSome) :
    usesOnline e t s = false := by
  have hnot : ¬(s.stB.t = e ∧ onlineReady s.stB) := by
    rintro ⟨he, hready⟩
    have hct : s.stB.ct1 = none := Option.isNone_iff_eq_none.mp hready.2.2.1
    have hnone := (keys_none_before_online kem onoff ecEk ecCt0 ecCt1 s hs hct).2
    rw [he] at hnone
    simp only [hnone, Option.isSome_none, Bool.false_eq_true] at hk
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n) <;> simp [usesOnline, hnot]
  all_goals simp [usesOnline, hnot]

/-- Single use of the online sample: every query of the stage oracle `stageOracle stage kemMat e b`
keeps B's key of epoch `e` once recorded, that is, preserves `(s.keyB e).isSome`. -/
theorem stageOracle_preserves_keyB_available
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) :
    QueryImpl.PreservesInv (stageOracle kem onoff ecEk ecCt0 ecCt1 leak stage kemMat e b)
      (fun s => (s.keyB e).isSome) :=
  securityImplAt_preservesInv kem onoff leak _ _ _ (fun _ _ _ h => h)
    (fun _ => sendArleak_forget (onoff := Pinned.onOff kemMat _ _ _ _) _ _ _)
    (fun _ => sendBrleak_forget (onoff := Pinned.onOff kemMat _ _ _ _) _ _ _ _)
    (SCKAScheme.challOf_recordsChallenges _)
    (fun s hs t => SCKAScheme.correctnessImpl_preserves_keyB_available _ e t s hs)

section

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Single use of the online sample: after a query that runs B's online encapsulation of `e`
(`usesOnline e t s`) in the pinned stage oracle, B holds the key of `e` in every possible successor
state in which `e` is unexposed. -/
theorem stageOracle_online_first_use
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym)
    (hh : usesOnline e t s = true)
    (res : (securitySpec leak Sym).Range t ×
      GameState onoff Sym)
    (hres : res ∈ support ((stageOracle kem onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e b t).run
      s))
    (hcont : decide (e ∈ res.2.exposed) = false) : (res.2.keyB e).isSome := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    all_goals try simp only [usesOnline, Bool.false_eq_true] at hh
    cases u
    have hr : s.stB.t = e ∧ onlineReady s.stB := of_decide_eq_true hh
    obtain ⟨he, ha, hp, hc1, hsrc⟩ := hr
    obtain ⟨pk, hp⟩ := Option.isSome_iff_exists.mp hp
    have hc1 : s.stB.ct1 = none := Option.isNone_iff_eq_none.mp hc1
    cases hc0 : s.stB.ct0 <;> cases hst : s.stB.stCt
    all_goals simp only [hc0, hst, Option.isNone_some, Option.isNone_none,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, or_false] at hsrc
    all_goals
      simp only [securityImplAt, SCKAScheme.securityImplOf, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr, stageOracle, SCKAScheme.sckaCorrectnessImpl,
        SCKAScheme.oracleSendB, stageScheme, Stage.keygenFlag, Stage.offlineFlag,
        Stage.onlineFlag, scheme, sendB, Pinned.kem,
        Pinned.onOff, Pinned.encapsOff, Pinned.encapsOn, he, ha, hp, hc1, hc0, hst,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, decide_true,
        mem_support_pure_iff] at hres
      obtain rfl := hres
      simp [Function.update]
  · simp only [usesOnline, Bool.false_eq_true] at hh
  · cases u
    have hr : (s.stB.t = e ∧ onlineReady s.stB) ∧ e ∉ s.challenged := of_decide_eq_true hh
    obtain ⟨⟨he, ha, hp, hc1, hsrc⟩, hchall⟩ := hr
    obtain ⟨pk, hp⟩ := Option.isSome_iff_exists.mp hp
    have hc1 : s.stB.ct1 = none := Option.isNone_iff_eq_none.mp hc1
    cases hc0 : s.stB.ct0 <;> cases hst : s.stB.stCt
    all_goals simp only [hc0, hst, Option.isNone_some, Option.isNone_none,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, or_false] at hsrc
    all_goals
      simp only [securityImplAt, SCKAScheme.securityImplOf, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr, stageOracle, SCKAScheme.oracleSendBrleak,
        stageScheme, Stage.keygenFlag, Stage.offlineFlag, Stage.onlineFlag, scheme,
        sendBrleak, Pinned.leakage, vulnRleakB,
        he, ha, hp, hc1, hc0, hst, hchall, StateT.run_bind, StateT.run_get,
        StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, decide_true,
        Finset.singleton_inter] at hres
      obtain rfl := hres
      simp at hcont
  · simp only [usesOnline, Bool.false_eq_true] at hh
  · simp only [usesOnline, Bool.false_eq_true] at hh
  · simp only [usesOnline, Bool.false_eq_true] at hh

end

section

variable [DecidableEq Sym]

/-- B's leaking send does not read the online sample unless it runs online encapsulation: if B is
not at `e` with `onlineReady`, the send in `stageScheme .pinned { kemMat with on := o } e s` is the
same computation for every `o`. -/
theorem sendBrleak_online_independent
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (hh : ¬(s.stB.t = e ∧ onlineReady s.stB))
    (online online' : (onoff.C₁ × K) × leak.OnRand) :
    (stageScheme ecEk ecCt0 ecCt1 .pinned
      { kemMat with on := online } e s).sendBrleak s.stB =
    (stageScheme ecEk ecCt0 ecCt1 .pinned
      { kemMat with on := online' } e s).sendBrleak s.stB := by
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [onlineReady, he, hc0, hp, hc1, hst, ha,
      Option.isSome_none, Option.isSome_some, Option.isNone_none, Option.isNone_some,
      Bool.false_eq_true, and_false, and_true,
      false_or, true_or, or_self, not_true_eq_false] at hh
  all_goals
    simp only [stageScheme, Stage.keygenFlag, Stage.offlineFlag, Stage.onlineFlag,
      scheme, sendBrleak, hc0, hp, hc1, hst, ha, pure_bind,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Pinned.leakage, he, decide_true, decide_false]

/-- The version of `sendBrleak_online_independent` for B's ordinary send. -/
theorem sendB_online_independent
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (hh : ¬(s.stB.t = e ∧ onlineReady s.stB))
    (online online' : (onoff.C₁ × K) × leak.OnRand) :
    (stageScheme ecEk ecCt0 ecCt1 .pinned
      { kemMat with on := online } e s).sendB s.stB =
    (stageScheme ecEk ecCt0 ecCt1 .pinned
      { kemMat with on := online' } e s).sendB s.stB := by
  rw [scheme_sendB_eq_map_sendBrleak, scheme_sendB_eq_map_sendBrleak,
    sendBrleak_online_independent kem onoff ecEk ecCt0 ecCt1 leak kemMat e s hh online online']

/-- If B is at `e` with `onlineReady` and `e ∈ s.challenged`, B's leaking-send oracle of
`stageScheme .pinned kemMat e s` rejects from `s`: it is the computation `pure (none, s)`. -/
theorem leaking_online_rejected [DecidableEq K]
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (he : s.stB.t = e) (hready : onlineReady s.stB) (hc : e ∈ s.challenged) :
    (SCKAScheme.oracleSendBrleak vulnRleakB
      (stageScheme ecEk ecCt0 ecCt1 .pinned kemMat e s) ()).run s = pure (none, s) := by
  obtain ⟨ha, hp, hc1, hsrc⟩ := hready
  obtain ⟨pk, hp⟩ := Option.isSome_iff_exists.mp hp
  have hc1 : s.stB.ct1 = none := Option.isNone_iff_eq_none.mp hc1
  cases hc0 : s.stB.ct0 <;> cases hst : s.stB.stCt
  all_goals simp only [hc0, hst, Option.isNone_some, Option.isNone_none,
    Option.isSome_none, Option.isSome_some, Bool.false_eq_true, or_false] at hsrc
  all_goals
    simp [SCKAScheme.oracleSendBrleak, stageScheme, Stage.keygenFlag,
      Stage.offlineFlag, Stage.onlineFlag, scheme, sendBrleak,
      Pinned.leakage, vulnRleakB, he, ha, hp, hc1, hc0, hst, hc]

variable [DecidableEq K] [SampleableType K]

/-- Independence of the online sample: a query `t` that does not run B's online encapsulation of
`e` (`usesOnline e t s = false`) is the same computation in the pinned stage oracle for every online
sample `o`. -/
theorem stageOracle_online_independent
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym)
    (hh : usesOnline e t s = false)
    (online online' : (onoff.C₁ × K) × leak.OnRand) :
    (stageOracle kem onoff ecEk ecCt0 ecCt1 leak .pinned
      { kemMat with on := online } e b t).run s =
    (stageOracle kem onoff ecEk ecCt0 ecCt1 leak .pinned
      { kemMat with on := online' } e b t).run s := by
  rcases t with (((((t | u) | u) | _) | u) | u) <;> try rcases t with ((((n | u) | u) | n) | n)
  all_goals try cases u
  all_goals simp only [stageOracle, securityImplAt, SCKAScheme.securityImplOf,
    QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind,
      StateT.run_get, pure_bind,
    SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
  · exact SCKAScheme.oracleSendA_run_congr _ _ s rfl
  · exact SCKAScheme.oracleSendB_run_congr _ _ s
      (sendB_online_independent kem onoff ecEk ecCt0 ecCt1 leak kemMat e s
        (of_decide_eq_false hh) online online')
  · exact SCKAScheme.oracleRecvA_run_congr _ _ s (fun ρ =>
      (stageScheme_recvA_eq_ideal kem onoff ecEk ecCt0 ecCt1 leak .pinned
        { kemMat with on := online } e s ρ).trans
      (stageScheme_recvA_eq_ideal kem onoff ecEk ecCt0 ecCt1 leak .pinned
        { kemMat with on := online' } e s ρ).symm) n
  · rfl
  · exact SCKAScheme.oracleSendArleak_run_congr _ _ _ s rfl
  · by_cases hready : s.stB.t = e ∧ onlineReady s.stB
    · have hc : e ∈ s.challenged := by
        have hnot : ¬((s.stB.t = e ∧ onlineReady s.stB) ∧ e ∉ s.challenged) :=
          of_decide_eq_false hh
        by_contra hc
        exact hnot ⟨hready, hc⟩
      exact (leaking_online_rejected kem onoff ecEk ecCt0 ecCt1 leak
        { kemMat with on := online } e s hready.1 hready.2 hc).trans
        (leaking_online_rejected kem onoff ecEk ecCt0 ecCt1 leak
          { kemMat with on := online' } e s hready.1 hready.2 hc).symm
    · exact SCKAScheme.oracleSendBrleak_run_congr _ _ _ s
        (sendBrleak_online_independent kem onoff ecEk ecCt0 ecCt1 leak kemMat e s hready
          online online')

end

/-- Averaging of the online sample for B's leaking send: from a state satisfying `reachableInv` and
`consistentMat kemMat e`, pinning `o ← leak.encapsOnRleak kemMat.st kemMat.pk` (stage `.pinned`)
gives the output distribution of fresh online encapsulation (stage `.onlineFresh`). -/
theorem sendBrleak_sample_online_eq_fresh [DecidableEq Sym]
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s) (hsrc : consistentMat kemMat e s) :
    (do
      let online ← leak.encapsOnRleak kemMat.st kemMat.pk
      (stageScheme ecEk ecCt0 ecCt1 .pinned { kemMat with on := online } e s).sendBrleak s.stB) =ᵈ
    (stageScheme ecEk ecCt0 ecCt1 .onlineFresh kemMat e s).sendBrleak s.stB := by
  have hpub := online_pk_eq_material kem onoff ecEk ecCt0 ecCt1 leak kemMat e s hs hsrc
  have hoff (he : s.stB.t = e) (st : onoff.St) (hst : s.stB.stCt = some st) :
      st = kemMat.st :=
    Option.some.inj (hst.symm.trans (hsrc.2 he (by simp [hst])).1)
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [stageScheme, Stage.keygenFlag, Stage.offlineFlag, Stage.onlineFlag,
      scheme, sendBrleak, hc0, hp, hc1, hst, ha, pure_bind, Pinned.leakage,
      he, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  all_goals
    first
    | solve
      | exact ToVCVio.evalDistEq_bind_of_const' _ fun online _ => rfl
    | have hpk := hpub he _ hp hc1
      first
      | solve | simp only [hpk, EvalDistEq.refl]
      | have hstate := hoff he _ hst
        simp only [hpk, hstate, EvalDistEq.refl]

/-- The version of `sendBrleak_sample_online_eq_fresh` for B's ordinary send. -/
theorem sendB_sample_online_eq_fresh [DecidableEq Sym]
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s) (hsrc : consistentMat kemMat e s) :
    (do
      let online ← leak.encapsOnRleak kemMat.st kemMat.pk
      (stageScheme ecEk ecCt0 ecCt1 .pinned { kemMat with on := online } e s).sendB s.stB) =ᵈ
    (stageScheme ecEk ecCt0 ecCt1 .onlineFresh kemMat e s).sendB s.stB := by
  have h := EvalDistEq.map
    (sendBrleak_sample_online_eq_fresh kem onoff ecEk ecCt0 ecCt1 leak kemMat e s hs hsrc)
    (fun out => out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))
  rw [map_bind] at h
  simpa only [scheme_sendB_eq_map_sendBrleak] using h

section

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Averaging of the online sample for every query: from a state satisfying `reachableInv` and
`consistentMat kemMat e`, pinning `o ← leak.encapsOnRleak kemMat.st kemMat.pk` (stage `.pinned`)
gives the response/successor distribution of fresh online encapsulation (stage `.onlineFresh`). -/
theorem stageOracle_sample_online_eq_fresh
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym)
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s) (hsrc : consistentMat kemMat e s) :
    (do
      let online ← leak.encapsOnRleak kemMat.st kemMat.pk
      (stageOracle kem onoff ecEk ecCt0 ecCt1 leak .pinned { kemMat with on := online } e b t).run
        s) =ᵈ
    (stageOracle kem onoff ecEk ecCt0 ecCt1 leak .onlineFresh kemMat e b t).run s :=
  securityImplAt_sample_eq kem onoff leak (leak.encapsOnRleak kemMat.st kemMat.pk)
    (fun online => stageScheme ecEk ecCt0 ecCt1 .pinned { kemMat with on := online } e)
    (stageScheme ecEk ecCt0 ecCt1 .onlineFresh kemMat e)
    (SCKAScheme.challOf (adjacentMode e b)) s
    (ToVCVio.evalDistEq_bind_of_const' _ fun _ _ => rfl)
    (sendB_sample_online_eq_fresh kem onoff ecEk ecCt0 ecCt1 leak kemMat e s hs hsrc)
    (ToVCVio.evalDistEq_bind_of_const' _ fun _ _ => rfl)
    (sendBrleak_sample_online_eq_fresh kem onoff ecEk ecCt0 ecCt1 leak kemMat e s hs hsrc)
    (fun online _ ρ => (stageScheme_recvA_eq_ideal kem onoff ecEk ecCt0 ecCt1 leak .pinned
      { kemMat with on := online } e s ρ).trans
      (stageScheme_recvA_eq_ideal kem onoff ecEk ecCt0 ecCt1 leak .onlineFresh kemMat e s ρ).symm)
    (fun _ _ _ => rfl) t

include hDet hEk hCt0 hCt1 in
/-- Deferral of the online sample: for a possible KEM material `kemMat` and a state satisfying
`reachableInv` and `consistentMat kemMat e`, drawing `o ← leak.encapsOnRleak kemMat.st kemMat.pk`
once before the pinned stage game with online sample `o` gives the acceptance probability of the
`onlineFresh` stage game, which draws it at B's online encapsulation. -/
theorem stageStopped_online_deferred
    (kemMat : KEMMaterial leak) (hm : kemMat ∈ support (sampleMaterial leak)) (e : ℕ) (b : Bool)
    (adv : SecurityAdversary leak Sym)
    (s : GameState onoff Sym)
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s) (hsrc : consistentMat kemMat e s) :
    Pr{let x ← (do
      let online ← leak.encapsOnRleak kemMat.st kemMat.pk
      optionRun (stageStopped kem onoff ecEk ecCt0 ecCt1 leak .pinned { kemMat with on := online }
        e b)
        adv s)}[x = true] =
    Pr{let x ← (optionRun
      (stageStopped kem onoff ecEk ecCt0 ecCt1 leak .onlineFresh kemMat e b)
      adv s)}[x = true] :=
  stoppedRun_sample_once_eq (leak.encapsOnRleak kemMat.st kemMat.pk)
    (fun online => stageOracle kem onoff ecEk ecCt0 ecCt1 leak .pinned { kemMat with on := online }
      e b)
    (stageOracle kem onoff ecEk ecCt0 ecCt1 leak .onlineFresh kemMat e b)
    (fun s => decide (e ∈ s.exposed))
    (fun s => reachableInv kem onoff ecEk ecCt0 ecCt1 s ∧ consistentMat kemMat e s)
    (fun s => (s.keyB e).isSome) (usesOnline e)
    (fun online hon t s hs res hres _ => honestScheme_preserves_reachableInv_consistentMat kem
      onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak { kemMat with on := online }
      (sampleMaterial_update_online_mem leak kemMat hm online hon) e _
      (SCKAScheme.challOf_recordsChallenges _) t s hs res hres)
    (fun online _ t s _ hu res hres _ => stageOracle_preserves_keyB_available kem onoff ecEk
      ecCt0 ecCt1 leak .pinned { kemMat with on := online } e b t s hu res hres)
    (fun t s _ hh online _ online' _ => ToVCVio.evalDistEq_of_eq
      (stageOracle_online_independent kem onoff ecEk ecCt0 ecCt1 leak kemMat e b t s hh
        online online'))
    (fun t s hs hu => usesOnline_eq_false_of_used kem onoff ecEk ecCt0 ecCt1 leak
      e t s hs.1 hu)
    (fun online _ t s _ hh res hres hcont => stageOracle_online_first_use kem onoff ecEk
      ecCt0 ecCt1 leak { kemMat with on := online } e b t s hh res hres hcont)
    (fun t s hs => stageOracle_sample_online_eq_fresh kem onoff ecEk ecCt0 ecCt1 leak
      kemMat e b t s hs.1 hs.2)
    adv s ⟨hs, hsrc⟩

end

/-! ## Offline encapsulation: from `.onlineFresh` to `.encapsFresh` -/

section

variable {kem onoff} in
/-- Predicate on B's state `stB` stating that B has run its offline encapsulation of epoch `e`
(`used` of the offline deferral). -/
def offlineUsed (e : ℕ) (stB : StB onoff Sym) : Prop :=
  e < stB.t ∨ (stB.t = e ∧ stB.ct0.isSome)

variable {kem onoff leak} in
/-- Predicate on a query `t` and a game state `s` stating that `t` runs B's offline encapsulation
of epoch `e` from `s` (`hit` of the offline deferral). -/
def usesOffline (e : ℕ) (t : (securitySpec leak Sym).Domain) (s : GameState onoff Sym) : Bool :=
  match t with
  | OCorrectness OSendB =>
    decide (s.stB.t = e ∧ s.stB.ct0.isNone)
  | OSendBrleak =>
    decide ((s.stB.t = e ∧ s.stB.ct0.isNone) ∧ e ∉ s.challenged)
  | _ => false

variable {kem onoff leak} in
/-- Single use of the offline sample: once B has used its offline encapsulation of epoch `e`
(`offlineUsed e s.stB`), no query runs it: `usesOffline e t s = false`. -/
theorem usesOffline_eq_false_of_used (e : ℕ) (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym) (hs : offlineUsed e s.stB) : usesOffline e t s = false := by
  have hno : ¬(s.stB.t = e ∧ s.stB.ct0.isNone) := by
    rintro ⟨ht, hp⟩
    cases hc : s.stB.ct0 <;> simp_all [offlineUsed]
  simp only [Option.isNone_iff_eq_none] at hno
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    all_goals
      simp [usesOffline]
      all_goals aesop
  all_goals
    simp [usesOffline]
    all_goals aesop

variable [DecidableEq K] [DecidableEq Sym]

/-- Once B has used its offline encapsulation of epoch `e`, it stays used: every correctness query
(send or receive) of `stageScheme stage kemMat e s` from `s` preserves `offlineUsed e`. -/
theorem correctness_preserves_offlineUsed
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym) (hs : offlineUsed e s.stB)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (res : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t × GameState onoff Sym)
    (hres : res ∈ support
      ((SCKAScheme.sckaCorrectnessImpl (stageScheme ecEk ecCt0 ecCt1 stage kemMat e s) t).run s)) :
    offlineUsed e res.2.stB := by
  apply SCKAScheme.correctnessImpl_preserves_localInv_at _ (fun _ stB => offlineUsed e stB) s hs
    ?_ ?_ ?_ ?_ t res hres
  · exact fun _ _ _ _ _ => hs
  · intro key msg epoch next hout
    have hshape := sendB_offline_shape
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecCt0 ecCt1 s.stB key msg epoch
      next hout
    rcases hs with h | ⟨h, _⟩
    · exact Or.inl (by simpa only [hshape.1] using h)
    · exact Or.inr ⟨hshape.1.trans h, hshape.2⟩
  · exact fun _ _ _ _ _ => hs
  · intro msg key epoch next hout
    have hshape := oppUniKemCKA.Reduction.Internal.recvB_kem_source_shape
      kem onoff ecEk s.stB msg key epoch next hout
    rcases hshape with h | h
    · simpa only [offlineUsed, h.1, h.2.2.1] using hs
    · apply Or.inl
      rcases hs with hs | ⟨hs, _⟩ <;> omega

/-- Single use of the offline sample: every query of the stage oracle `stageOracle stage kemMat e b`
preserves `offlineUsed e`. -/
theorem stageOracle_preserves_offlineUsed [SampleableType K]
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) :
    QueryImpl.PreservesInv (stageOracle kem onoff ecEk ecCt0 ecCt1 leak stage kemMat e b)
      (fun s => offlineUsed e s.stB) :=
  securityImplAt_preservesInv kem onoff leak _ _ _ (fun _ _ _ h => h)
    (fun _ => sendArleak_forget (onoff := Pinned.onOff kemMat _ _ _ _) _ _ _)
    (fun _ => sendBrleak_forget (onoff := Pinned.onOff kemMat _ _ _ _) _ _ _ _)
    (SCKAScheme.challOf_recordsChallenges _)
    (fun s hs t => correctness_preserves_offlineUsed kem onoff ecEk ecCt0 ecCt1 leak
      stage kemMat e s hs t)

/-- B's ordinary send holds or produces B's offline ciphertext: if B is at `e`, every possible
successor state of the send satisfies `offlineUsed e`. -/
theorem oracleSendB_installs_offline
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (he : s.stB.t = e)
    (res : Option (ℕ × Option ℕ × Message Sym) ×
      GameState onoff Sym)
    (hres : res ∈ support
      ((SCKAScheme.oracleSendB (stageScheme ecEk ecCt0 ecCt1 stage kemMat e s) ()).run s)) :
    offlineUsed e res.2.stB := by
  simp only [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get,
    StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
    mem_support_bind_iff] at hres
  obtain ⟨out, hout, hres⟩ := hres
  cases out with
  | none =>
    exact False.elim (sendB_none_not_mem_support
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecCt0 ecCt1 _ hout)
  | some out =>
    rcases out with ⟨key, msg, epoch, next⟩
    have hshape := sendB_offline_shape
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecCt0 ecCt1 s.stB key msg epoch
      next hout
    cases key <;>
      simp only [StateT.run_bind, StateT.run_set, pure_bind,
        StateT.run_pure, mem_support_pure_iff] at hres
    all_goals obtain rfl := hres; exact Or.inr ⟨hshape.1.trans he, hshape.2⟩

/-- If B is at `e` without `ct0` and `e ∉ s.challenged`, B's leaking-send oracle of
`stageScheme stage kemMat e s`, stopped at the first exposure of `e`, answers `none` from `s`. -/
theorem leaking_offline_stops
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (he : s.stB.t = e) (hfield : s.stB.ct0 = none) (hc : e ∉ s.challenged)
    (res : Option (Option (ℕ × Option ℕ × Message Sym ×
      SendRand leak.KeygenRand leak.OffRand leak.OnRand)) ×
      GameState onoff Sym)
    (hres : res ∈ support (((stopOnState
      (SCKAScheme.oracleSendBrleak vulnRleakB (stageScheme ecEk ecCt0 ecCt1 stage kemMat e s))
      (fun s => decide (e ∈ s.exposed)) ()).run).run s)) : res.1 = none := by
  apply SCKAScheme.oracleSendBrleak_stop_of_exposure _ _ s {e} e ?_ ?_ ?_
    (Finset.mem_singleton_self e) res hres
  · exact sendBrleak_none_not_mem_support
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecCt0 ecCt1
      (stageLeak stage kemMat e s) _
  · intro key msg epoch next coins hout
    have hex := sendBrleak_exposure
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecCt0 ecCt1
      (stageLeak stage kemMat e s) s.stB key msg epoch next coins hout
    simpa only [leakEpochsB, hfield, Option.isNone_none,
      Bool.true_or, ↓reduceIte, he] using hex
  · simp [hc]

variable [SampleableType K]

/-- Single use of the offline sample: after a query that runs B's offline encapsulation of epoch `e`
(`usesOffline e t s`) in any stage oracle, every possible successor state in which `e` is unexposed
satisfies `offlineUsed e`. -/
theorem stageOracle_offline_first_use
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain) (s : GameState onoff Sym)
    (hh : usesOffline e t s = true)
    (res : (securitySpec leak Sym).Range t × GameState onoff Sym)
    (hres : res ∈ support ((stageOracle kem onoff ecEk ecCt0 ecCt1 leak stage kemMat e b t).run s))
    (hcont : decide (e ∈ res.2.exposed) = false) : offlineUsed e res.2.stB := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  all_goals try (rcases t with ((((n | u) | u) | n) | n))
  all_goals try (simp only [usesOffline, Bool.false_eq_true] at hh)
  all_goals cases u
  · have hhit : s.stB.t = e ∧ s.stB.ct0.isNone := of_decide_eq_true hh
    change res ∈ support
      ((SCKAScheme.oracleSendB (stageScheme ecEk ecCt0 ecCt1 stage kemMat e s) ()).run s) at hres
    exact oracleSendB_installs_offline kem onoff ecEk ecCt0 ecCt1 leak
      stage kemMat e s hhit.1 res hres
  · have hhit : (s.stB.t = e ∧ s.stB.ct0.isNone) ∧ e ∉ s.challenged :=
      of_decide_eq_true hh
    change res ∈ support ((SCKAScheme.oracleSendBrleak vulnRleakB
      (stageScheme ecEk ecCt0 ecCt1 stage kemMat e s) ()).run s) at hres
    have hstop := leaking_offline_stops kem onoff ecEk ecCt0 ecCt1 leak stage kemMat e s
      hhit.1.1 (Option.isNone_iff_eq_none.mp hhit.1.2) hhit.2 (some res.1, res.2)
      (mem_support_stopOnState_of_mem (SCKAScheme.oracleSendBrleak vulnRleakB
        (stageScheme ecEk ecCt0 ecCt1 stage kemMat e s)) (fun s => decide (e ∈ s.exposed)) ()
        s res hres hcont)
    exact absurd hstop (Option.some_ne_none _)

end

section

variable [DecidableEq Sym]

/-- B's leaking send does not read the offline sample unless it runs offline encapsulation: if
`¬(s.stB.t = e ∧ s.stB.ct0.isNone)`, the send in
`stageScheme .onlineFresh { kemMat with off := off } e s` is the same computation for every `off`.
-/
theorem sendBrleak_offline_independent
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (hh : ¬(s.stB.t = e ∧ s.stB.ct0.isNone))
    (offline offline' : (onoff.St × onoff.C₀) × leak.OffRand) :
    (stageScheme ecEk ecCt0 ecCt1 .onlineFresh { kemMat with off := offline } e s).sendBrleak
      s.stB =
    (stageScheme ecEk ecCt0 ecCt1 .onlineFresh { kemMat with off := offline' } e s).sendBrleak
      s.stB := by
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [he, hc0, Option.isNone_none, Option.isNone_some, Bool.false_eq_true,
      and_true, and_false, not_true_eq_false] at hh
  all_goals
    simp only [stageScheme, Stage.keygenFlag, Stage.offlineFlag, Stage.onlineFlag,
      scheme, sendBrleak, hc0, hp, hc1, hst, ha, pure_bind,
      Pinned.onOff, Pinned.leakage, Pinned.encapsOff,
      he, decide_false,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- The version of `sendBrleak_offline_independent` for B's ordinary send. -/
theorem sendB_offline_independent
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (hh : ¬(s.stB.t = e ∧ s.stB.ct0.isNone))
    (offline offline' : (onoff.St × onoff.C₀) × leak.OffRand) :
    (stageScheme ecEk ecCt0 ecCt1 .onlineFresh { kemMat with off := offline } e s).sendB s.stB =
    (stageScheme ecEk ecCt0 ecCt1 .onlineFresh { kemMat with off := offline' } e s).sendB
      s.stB := by
  rw [scheme_sendB_eq_map_sendBrleak, scheme_sendB_eq_map_sendBrleak,
    sendBrleak_offline_independent kem onoff ecEk ecCt0 ecCt1 leak kemMat e s hh offline offline']

variable [DecidableEq K]

/-- If B is at `e` without `ct0` and `e ∈ s.challenged`, B's leaking-send oracle of
`stageScheme stage kemMat e s` rejects from `s`: it has the distribution of `pure (none, s)`. -/
theorem leaking_offline_rejected
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (he : s.stB.t = e) (hfield : s.stB.ct0 = none) (hc : e ∈ s.challenged) :
    (SCKAScheme.oracleSendBrleak vulnRleakB
      (stageScheme ecEk ecCt0 ecCt1 stage kemMat e s) ()).run s =ᵈ
      (pure (none, s) : ProbComp _) := by
  apply SCKAScheme.oracleSendBrleak_rejected_evalDistEq _ _ s {e} ?_ ?_
  · intro key msg epoch next coins hout
    have hex := sendBrleak_exposure
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecCt0 ecCt1
      (stageLeak stage kemMat e s) s.stB key msg epoch next coins hout
    simpa only [leakEpochsB, hfield, Option.isNone_none,
      Bool.true_or, ↓reduceIte, he] using hex
  · simp [hc]

variable [SampleableType K]

/-- Independence of the offline sample: a query `t` that does not run B's offline encapsulation of
`e` (`usesOffline e t s = false`) has the same response/successor distribution in the
`onlineFresh` stage oracle for every offline sample `off`. -/
theorem stageOracle_offline_independent
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym)
    (hh : usesOffline e t s = false)
    (offline offline' : (onoff.St × onoff.C₀) × leak.OffRand) :
    (stageOracle kem onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { kemMat with off := offline } e b t).run s =ᵈ
    (stageOracle kem onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { kemMat with off := offline' } e b t).run s := by
  rcases t with (((((t | u) | u) | _) | u) | u) <;> try rcases t with ((((n | u) | u) | n) | n)
  all_goals try cases u
  all_goals simp only [stageOracle, securityImplAt, SCKAScheme.securityImplOf,
    QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind,
      StateT.run_get, pure_bind,
    SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
    EvalDistEq.refl]
  · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleSendA_run_congr _ _ s rfl)
  · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleSendB_run_congr _ _ s
      (sendB_offline_independent kem onoff ecEk ecCt0 ecCt1 leak kemMat e s
        (of_decide_eq_false hh) offline offline'))
  · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleRecvA_run_congr _ _ s (fun ρ =>
      (stageScheme_recvA_eq_ideal kem onoff ecEk ecCt0 ecCt1 leak .onlineFresh
        { kemMat with off := offline } e s ρ).trans
      (stageScheme_recvA_eq_ideal kem onoff ecEk ecCt0 ecCt1 leak .onlineFresh
        { kemMat with off := offline' } e s ρ).symm) n)
  · rfl
  · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleSendArleak_run_congr _ _ _ s rfl)
  · by_cases hready : s.stB.t = e ∧ s.stB.ct0.isNone
    · have hc : e ∈ s.challenged := by
        have hnot : ¬((s.stB.t = e ∧ s.stB.ct0.isNone) ∧ e ∉ s.challenged) :=
          of_decide_eq_false hh
        by_contra hc
        exact hnot ⟨hready, hc⟩
      exact (leaking_offline_rejected kem onoff ecEk ecCt0 ecCt1 leak .onlineFresh
        { kemMat with off := offline } e s hready.1
        (Option.isNone_iff_eq_none.mp hready.2) hc).trans
        (leaking_offline_rejected kem onoff ecEk ecCt0 ecCt1 leak .onlineFresh
          { kemMat with off := offline' } e s hready.1
          (Option.isNone_iff_eq_none.mp hready.2) hc).symm
    · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleSendBrleak_run_congr _ _ _ s
        (sendBrleak_offline_independent kem onoff ecEk ecCt0 ecCt1 leak kemMat e s hready
          offline offline'))

end

/-- Averaging of the offline sample for B's leaking send: pinning `off ← leak.encapsOffRleak`
(stage `.onlineFresh`) gives the output distribution of fresh offline encapsulation (stage
`.encapsFresh`). -/
theorem sendBrleak_sample_offline_eq_fresh [DecidableEq Sym]
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym) :
    (do
      let offline ← leak.encapsOffRleak
      (stageScheme ecEk ecCt0 ecCt1 .onlineFresh
        { kemMat with off := offline } e s).sendBrleak s.stB) =ᵈ
    (stageScheme ecEk ecCt0 ecCt1 .encapsFresh kemMat e s).sendBrleak s.stB := by
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [stageScheme, Stage.keygenFlag, Stage.offlineFlag, Stage.onlineFlag, scheme,
      sendBrleak, hc0, hp, hc1, hst, ha, pure_bind, Pinned.onOff, Pinned.leakage,
      Pinned.encapsOff, he, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, EvalDistEq.refl]
  all_goals
    exact ToVCVio.evalDistEq_bind_of_const' _ fun offline _ => rfl

/-- The version of `sendBrleak_sample_offline_eq_fresh` for B's ordinary send. -/
theorem sendB_sample_offline_eq_fresh [DecidableEq Sym]
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym) :
    (do
      let offline ← leak.encapsOffRleak
      (stageScheme ecEk ecCt0 ecCt1 .onlineFresh { kemMat with off := offline } e s).sendB
        s.stB) =ᵈ
    (stageScheme ecEk ecCt0 ecCt1 .encapsFresh kemMat e s).sendB s.stB := by
  have h := EvalDistEq.map
    (sendBrleak_sample_offline_eq_fresh kem onoff ecEk ecCt0 ecCt1 leak kemMat e s)
    (fun out => out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))
  rw [map_bind] at h
  simpa only [scheme_sendB_eq_map_sendBrleak] using h

section

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Averaging of the offline sample for every query: pinning `off ← leak.encapsOffRleak` (stage
`.onlineFresh`) gives the response/successor distribution of fresh offline encapsulation (stage
`.encapsFresh`). -/
theorem stageOracle_sample_offline_eq_fresh
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym) :
    (do
      let offline ← leak.encapsOffRleak
      (stageOracle kem onoff ecEk ecCt0 ecCt1 leak
        .onlineFresh { kemMat with off := offline } e b t).run s) =ᵈ
    (stageOracle kem onoff ecEk ecCt0 ecCt1 leak .encapsFresh kemMat e b t).run s :=
  securityImplAt_sample_eq kem onoff leak leak.encapsOffRleak
    (fun offline =>
      stageScheme ecEk ecCt0 ecCt1 .onlineFresh { kemMat with off := offline } e)
    (stageScheme ecEk ecCt0 ecCt1 .encapsFresh kemMat e)
    (SCKAScheme.challOf (adjacentMode e b)) s
    (ToVCVio.evalDistEq_bind_of_const' _ fun _ _ => rfl)
    (sendB_sample_offline_eq_fresh kem onoff ecEk ecCt0 ecCt1 leak kemMat e s)
    (ToVCVio.evalDistEq_bind_of_const' _ fun _ _ => rfl)
    (sendBrleak_sample_offline_eq_fresh kem onoff ecEk ecCt0 ecCt1 leak kemMat e s)
    (fun offline _ ρ => (stageScheme_recvA_eq_ideal kem onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { kemMat with off := offline } e s ρ).trans
      (stageScheme_recvA_eq_ideal kem onoff ecEk ecCt0 ecCt1 leak .encapsFresh kemMat e s ρ).symm)
    (fun _ _ _ => rfl) t

end

section

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Deferral of the offline sample: from every state, drawing `off ← leak.encapsOffRleak` once
before the `onlineFresh` stage game with offline sample `off` gives the acceptance probability of
the `encapsFresh` stage game, which draws it at B's offline encapsulation. -/
theorem stageStopped_offline_deferred
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym)
    (s : GameState onoff Sym) :
    Pr{let x ← (do
      let offline ← leak.encapsOffRleak
      optionRun (stageStopped kem onoff ecEk ecCt0 ecCt1 leak
        .onlineFresh { kemMat with off := offline } e b) adv s)}[x = true] =
    Pr{let x ← (optionRun (stageStopped kem onoff ecEk ecCt0 ecCt1 leak .encapsFresh kemMat e b)
      adv s)}[x = true] :=
  stoppedRun_sample_once_eq leak.encapsOffRleak
    (fun offline => stageOracle kem onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { kemMat with off := offline } e b)
    (stageOracle kem onoff ecEk ecCt0 ecCt1 leak .encapsFresh kemMat e b)
    (fun s => decide (e ∈ s.exposed))
    (fun _ => True) (fun s => offlineUsed e s.stB) (usesOffline e)
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun offline _ t s _ hu res hres _ => stageOracle_preserves_offlineUsed kem onoff ecEk ecCt0
      ecCt1 leak .onlineFresh { kemMat with off := offline } e b t s hu res hres)
    (fun t s _ hh offline _ offline' _ => stageOracle_offline_independent kem onoff ecEk ecCt0
      ecCt1 leak kemMat e b t s hh offline offline')
    (fun t s _ hu => usesOffline_eq_false_of_used e t s hu)
    (fun offline _ t s _ hh res hres hcont => stageOracle_offline_first_use kem onoff ecEk ecCt0
      ecCt1 leak .onlineFresh { kemMat with off := offline } e b t s hh res hres hcont)
    (fun t s _ => stageOracle_sample_offline_eq_fresh kem onoff ecEk ecCt0 ecCt1 leak kemMat e b t
      s)
    adv s trivial

end

/-! ## Key generation: from `.encapsFresh` to `.fresh` -/

section

variable {kem onoff} in
/-- Predicate on A's state `stA` stating that A has run its key generation of epoch `e` (`used` of
the key-generation deferral). -/
def keygenUsed (e : ℕ) (stA : StA onoff Sym) : Prop :=
  e < stA.t ∨ (stA.t = e ∧ stA.dkA.isSome)

variable {kem onoff leak} in
/-- Predicate on a query `t` and a game state `s` stating that `t` runs A's key generation of epoch
`e` from `s` (`hit` of the key-generation deferral). -/
def usesKeygen (e : ℕ) (t : (securitySpec leak Sym).Domain) (s : GameState onoff Sym) : Bool :=
  match t with
  | OCorrectness OSendA =>
    decide (s.stA.t = e ∧ s.stA.dkA.isNone)
  | OSendArleak =>
    decide ((s.stA.t = e ∧ s.stA.dkA.isNone) ∧ e ∉ s.challenged)
  | _ => false

variable {kem onoff leak} in
/-- Single use of the key pair: once A has used its key generation of epoch `e`
(`keygenUsed e s.stA`), no query runs it: `usesKeygen e t s = false`. -/
theorem usesKeygen_eq_false_of_used (e : ℕ) (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym) (hs : keygenUsed e s.stA) : usesKeygen e t s = false := by
  have hno : ¬(s.stA.t = e ∧ s.stA.dkA.isNone) := by
    rintro ⟨ht, hp⟩
    cases hd : s.stA.dkA <;> simp_all [keygenUsed]
  simp only [Option.isNone_iff_eq_none] at hno
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    all_goals
      simp [usesKeygen]
      all_goals aesop
  all_goals
    simp [usesKeygen]
    all_goals aesop

variable [DecidableEq K] [DecidableEq Sym]

/-- Once A has used its key generation of epoch `e`, it stays used: every correctness query (send
or receive) of `stageScheme stage kemMat e s` from `s` preserves `keygenUsed e`. -/
theorem correctness_preserves_keygenUsed
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym) (hs : keygenUsed e s.stA)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (res : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t × GameState onoff Sym)
    (hres : res ∈ support
      ((SCKAScheme.sckaCorrectnessImpl (stageScheme ecEk ecCt0 ecCt1 stage kemMat e s) t).run s)) :
    keygenUsed e res.2.stA := by
  apply SCKAScheme.correctnessImpl_preserves_localInv_at _ (fun stA _ => keygenUsed e stA) s hs
    ?_ ?_ ?_ ?_ t res hres
  · intro key msg epoch next hout
    have hshape := sendA_keygen_shape
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecEk s.stA key msg epoch next hout
    rcases hs with h | ⟨h, _⟩
    · exact Or.inl (by simpa only [hshape.1] using h)
    · exact Or.inr ⟨hshape.1.trans h, hshape.2⟩
  · exact fun _ _ _ _ _ => hs
  · intro msg key epoch next hout
    rw [stageScheme_recvA_eq_ideal] at hout
    have hshape := oppUniKemCKA.Reduction.Internal.recvA_kem_source_shape
      kem onoff (fun _ _ => s.keyB s.stA.t)
      ecCt0 ecCt1 s.stA msg key epoch next hout
    rcases hshape with h | h
    · simpa only [keygenUsed, h.1, h.2.2] using hs
    · apply Or.inl
      rcases hs with hs | ⟨hs, _⟩ <;> omega
  · exact fun _ _ _ _ _ => hs

/-- Single use of the key pair: every query of the stage oracle `stageOracle stage kemMat e b`
preserves `keygenUsed e`. -/
theorem stageOracle_preserves_keygenUsed [SampleableType K]
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) :
    QueryImpl.PreservesInv (stageOracle kem onoff ecEk ecCt0 ecCt1 leak stage kemMat e b)
      (fun s => keygenUsed e s.stA) :=
  securityImplAt_preservesInv kem onoff leak _ _ _ (fun _ _ _ h => h)
    (fun _ => sendArleak_forget (onoff := Pinned.onOff kemMat _ _ _ _) _ _ _)
    (fun _ => sendBrleak_forget (onoff := Pinned.onOff kemMat _ _ _ _) _ _ _ _)
    (SCKAScheme.challOf_recordsChallenges _)
    (fun s hs t => correctness_preserves_keygenUsed kem onoff ecEk ecCt0 ecCt1 leak
      stage kemMat e s hs t)

/-- A's ordinary send holds or generates A's decapsulation key: if A is at `e`, every possible
successor state of the send satisfies `keygenUsed e`. -/
theorem oracleSendA_installs_keygen
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (he : s.stA.t = e)
    (res : Option (ℕ × Option ℕ × Message Sym) ×
      GameState onoff Sym)
    (hres : res ∈ support
      ((SCKAScheme.oracleSendA (stageScheme ecEk ecCt0 ecCt1 stage kemMat e s) ()).run s)) :
    keygenUsed e res.2.stA := by
  simp only [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get,
    StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
    mem_support_bind_iff] at hres
  obtain ⟨out, hout, hres⟩ := hres
  cases out with
  | none => exact False.elim (sendA_none_not_mem_support _ _ ecEk _ hout)
  | some out =>
    rcases out with ⟨key, msg, epoch, next⟩
    have hshape := sendA_keygen_shape
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecEk s.stA key msg epoch next hout
    cases key <;>
      simp only [StateT.run_bind, StateT.run_set, pure_bind,
        StateT.run_pure, mem_support_pure_iff] at hres
    all_goals obtain rfl := hres; exact Or.inr ⟨hshape.1.trans he, hshape.2⟩

/-- If A is at `e` without `dkA` and `e ∉ s.challenged`, A's leaking-send oracle of
`stageScheme stage kemMat e s`, stopped at the first exposure of `e`, answers `none` from `s`. -/
theorem leaking_keygen_stops
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (he : s.stA.t = e) (hfield : s.stA.dkA = none) (hc : e ∉ s.challenged)
    (res : Option (Option (ℕ × Option ℕ × Message Sym ×
      SendRand leak.KeygenRand leak.OffRand leak.OnRand)) ×
      GameState onoff Sym)
    (hres : res ∈ support (((stopOnState
      (SCKAScheme.oracleSendArleak vulnRleakA (stageScheme ecEk ecCt0 ecCt1 stage kemMat e s))
      (fun s => decide (e ∈ s.exposed)) ()).run).run s)) : res.1 = none := by
  apply SCKAScheme.oracleSendArleak_stop_of_exposure _ _ s {e} e ?_ ?_ ?_
    (Finset.mem_singleton_self e) res hres
  · exact sendArleak_none_not_mem_support _ _ ecEk _ _
  · intro key msg epoch next coins hout
    have hex := sendArleak_exposure
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecEk (stageLeak stage kemMat e s)
      s.stA key msg epoch next coins hout
    simpa only [leakEpochsA, hfield, Option.isNone_none,
      Bool.true_or, ↓reduceIte, he] using hex
  · simp [hc]

variable [SampleableType K]

/-- Single use of the key pair: after a query that runs A's key generation of epoch `e`
(`usesKeygen e t s`) in any stage oracle, every possible successor state in which `e` is unexposed
satisfies `keygenUsed e`. -/
theorem stageOracle_keygen_first_use
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain) (s : GameState onoff Sym)
    (hh : usesKeygen e t s = true)
    (res : (securitySpec leak Sym).Range t × GameState onoff Sym)
    (hres : res ∈ support ((stageOracle kem onoff ecEk ecCt0 ecCt1 leak stage kemMat e b t).run s))
    (hcont : decide (e ∈ res.2.exposed) = false) : keygenUsed e res.2.stA := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  all_goals try (rcases t with ((((n | u) | u) | n) | n))
  all_goals try (simp only [usesKeygen, Bool.false_eq_true] at hh)
  all_goals cases u
  · have hhit : s.stA.t = e ∧ s.stA.dkA.isNone := of_decide_eq_true hh
    change res ∈ support
      ((SCKAScheme.oracleSendA (stageScheme ecEk ecCt0 ecCt1 stage kemMat e s) ()).run s) at hres
    exact oracleSendA_installs_keygen kem onoff ecEk ecCt0 ecCt1 leak
      stage kemMat e s hhit.1 res hres
  · have hhit : (s.stA.t = e ∧ s.stA.dkA.isNone) ∧ e ∉ s.challenged :=
      of_decide_eq_true hh
    change res ∈ support ((SCKAScheme.oracleSendArleak vulnRleakA
      (stageScheme ecEk ecCt0 ecCt1 stage kemMat e s) ()).run s) at hres
    have hstop := leaking_keygen_stops kem onoff ecEk ecCt0 ecCt1 leak stage kemMat e s
      hhit.1.1 (Option.isNone_iff_eq_none.mp hhit.1.2) hhit.2 (some res.1, res.2)
      (mem_support_stopOnState_of_mem (SCKAScheme.oracleSendArleak vulnRleakA
        (stageScheme ecEk ecCt0 ecCt1 stage kemMat e s)) (fun s => decide (e ∈ s.exposed)) ()
        s res hres hcont)
    exact absurd hstop (Option.some_ne_none _)

end

section

/-- Averaging of the key pair for A's leaking send: pinning `kg ← leak.keygenRleak` (stage
`.encapsFresh`) gives the output distribution of fresh key generation (stage `.fresh`). -/
theorem sendArleak_sample_keygen_eq_fresh [DecidableEq Sym]
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym) :
    (do
      let pair ← leak.keygenRleak
      (stageScheme ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e s).sendArleak
        s.stA) =ᵈ
    (stageScheme ecEk ecCt0 ecCt1 .fresh kemMat e s).sendArleak s.stA := by
  by_cases he : s.stA.t = e <;> cases hd : s.stA.dkA <;>
    cases hp : s.stA.ekA <;> cases ha : s.stA.ack.ekRec
  all_goals
    simp only [stageScheme, Stage.keygenFlag, scheme, sendArleak, Pinned.leakage,
      hd, hp, ha, he, decide_true, decide_false,
      Bool.false_eq_true, ↓reduceIte, pure_bind, EvalDistEq.refl]
  all_goals
    exact ToVCVio.evalDistEq_bind_of_const' _ fun pair _ => rfl

/-- The version of `sendArleak_sample_keygen_eq_fresh` for A's ordinary send. -/
theorem sendA_sample_keygen_eq_fresh [DecidableEq Sym]
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym) :
    (do
      let pair ← leak.keygenRleak
      (stageScheme ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e s).sendA s.stA) =ᵈ
    (stageScheme ecEk ecCt0 ecCt1 .fresh kemMat e s).sendA s.stA := by
  have h := EvalDistEq.map
    (sendArleak_sample_keygen_eq_fresh kem onoff ecEk ecCt0 ecCt1 leak kemMat e s)
    (fun out => out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))
  rw [map_bind] at h
  simpa only [scheme_sendA_eq_map_sendArleak] using h

/-- B's sends do not read the key pair: for every `kg`, B's leaking send in
`stageScheme .encapsFresh { kemMat with keygen := kg } e s` is that of
`stageScheme .fresh kemMat e s`. -/
theorem sendBrleak_encapsFresh_eq_fresh [DecidableEq Sym]
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (pair : (PK × SK) × leak.KeygenRand) :
    (stageScheme ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e s).sendBrleak
      s.stB =
    (stageScheme ecEk ecCt0 ecCt1 .fresh kemMat e s).sendBrleak s.stB := by
  cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;> cases hc1 : s.stB.ct1 <;>
    cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [stageScheme, scheme, sendBrleak, hc0, hp, hc1, hst, ha, pure_bind,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    all_goals rfl

/-- The version of `sendBrleak_encapsFresh_eq_fresh` for B's ordinary send. -/
theorem sendB_encapsFresh_eq_fresh [DecidableEq Sym]
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (pair : (PK × SK) × leak.KeygenRand) :
    (stageScheme ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e s).sendB s.stB =
    (stageScheme ecEk ecCt0 ecCt1 .fresh kemMat e s).sendB s.stB := by
  rw [scheme_sendB_eq_map_sendBrleak, scheme_sendB_eq_map_sendBrleak,
    sendBrleak_encapsFresh_eq_fresh kem onoff ecEk ecCt0 ecCt1 leak kemMat e s pair]

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Averaging of the key pair for every query: pinning `kg ← leak.keygenRleak` (stage
`.encapsFresh`) gives the response/successor distribution of fresh key generation (stage
`.fresh`). -/
theorem stageOracle_sample_keygen_eq_fresh
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym) :
    (do
      let pair ← leak.keygenRleak
      (stageOracle kem onoff ecEk ecCt0 ecCt1 leak .encapsFresh
        { kemMat with keygen := pair } e b t).run s) =ᵈ
    (stageOracle kem onoff ecEk ecCt0 ecCt1 leak .fresh kemMat e b t).run s :=
  securityImplAt_sample_eq kem onoff leak leak.keygenRleak
    (fun pair => stageScheme ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e)
    (stageScheme ecEk ecCt0 ecCt1 .fresh kemMat e) (SCKAScheme.challOf (adjacentMode e b)) s
    (sendA_sample_keygen_eq_fresh kem onoff ecEk ecCt0 ecCt1 leak kemMat e s)
    (ToVCVio.evalDistEq_bind_of_const' _ fun pair _ =>
      sendB_encapsFresh_eq_fresh kem onoff ecEk ecCt0 ecCt1 leak kemMat e s pair)
    (sendArleak_sample_keygen_eq_fresh kem onoff ecEk ecCt0 ecCt1 leak kemMat e s)
    (ToVCVio.evalDistEq_bind_of_const' _ fun pair _ =>
      sendBrleak_encapsFresh_eq_fresh kem onoff ecEk ecCt0 ecCt1 leak kemMat e s pair)
    (fun pair _ ρ => (stageScheme_recvA_eq_ideal kem onoff ecEk ecCt0 ecCt1 leak .encapsFresh
      { kemMat with keygen := pair } e s ρ).trans
      (stageScheme_recvA_eq_ideal kem onoff ecEk ecCt0 ecCt1 leak .fresh kemMat e s ρ).symm)
    (fun _ _ _ => rfl) t

end

section

variable [DecidableEq Sym]

/-- A's ordinary send does not read the key pair unless it runs key generation: if
`¬(s.stA.t = e ∧ s.stA.dkA.isNone)`, the send in
`stageScheme .encapsFresh { kemMat with keygen := kg } e s` is the same computation for every `kg`.
-/
theorem sendA_keygen_independent
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (hh : ¬(s.stA.t = e ∧ s.stA.dkA.isNone))
    (pair pair' : (PK × SK) × leak.KeygenRand) :
    (stageScheme ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e s).sendA s.stA =
    (stageScheme ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair' } e s).sendA
      s.stA := by
  by_cases he : s.stA.t = e <;> cases hd : s.stA.dkA <;>
    cases hp : s.stA.ekA <;> cases ha : s.stA.ack.ekRec
  all_goals
    simp only [he, hd, Option.isNone_none, Option.isNone_some, Bool.false_eq_true,
      and_true, and_false, not_true_eq_false] at hh
  all_goals
    simp only [stageScheme, Stage.keygenFlag, scheme, sendA, Pinned.kem, Pinned.leakage,
      Pinned.keygen, hd, hp, ha, he, decide_false,
      Bool.false_eq_true, ↓reduceIte, pure_bind]

/-- The version of `sendA_keygen_independent` for A's leaking send. -/
theorem sendArleak_keygen_independent
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (hh : ¬(s.stA.t = e ∧ s.stA.dkA.isNone))
    (pair pair' : (PK × SK) × leak.KeygenRand) :
    (stageScheme ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e s).sendArleak
      s.stA =
    (stageScheme ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair' } e s).sendArleak
      s.stA := by
  by_cases he : s.stA.t = e <;> cases hd : s.stA.dkA <;>
    cases hp : s.stA.ekA <;> cases ha : s.stA.ack.ekRec
  all_goals
    simp only [he, hd, Option.isNone_none, Option.isNone_some, Bool.false_eq_true,
      and_true, and_false, not_true_eq_false] at hh
  all_goals
    simp only [stageScheme, Stage.keygenFlag, scheme, sendArleak, Pinned.kem, Pinned.leakage,
      Pinned.keygen, hd, hp, ha, he, decide_false,
      Bool.false_eq_true, ↓reduceIte, pure_bind]

variable [DecidableEq K]

/-- The version of `leaking_offline_rejected` for A's leaking send running key generation (A at `e`
without `dkA`). -/
theorem leaking_keygen_rejected
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (he : s.stA.t = e) (hfield : s.stA.dkA = none) (hc : e ∈ s.challenged) :
    (SCKAScheme.oracleSendArleak vulnRleakA
      (stageScheme ecEk ecCt0 ecCt1 stage kemMat e s) ()).run s =ᵈ
    (pure (none, s) : ProbComp _) := by
  apply SCKAScheme.oracleSendArleak_rejected_evalDistEq _ _ s {e} ?_ ?_
  · intro key msg epoch next coins hout
    have hex := sendArleak_exposure
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecEk (stageLeak stage kemMat e s)
      s.stA key msg epoch next coins hout
    simpa only [leakEpochsA, hfield, Option.isNone_none, ↓reduceIte, he] using hex
  · simp [hc]

variable [SampleableType K]

/-- Independence of the key pair: a query `t` that does not run A's key generation of `e`
(`usesKeygen e t s = false`) has the same response/successor distribution in the
`encapsFresh` stage oracle for every key pair `kg`. -/
theorem stageOracle_keygen_independent
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym)
    (hh : usesKeygen e t s = false)
    (pair pair' : (PK × SK) × leak.KeygenRand) :
    (stageOracle kem onoff ecEk ecCt0 ecCt1 leak
      .encapsFresh { kemMat with keygen := pair } e b t).run s =ᵈ
    (stageOracle kem onoff ecEk ecCt0 ecCt1 leak
      .encapsFresh { kemMat with keygen := pair' } e b t).run s := by
  rcases t with (((((t | u) | u) | _) | u) | u) <;> try rcases t with ((((n | u) | u) | n) | n)
  all_goals try cases u
  all_goals simp only [stageOracle, securityImplAt, SCKAScheme.securityImplOf,
    QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind,
      StateT.run_get, pure_bind,
    SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
    EvalDistEq.refl]
  · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleSendA_run_congr _ _ s
      (sendA_keygen_independent kem onoff ecEk ecCt0 ecCt1 leak kemMat e s
        (of_decide_eq_false hh) pair pair'))
  · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleSendB_run_congr _ _ s
      ((sendB_encapsFresh_eq_fresh kem onoff ecEk ecCt0 ecCt1 leak kemMat e s pair).trans
        (sendB_encapsFresh_eq_fresh kem onoff ecEk ecCt0 ecCt1 leak kemMat e s pair').symm))
  · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleRecvA_run_congr _ _ s (fun ρ =>
      (stageScheme_recvA_eq_ideal kem onoff ecEk ecCt0 ecCt1 leak .encapsFresh
        { kemMat with keygen := pair } e s ρ).trans
      (stageScheme_recvA_eq_ideal kem onoff ecEk ecCt0 ecCt1 leak .encapsFresh
        { kemMat with keygen := pair' } e s ρ).symm) n)
  · rfl
  · by_cases hready : s.stA.t = e ∧ s.stA.dkA.isNone
    · have hc : e ∈ s.challenged := by
        have hnot : ¬((s.stA.t = e ∧ s.stA.dkA.isNone) ∧ e ∉ s.challenged) :=
          of_decide_eq_false hh
        by_contra hc
        exact hnot ⟨hready, hc⟩
      exact (leaking_keygen_rejected kem onoff ecEk ecCt0 ecCt1 leak .encapsFresh
        { kemMat with keygen := pair } e s hready.1
        (Option.isNone_iff_eq_none.mp hready.2) hc).trans
        (leaking_keygen_rejected kem onoff ecEk ecCt0 ecCt1 leak .encapsFresh
          { kemMat with keygen := pair' } e s hready.1
          (Option.isNone_iff_eq_none.mp hready.2) hc).symm
    · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleSendArleak_run_congr _ _ _ s
        (sendArleak_keygen_independent kem onoff ecEk ecCt0 ecCt1 leak kemMat e s hready
          pair pair'))
  · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleSendBrleak_run_congr _ _ _ s
      ((sendBrleak_encapsFresh_eq_fresh kem onoff ecEk ecCt0 ecCt1 leak kemMat e s pair).trans
        (sendBrleak_encapsFresh_eq_fresh kem onoff ecEk ecCt0 ecCt1 leak kemMat e s pair').symm))

end

section

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Deferral of the key pair: from every state, drawing `kg ← leak.keygenRleak` once before the
`encapsFresh` stage game with key pair `kg` gives the acceptance probability of the `fresh` stage
game, which draws it at A's key generation. -/
theorem stageStopped_keygen_deferred
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym)
    (s : GameState onoff Sym) :
    Pr{let x ← (do
      let keygen ← leak.keygenRleak
      optionRun (stageStopped kem onoff ecEk ecCt0 ecCt1 leak
        .encapsFresh { kemMat with keygen := keygen } e b) adv s)}[x = true] =
    Pr{let x ← (optionRun (stageStopped kem onoff ecEk ecCt0 ecCt1 leak .fresh kemMat e b)
      adv s)}[x = true] :=
  stoppedRun_sample_once_eq leak.keygenRleak
    (fun keygen => stageOracle kem onoff ecEk ecCt0 ecCt1 leak
      .encapsFresh { kemMat with keygen := keygen } e b)
    (stageOracle kem onoff ecEk ecCt0 ecCt1 leak .fresh kemMat e b) (fun s => decide (e ∈
      s.exposed))
    (fun _ => True) (fun s => keygenUsed e s.stA) (usesKeygen e)
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun keygen _ t s _ hu res hres _ => stageOracle_preserves_keygenUsed kem onoff ecEk ecCt0
      ecCt1 leak .encapsFresh { kemMat with keygen := keygen } e b t s hu res hres)
    (fun t s _ hh keygen _ keygen' _ => stageOracle_keygen_independent kem onoff ecEk ecCt0 ecCt1
      leak kemMat e b t s hh keygen keygen')
    (fun t s _ hu => usesKeygen_eq_false_of_used e t s hu)
    (fun keygen _ t s _ hh res hres hcont => stageOracle_keygen_first_use kem onoff ecEk ecCt0
      ecCt1 leak .encapsFresh { kemMat with keygen := keygen } e b t s hh res hres hcont)
    (fun t s _ => stageOracle_sample_keygen_eq_fresh kem onoff ecEk ecCt0 ecCt1 leak kemMat e b t
      s)
    adv s trivial

end

/-! ## The three deferrals combined -/

section

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

include hDet hEk hCt0 hCt1 in
/-- The three deferrals chained from the initial state: drawing the KEM material
`kemMat ← sampleMaterial leak` once before the pinned stage game gives the acceptance probability
of the fully fresh stage game, which draws each sample at its protocol call and is independent of
its material `kemMat₀`:
`Pr[kemMat ← sampleMaterial leak; stageStopped .pinned kemMat e b = true] =
Pr[stageStopped .fresh kemMat₀ e b = true]`. -/
theorem pinnedHybrid_eq_fresh
    (kemMat₀ : KEMMaterial leak) (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym) :
    Pr{let x ← (do
      let kemMat ← sampleMaterial leak
      optionRun (stageStopped kem onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e b) adv
        (oppUniKemCKA.Reduction.Internal.initialGame kem onoff))}[x = true] =
    Pr{let x ← (optionRun
      (stageStopped kem onoff ecEk ecCt0 ecCt1 leak .fresh kemMat₀ e b) adv
      (oppUniKemCKA.Reduction.Internal.initialGame kem onoff))}[x = true] := by
  trans Pr{let x ← (do
    let kg ← leak.keygenRleak
    let off ← leak.encapsOffRleak
    optionRun (stageStopped kem onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { kemMat₀ with keygen := kg, off := off } e b) adv
      (oppUniKemCKA.Reduction.Internal.initialGame kem onoff))}[x = true]
  · simp only [sampleMaterial, bind_assoc, pure_bind]
    rw [map_bind, map_bind]
    refine OracleComp.prEvent_bind_congr_of_support _ _ _ fun kg hkg => ?_
    rw [map_bind, map_bind]
    refine OracleComp.prEvent_bind_congr_of_support _ _ _ fun off hoff => ?_
    obtain ⟨online, hon⟩ := OracleComp.support_nonempty (leak.encapsOnRleak off.1.1 kg.1.1)
    let kemMat : KEMMaterial leak := ⟨kg, off, online⟩
    have hm : kemMat ∈ support (sampleMaterial leak) := by
      simp only [sampleMaterial, mem_support_bind_iff, mem_support_pure_iff]
      exact ⟨kg, hkg, off, hoff, online, hon, rfl⟩
    exact stageStopped_online_deferred kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak kemMat hm e b adv _
      (reachableInv_init kem onoff ecEk ecCt0 ecCt1 ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos)
      (consistentMat_initial kem onoff leak kemMat e)
  trans Pr{let x ← (do
    let kg ← leak.keygenRleak
    optionRun (stageStopped kem onoff ecEk ecCt0 ecCt1 leak
      .encapsFresh { kemMat₀ with keygen := kg } e b) adv
      (oppUniKemCKA.Reduction.Internal.initialGame kem onoff))}[x = true]
  · rw [map_bind, map_bind]
    refine OracleComp.prEvent_bind_congr_of_support _ _ _ fun kg _ => ?_
    exact stageStopped_offline_deferred kem onoff ecEk ecCt0 ecCt1 leak
      { kemMat₀ with keygen := kg } e b adv _
  · exact stageStopped_keygen_deferred kem onoff ecEk ecCt0 ecCt1 leak kemMat₀ e b adv _

include hEk hCt0 hCt1 in
/-- The pinned hybrid `kemMat ← sampleMaterial leak; stageStopped .pinned kemMat e b` has the same
acceptance probability as the ideal game `idealSecurityImpl (adjacentMode e b)` stopped at the
first exposure of `e`. -/
theorem pinnedHybrid_eq_ideal (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym) :
    Pr{let x ← (do
      let kemMat ← sampleMaterial leak
      optionRun (stageStopped kem onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e b) adv
        (oppUniKemCKA.Reduction.Internal.initialGame kem onoff))}[x = true] =
    Pr{let x ← (optionRun
      (stopOnState (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (adjacentMode e b))
        (fun s => decide (e ∈ s.exposed))) adv
      (oppUniKemCKA.Reduction.Internal.initialGame kem onoff))}[x = true] := by
  obtain ⟨kemMat₀, _⟩ := OracleComp.support_nonempty (sampleMaterial leak)
  rw [pinnedHybrid_eq_fresh kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak kemMat₀ e b adv]
  unfold stageStopped
  rw [stageOracle_fresh_eq_ideal kem onoff hDet ecEk ecCt0 ecCt1 leak kemMat₀ e b]

include hEk hCt0 hCt1 in
/-- For `e > 0`, the reduction's fixed branch `fixedBranch adv e b` (`Simulator`) has the same
acceptance probability as the ideal game `idealSecurityImpl (adjacentMode e (!b))` stopped at the
first exposure of `e`. -/
theorem fixedBranch_eq_ideal (e : ℕ) (he : 0 < e)
    (b : Bool) (adv : SecurityAdversary leak Sym) :
    Pr{let x ← fixedBranch kem onoff ecEk ecCt0 ecCt1 leak adv e b}[x = true] =
    Pr{let x ← (optionRun
      (stopOnState (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak
        (adjacentMode e (!b))) (fun s => decide (e ∈ s.exposed))) adv
      (oppUniKemCKA.Reduction.Internal.initialGame kem onoff))}[x = true] := by
  rw [fixedBranch_eq_pinnedHybrid kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak adv e he b]
  exact pinnedHybrid_eq_ideal kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak e (!b) adv

end

end oppUniKemCKA.Security.Embedding
