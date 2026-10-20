/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.HybridGame
import SecureMessaging.SCKA.Security

/-!
# Deferring the online sample

**Setting.** Let `m ∈ support (sampleMaterial leak)` be possible complete material (the outputs
and coins of the three sampling phases of one epoch), `e` a selected epoch, and `b` a mode bit.
The pinned hybrid `hybridOracle m e b` and the stage oracles `oracle .onlineFresh m e b`, which
sample the online encapsulation of epoch `e` at its protocol call, are those of `HybridGame`.
The material `{ m with on := o }`
replaces the online output of `m` by `o`, resampled as
`o ← leak.encapsOnRleak m.off.1.1 m.keygen.1.1` at the stored offline state and public key.
Game states satisfy the transcript invariant `reachableInv` and `pinnedSources m e` (`Game`).

**Definitions.**

- `onlineReady st`: B's next send from local state `st` runs online encapsulation.
- `usesOnline e t s`: query `t` is B's ordinary send, or its leaking send with
  `e ∉ s.challenged`, while B is at `e` with `onlineReady`. It is the test `hit` of
  `stoppedRun_sample_once_eq`, with `used s := (s.keyB e).isSome`.

**Results.**

- `hybridOracle_sample_online_eq_fresh`: for every query, averaging the pinned hybrid
  `hybridOracle { m with on := o } e b` over `o` gives the joint distribution of response and
  successor state of `oracle .onlineFresh m e b`.
- `hybridStopped_online_deferred`: drawing `o` once before the stopped pinned hybrid
  `hybridStopped { m with on := o } e b` gives the acceptance probability of
  `stopped .onlineFresh m e b`.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- B's next send from `s` runs online encapsulation: A has acknowledged `ct_0`
(`ack.ctRec`), B holds A's public key and no online ciphertext, and B holds an offline state or
this send generates one. -/
abbrev onlineReady {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (s : StB onoff Sym) : Prop :=
  s.ack.ctRec = true ∧ s.ekA.isSome ∧ s.ct1.isNone ∧
    (s.ct0.isNone ∨ s.stCt.isSome)

/-- Whether query `t` from `s` runs online encapsulation of epoch `e`: B's ordinary send, or
its leaking send with `e ∉ s.challenged`, while B is at `e` with `onlineReady`. -/
def usesOnline {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (e : ℕ) (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) : Bool :=
  match t with
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ()))))))) =>
    decide (s.stB.t = e ∧ onlineReady s.stB)
  | .inl (.inl (.inl (.inr ()))) =>
    decide ((s.stB.t = e ∧ onlineReady s.stB) ∧ e ∉ s.challenged)
  | _ => false

/-- If `reachableInv s` holds and B's key table has an entry at `e`, then
`usesOnline e t s = false` for every query `t`. -/
theorem usesOnline_eq_false_of_recorded
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (e : ℕ) (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hk : (s.keyB e).isSome) :
    usesOnline e t s = false := by
  have hnot : ¬(s.stB.t = e ∧ onlineReady s.stB) := by
    rintro ⟨he, hready⟩
    have hct : s.stB.ct1 = none := Option.isNone_iff_eq_none.mp hready.2.2.1
    have hnone := (keys_none_before_online base onoff ecEk ecCt0 ecCt1 s hs hct).2
    rw [he] at hnone
    simp only [hnone, Option.isSome_none, Bool.false_eq_true] at hk
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n) <;> simp [usesOnline, hnot]
  all_goals simp [usesOnline, hnot]

/-- `hybridOracle m e b` preserves `(s.keyB e).isSome`. -/
theorem hybridOracle_preserves_keyB_available
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool) :
    QueryImpl.PreservesInv (hybridOracle base onoff ecEk ecCt0 ecCt1 leak m e b)
      (fun s => (s.keyB e).isSome) :=
  securityImplAt_preservesInv base onoff leak _ _ _ (fun _ _ _ h => h)
    (fun _ => sendArleak_forget (onoff := Pinned.onOff m _ _ _ _) _ _ _)
    (fun _ => sendBrleak_forget (onoff := Pinned.onOff m _ _ _ _) _ _ _ _)
    (SCKAScheme.challOf_recordsChallenges _)
    (fun s hs t => SCKAScheme.correctnessImpl_preserves_keyB_available _ e t s hs)

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- If `usesOnline e t s = true`, every possible successor state of query `t` of
`hybridOracle m e b` from `s` in which `e` is unexposed has an entry in B's key table at `e`. -/
theorem hybridOracle_online_records_key
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : usesOnline e t s = true)
    (z : (securitySpec leak Sym).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((hybridOracle base onoff ecEk ecCt0 ecCt1 leak m e b t).run s))
    (hcont : decide (e ∈ z.2.exposed) = false) : (z.2.keyB e).isSome := by
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
      simp only [securityImplAt, hybridOracle, SCKAScheme.sckaCorrectnessImpl,
        SCKAScheme.oracleSendB, honestScheme, scheme, sendB, Pinned.kem,
        Pinned.onOff, Pinned.encapsOff, Pinned.encapsOn, he, ha, hp, hc1, hc0, hst,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, decide_true,
        mem_support_pure_iff] at hz
      obtain rfl := hz
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
      simp only [securityImplAt, hybridOracle, SCKAScheme.oracleSendBrleak,
        honestScheme, scheme, sendBrleak, Pinned.leakage, vulnRleakB,
        he, ha, hp, hc1, hc0, hst, hchall, StateT.run_bind, StateT.run_get,
        StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, decide_true,
        Finset.singleton_inter] at hz
      obtain rfl := hz
      simp at hcont
  · simp only [usesOnline, Bool.false_eq_true] at hh
  · simp only [usesOnline, Bool.false_eq_true] at hh
  · simp only [usesOnline, Bool.false_eq_true] at hh

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq Sym]

/-- Unless B is at `e` with `onlineReady`, B's leaking send in
`honestScheme { m with on := o } e s` is the same computation for every online output `o`. -/
theorem sendBrleak_online_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : ¬(s.stB.t = e ∧ onlineReady s.stB))
    (online online' : (onoff.C₁ × K) × leak.OnRand) :
    (honestScheme ecEk ecCt0 ecCt1
      { m with on := online } e s).sendBrleak s.stB =
    (honestScheme ecEk ecCt0 ecCt1
      { m with on := online' } e s).sendBrleak s.stB := by
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [onlineReady, he, hc0, hp, hc1, hst, ha,
      Option.isSome_none, Option.isSome_some, Option.isNone_none, Option.isNone_some,
      Bool.false_eq_true, and_false, and_true,
      false_or, true_or, or_self, not_true_eq_false] at hh
  all_goals
    simp only [honestScheme, scheme, sendBrleak, hc0, hp, hc1, hst, ha, pure_bind,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Pinned.leakage, he, decide_true, decide_false]

/-- The ordinary-send version of `sendBrleak_online_independent`. -/
theorem sendB_online_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : ¬(s.stB.t = e ∧ onlineReady s.stB))
    (online online' : (onoff.C₁ × K) × leak.OnRand) :
    (honestScheme ecEk ecCt0 ecCt1
      { m with on := online } e s).sendB s.stB =
    (honestScheme ecEk ecCt0 ecCt1
      { m with on := online' } e s).sendB s.stB := by
  rw [scheme_sendB_eq_map_sendBrleak, scheme_sendB_eq_map_sendBrleak,
    sendBrleak_online_independent base onoff ecEk ecCt0 ecCt1 leak m e s hh online online']

/-- If B is at `e` with `onlineReady` and `e ∈ s.challenged`, B's leaking-send oracle of
`honestScheme m e s` rejects from `s`: it is `pure (none, s)`. -/
theorem oracleSendBrleak_online_rejected [DecidableEq K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (he : s.stB.t = e) (hready : onlineReady s.stB) (hc : e ∈ s.challenged) :
    (SCKAScheme.oracleSendBrleak vulnRleakB
      (honestScheme ecEk ecCt0 ecCt1 m e s) ()).run s = pure (none, s) := by
  obtain ⟨ha, hp, hc1, hsrc⟩ := hready
  obtain ⟨pk, hp⟩ := Option.isSome_iff_exists.mp hp
  have hc1 : s.stB.ct1 = none := Option.isNone_iff_eq_none.mp hc1
  cases hc0 : s.stB.ct0 <;> cases hst : s.stB.stCt
  all_goals simp only [hc0, hst, Option.isNone_some, Option.isNone_none,
    Option.isSome_none, Option.isSome_some, Bool.false_eq_true, or_false] at hsrc
  all_goals
    simp [SCKAScheme.oracleSendBrleak, honestScheme, scheme, sendBrleak,
      Pinned.leakage, vulnRleakB, he, ha, hp, hc1, hc0, hst, hc]

variable [DecidableEq K] [SampleableType K]

/-- If `usesOnline e t s = false`, query `t` of `hybridOracle { m with on := o } e b` from `s`
is the same computation for every online output `o`. -/
theorem hybridOracle_online_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : usesOnline e t s = false)
    (online online' : (onoff.C₁ × K) × leak.OnRand) :
    (hybridOracle base onoff ecEk ecCt0 ecCt1 leak { m with on := online } e b t).run s =
    (hybridOracle base onoff ecEk ecCt0 ecCt1 leak { m with on := online' } e b t).run s := by
  rcases t with (((((t | u) | u) | _) | u) | u) <;> try rcases t with ((((n | u) | u) | n) | n)
  all_goals try cases u
  all_goals simp only [hybridOracle, securityImplAt, StateT.run_bind, StateT.run_get, pure_bind,
    SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
  · exact SCKAScheme.oracleSendA_run_congr _ _ s rfl
  · exact SCKAScheme.oracleSendB_run_congr _ _ s
      (sendB_online_independent base onoff ecEk ecCt0 ecCt1 leak m e s
        (of_decide_eq_false hh) online online')
  · exact SCKAScheme.oracleRecvA_run_congr _ _ s (fun ρ =>
      (honest_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak { m with on := online } e s ρ).trans
      (honest_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak
        { m with on := online' } e s ρ).symm) n
  · rfl
  · exact SCKAScheme.oracleSendArleak_run_congr _ _ _ s rfl
  · by_cases hready : s.stB.t = e ∧ onlineReady s.stB
    · have hc : e ∈ s.challenged := by
        have hnot : ¬((s.stB.t = e ∧ onlineReady s.stB) ∧ e ∉ s.challenged) :=
          of_decide_eq_false hh
        by_contra hc
        exact hnot ⟨hready, hc⟩
      exact (oracleSendBrleak_online_rejected base onoff ecEk ecCt0 ecCt1 leak
        { m with on := online } e s hready.1 hready.2 hc).trans
        (oracleSendBrleak_online_rejected base onoff ecEk ecCt0 ecCt1 leak
          { m with on := online' } e s hready.1 hready.2 hc).symm
    · exact SCKAScheme.oracleSendBrleak_run_congr _ _ _ s
        (sendBrleak_online_independent base onoff ecEk ecCt0 ecCt1 leak m e s hready
          online online')

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] in
/-- If `m` is a possible result of `sampleMaterial leak` and `o` a possible result of
`leak.encapsOnRleak m.off.1.1 m.keygen.1.1`, then so is `{ m with on := o }`. -/
theorem sampleMaterial_update_online_mem
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (m : Material leak)
    (hm : m ∈ support (sampleMaterial leak))
    (online : (onoff.C₁ × K) × leak.OnRand)
    (hon : online ∈ support (leak.encapsOnRleak m.off.1.1 m.keygen.1.1)) :
    { m with on := online } ∈ support (sampleMaterial leak) := by
  obtain ⟨hkg, hoff, _⟩ := sampleMaterial_support leak m hm
  simp only [sampleMaterial, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨m.keygen, hkg, m.off, hoff, online, hon, rfl⟩

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Assume `reachableInv s` and `pinnedSources m e s`. If B is at `e` with public key `pk`
and no online ciphertext, then `pk = m.keygen.1.1`. -/
theorem selected_online_public_key
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s)
    (he : s.stB.t = e) (pk : PK) (hp : s.stB.ekA = some pk) (hc1 : s.stB.ct1 = none) :
    pk = m.keygen.1.1 := by
  have ht := epochs_eq_before_online base onoff ecEk ecCt0 ecCt1 s hs hc1
  obtain ⟨T, hT⟩ := hs
  obtain ⟨sk, hpk⟩ := hT.decodedEk pk hp
  have hpair := hT.keypairA
  rw [ht, hpk] at hpair
  have ha : s.stA.ekA = some pk ∧ s.stA.dkA = some sk := by
    cases hpA : s.stA.ekA <;> cases hsA : s.stA.dkA <;> simp_all [Option.map₂]
  exact Option.some.inj (ha.1.symm.trans (hsrc.1 (ht.trans he) (by simp [ha.2])).1)

/-- Assume `reachableInv s` and `pinnedSources m e s`. Averaging B's leaking send in
`honestScheme { m with on := o } e s` over `o ← leak.encapsOnRleak m.off.1.1 m.keygen.1.1`
gives the output distribution of B's leaking send in `schemeAt .onlineFresh m e s`. -/
theorem sendBrleak_sample_online_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s) :
    𝒟[(do
      let online ← leak.encapsOnRleak m.off.1.1 m.keygen.1.1
      (honestScheme ecEk ecCt0 ecCt1 { m with on := online } e s).sendBrleak s.stB)] =
    𝒟[(Sampling.schemeAt ecEk ecCt0 ecCt1 .onlineFresh m e s).sendBrleak s.stB] := by
  have hpub := selected_online_public_key base onoff ecEk ecCt0 ecCt1 leak m e s hs hsrc
  have hoff (he : s.stB.t = e) (st : onoff.St) (hst : s.stB.stCt = some st) :
      st = m.off.1.1 :=
    Option.some.inj (hst.symm.trans (hsrc.2 he (by simp [hst])).1)
  apply evalDist_ext
  intro out
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [honestScheme, Sampling.schemeAt, Sampling.Stage.pinsKeygen,
      Sampling.Stage.pinsOffline, scheme, sendBrleak,
      hc0, hp, hc1, hst, ha, pure_bind, Pinned.leakage,
      he, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.false_eq_true,
      Bool.and_true, ↓reduceIte]
  all_goals
    first
    | solve
      | apply ToVCVio.probOutput_bind_of_const'
        intro online _
        rfl
    | have hpk := hpub he _ hp hc1
      first
      | solve | simp only [hpk]
      | have hstate := hoff he _ hst
        simp only [hpk, hstate]

/-- The ordinary-send version of `sendBrleak_sample_online_eq_fresh`. -/
theorem sendB_sample_online_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s) :
    𝒟[(do
      let online ← leak.encapsOnRleak m.off.1.1 m.keygen.1.1
      (honestScheme ecEk ecCt0 ecCt1 { m with on := online } e s).sendB s.stB)] =
    𝒟[(Sampling.schemeAt ecEk ecCt0 ecCt1 .onlineFresh m e s).sendB s.stB] := by
  have h := evalDist_map_eq_of_evalDist_eq
    (sendBrleak_sample_online_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s hs hsrc)
    (fun out => out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))
  rw [map_bind] at h
  simpa only [scheme_sendB_eq_map_sendBrleak] using h

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Assume `reachableInv s` and `pinnedSources m e s`. For every query `t`, averaging query `t`
of `hybridOracle { m with on := o } e b` from `s` over
`o ← leak.encapsOnRleak m.off.1.1 m.keygen.1.1` gives the joint distribution of response and
successor state of query `t` of `oracle .onlineFresh m e b` from `s`. -/
theorem hybridOracle_sample_online_eq_fresh
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s) :
    𝒟[(do
      let online ← leak.encapsOnRleak m.off.1.1 m.keygen.1.1
      (hybridOracle base onoff ecEk ecCt0 ecCt1 leak { m with on := online } e b t).run s)] =
    𝒟[(Sampling.oracle base onoff ecEk ecCt0 ecCt1 leak .onlineFresh m e b t).run s] :=
  securityImplAt_sample_eq base onoff leak (leak.encapsOnRleak m.off.1.1 m.keygen.1.1)
    (fun online => honestScheme ecEk ecCt0 ecCt1 { m with on := online } e)
    (Sampling.schemeAt ecEk ecCt0 ecCt1 .onlineFresh m e)
    (SCKAScheme.challOf (adjacentMode e b)) s
    (ToVCVio.evalDist_bind_of_const' _ fun _ _ => rfl)
    (sendB_sample_online_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s hs hsrc)
    (ToVCVio.evalDist_bind_of_const' _ fun _ _ => rfl)
    (sendBrleak_sample_online_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s hs hsrc)
    (fun online _ ρ => (honest_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak
      { m with on := online } e s ρ).trans
      (Sampling.recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .onlineFresh m e s ρ).symm)
    (fun _ _ _ => rfl) t

/-- Assume deterministic decapsulation, correct erasure codes, and
`m ∈ support (sampleMaterial leak)`. For every adversary `adv` and state `s` with
`reachableInv s` and `pinnedSources m e s`, drawing
`o ← leak.encapsOnRleak m.off.1.1 m.keygen.1.1` once and running
`optionRun (hybridStopped { m with on := o } e b) adv s` returns `true` with the probability of
`optionRun (stopped .onlineFresh m e b) adv s`. -/
theorem hybridStopped_online_deferred
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ) (b : Bool)
    (adv : SecurityAdversary leak Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s) :
    Pr[= true | do
      let online ← leak.encapsOnRleak m.off.1.1 m.keygen.1.1
      optionRun (hybridStopped base onoff ecEk ecCt0 ecCt1 leak { m with on := online } e b)
        adv s] =
    Pr[= true | optionRun
      (Sampling.stopped base onoff ecEk ecCt0 ecCt1 leak .onlineFresh m e b) adv s] :=
  stoppedRun_sample_once_eq (leak.encapsOnRleak m.off.1.1 m.keygen.1.1)
    (fun online => hybridOracle base onoff ecEk ecCt0 ecCt1 leak { m with on := online } e b)
    (Sampling.oracle base onoff ecEk ecCt0 ecCt1 leak .onlineFresh m e b)
    (fun s => decide (e ∈ s.exposed))
    (fun s => reachableInv base onoff ecEk ecCt0 ecCt1 s ∧ pinnedSources m e s)
    (fun s => (s.keyB e).isSome) (usesOnline e)
    (fun online hon t s hs z hz _ => honestScheme_preserves_simulationInv base onoff hDet
      ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak { m with on := online }
      (sampleMaterial_update_online_mem leak m hm online hon) e _
      (SCKAScheme.challOf_recordsChallenges _) t s hs z hz)
    (fun online _ t s _ hu z hz _ => hybridOracle_preserves_keyB_available base onoff ecEk
      ecCt0 ecCt1 leak { m with on := online } e b t s hu z hz)
    (fun t s _ hh online _ online' _ => congrArg evalDist
      (hybridOracle_online_independent base onoff ecEk ecCt0 ecCt1 leak m e b t s hh
        online online'))
    (fun t s hs hu => usesOnline_eq_false_of_recorded base onoff ecEk ecCt0 ecCt1 leak
      e t s hs.1 hu)
    (fun online _ t s _ hh z hz hcont => hybridOracle_online_records_key base onoff ecEk
      ecCt0 ecCt1 leak { m with on := online } e b t s hh z hz hcont)
    (fun t s hs => hybridOracle_sample_online_eq_fresh base onoff ecEk ecCt0 ecCt1 leak
      m e b t s hs.1 hs.2)
    adv s ⟨hs, hsrc⟩

end oppUniKemCKA.Security.Embedding
