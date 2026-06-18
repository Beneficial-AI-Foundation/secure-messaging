/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Security.PrefixInjectCouplingCore

/-!
# CKA from KEM — Injected-Prefix Coupling, challenged party A

The coupling between the injected prefix and the reduction prefix for a
challenged party A: the pre-injection invariant `preInvA`, the four-phase
relation `coupleRelA`, one step lemma per phase, and the induction
`injectedPrefix_couples_challengePrefix_A` establishing `couplePostA`: both
runs finish, or both pause at the challenge query in the challenge-bridge
shapes.
-/

open OracleSpec OracleComp ENNReal KEMScheme
open OracleComp.ProgramLogic.Relational

namespace kemCKA

variable {K PK SK C : Type}

/-! ## The pre-injection invariant, challenged party A

`preTraceA` pins the counters to the A-first alternation, bounded below the
challenge epoch; it keeps `willChallengeA` false until the injecting send.
`preInvA` combines it with `securityShapeInv`. -/

private def preTraceA
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Prop :=
  match σ.lastAction with
  | none => σ.tA = 0 ∧ σ.tB = 0
  | some .sendA => σ.tA % 2 = 1 ∧ σ.tA = σ.tB + 1 ∧ σ.tA + 2 ≤ gp.challengeEpoch
  | some .recvB => σ.tB % 2 = 1 ∧ σ.tA = σ.tB ∧ σ.tB + 2 ≤ gp.challengeEpoch
  | some .sendB => σ.tB % 2 = 0 ∧ σ.tB = σ.tA + 1 ∧ σ.tB + 3 ≤ gp.challengeEpoch
  | some .recvA => σ.tA % 2 = 0 ∧ σ.tA = σ.tB ∧ σ.tA + 3 ≤ gp.challengeEpoch
  | some .challA | some .challB => False

private def preInvA
    (kem : KEMScheme ProbComp K PK SK C)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Prop :=
  securityShapeInv kem σ ∧ 3 ≤ gp.challengeEpoch ∧ preTraceA gp σ

/-- Inside the pre-injection invariant `willChallengeA` is false: where a
challenge would be a valid next step, the counter is still at least two epochs
below the challenge epoch. -/
private lemma willChallengeA_eq_false_of_preInvA
    (kem : KEMScheme ProbComp K PK SK C)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (hσ : preInvA kem gp σ) :
    willChallengeA gp σ = false := by
  obtain ⟨-, he3, htrace⟩ := hσ
  by_cases hvalid : CKAScheme.validStep σ.lastAction .challA = true
  · have hne : (σ.tA + 1 == gp.challengeEpoch) = false := by
      rw [beq_eq_false_iff_ne]
      cases hlast : σ.lastAction with
      | none =>
          simp only [preTraceA, hlast] at htrace
          omega
      | some act =>
          cases act <;> simp [CKAScheme.validStep, hlast] at hvalid
          case recvA =>
            simp only [preTraceA, hlast] at htrace
            omega
    simp [willChallengeA, hne]
  · simp [willChallengeA, Bool.eq_false_of_not_eq_true hvalid]

/-! ## Preservation of the pre-injection invariant

One lemma per state-changing oracle of `securityImpl`.  Challenge queries are
no-ops inside the invariant (`willChallengeA_eq_false_of_preInvA` and the
party gate), and corruption and adversary-randomness queries do not touch the
state, so they need no preservation lemmas. -/

private lemma preInvA_preserved_sendA [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (hσ : preInvA kem gp σ)
    (z : Option (Message C PK × K) × SecurityState K PK SK C)
    (hz : z ∈ support ((securityImpl kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OSendA : (securitySpec leak).Domain)).run σ)) :
    preInvA kem gp z.2 := by
  obtain ⟨hshape, he3, htrace⟩ := hσ
  change z ∈ support ((CKAScheme.oracleSendA (scheme kem hDet leak) ()).run σ) at hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
  cases hGuard : CKAScheme.validStep last .sendA
  case false =>
    have hzEq : z = (none, ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩) := by
      simpa [CKAScheme.oracleSendA, hGuard, stateT_run] using hz
    subst hzEq
    exact ⟨hshape, he3, htrace⟩
  case true =>
    rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;>
      simp [CKAScheme.validStep] at hGuard
    all_goals (
      rcases (by simpa [securityShapeInv] using hshape) with
        ⟨pk, sk, hks, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [CKAScheme.oracleSendA, StateT.run_bind, StateT.run_get] at hz
      have hz' : ∃ c key pk' sk',
          (c, key) ∈ support (kem.encaps pk) ∧
          (pk', sk') ∈ support kem.keygen ∧
          (some ((c, pk'), key),
            ({ stA := State.recvReady sk', stB := State.recvReady sk,
               rhoA := some (c, pk'), rhoB := none,
               keyA := some key, keyB := none,
               correct := corr, lastAction := some .sendA,
               tA := tA + 1, tB := tB } : SecurityState K PK SK C)) = z := by
        simpa [CKAScheme.validStep, scheme, send] using hz
      obtain ⟨c, key, pk', sk', hck, hks', rfl⟩ := hz'
      refine ⟨?_, he3, ?_⟩
      · exact ⟨pk, sk, c, key, pk', sk', hks, hck, hks', rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp only [preTraceA] at htrace ⊢
        omega)

private lemma preInvA_preserved_recvB [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (hσ : preInvA kem gp σ)
    (z : Unit × SecurityState K PK SK C)
    (hz : z ∈ support ((securityImpl kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run σ)) :
    preInvA kem gp z.2 := by
  obtain ⟨hshape, he3, htrace⟩ := hσ
  change z ∈ support ((CKAScheme.oracleRecvB (scheme kem hDet leak) ()).run σ) at hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
  cases hGuard : CKAScheme.validStep last .recvB
  case false =>
    have hzEq : z = ((), ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩) := by
      simpa [CKAScheme.oracleRecvB, hGuard, stateT_run] using hz
    subst hzEq
    exact ⟨hshape, he3, htrace⟩
  case true =>
    rcases last with _ | action
    · simp [CKAScheme.validStep] at hGuard
    cases action <;> simp [CKAScheme.validStep] at hGuard
    · -- previous action was the A-send carrying the pending message
      rcases (by simpa [securityShapeInv] using hshape) with
        ⟨pk, sk, hks, c, key, hck, pk', sk', hks', rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hdec := decapsDet_eq_some_of_mem_support
        (pk := pk) (sk := sk) (c := c) (key := key) kem hDet hkem hks hck
      have hzEq : z = ((), ⟨State.recvReady sk', State.sendReady pk',
          none, none, none, none, corr, some .recvB, tA, tB + 1⟩) := by
        simpa [CKAScheme.oracleRecvB, CKAScheme.validStep, scheme, recv, hdec,
          stateT_run] using hz
      subst hzEq
      refine ⟨?_, he3, ?_⟩
      · exact ⟨pk', sk', hks', rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp only [preTraceA] at htrace ⊢
        omega
    · -- a challenge never appears as the last action inside the invariant
      exact False.elim (by simp only [securityShapeInv] at hshape)

private lemma preInvA_preserved_recvA [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (hσ : preInvA kem gp σ)
    (z : Unit × SecurityState K PK SK C)
    (hz : z ∈ support ((securityImpl kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run σ)) :
    preInvA kem gp z.2 := by
  obtain ⟨hshape, he3, htrace⟩ := hσ
  change z ∈ support ((CKAScheme.oracleRecvA (scheme kem hDet leak) ()).run σ) at hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
  cases hGuard : CKAScheme.validStep last .recvA
  case false =>
    have hzEq : z = ((), ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩) := by
      simpa [CKAScheme.oracleRecvA, hGuard, stateT_run] using hz
    subst hzEq
    exact ⟨hshape, he3, htrace⟩
  case true =>
    rcases last with _ | action
    · simp [CKAScheme.validStep] at hGuard
    cases action <;> simp [CKAScheme.validStep] at hGuard
    · -- previous action was the B-send carrying the pending message
      rcases (by simpa [securityShapeInv] using hshape) with
        ⟨pk, sk, hks, c, key, hck, pk', sk', hks', rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hdec := decapsDet_eq_some_of_mem_support
        (pk := pk) (sk := sk) (c := c) (key := key) kem hDet hkem hks hck
      have hzEq : z = ((), ⟨State.sendReady pk', State.recvReady sk',
          none, none, none, none, corr, some .recvA, tA + 1, tB⟩) := by
        simpa [CKAScheme.oracleRecvA, CKAScheme.validStep, scheme, recv, hdec,
          stateT_run] using hz
      subst hzEq
      refine ⟨?_, he3, ?_⟩
      · exact ⟨pk', sk', hks', rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp only [preTraceA] at htrace ⊢
        omega
    · -- a challenge never appears as the last action inside the invariant
      exact False.elim (by simp only [securityShapeInv] at hshape)

private lemma preInvA_preserved_sendB_of_not_inject [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hparty : gp.challengedParty = CKAScheme.CKAParty.A)
    (hodd : gp.challengeEpoch % 2 = 1)
    (σ : SecurityState K PK SK C)
    (hσ : preInvA kem gp σ)
    (hnoinj : sendBInjectsChallengeKey gp { σ with tB := σ.tB + 1 } = false)
    (z : Option (Message C PK × K) × SecurityState K PK SK C)
    (hz : z ∈ support ((securityImpl kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OSendB : (securitySpec leak).Domain)).run σ)) :
    preInvA kem gp z.2 := by
  obtain ⟨hshape, he3, htrace⟩ := hσ
  change z ∈ support ((CKAScheme.oracleSendB (scheme kem hDet leak) ()).run σ) at hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
  cases hGuard : CKAScheme.validStep last .sendB
  case false =>
    have hzEq : z = (none, ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩) := by
      simpa [CKAScheme.oracleSendB, hGuard, stateT_run] using hz
    subst hzEq
    exact ⟨hshape, he3, htrace⟩
  case true =>
    rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;>
      simp [CKAScheme.validStep] at hGuard
    have hne : tB + 1 ≠ gp.challengeEpoch - 1 := by
      simpa [sendBInjectsChallengeKey, hparty] using hnoinj
    rcases (by simpa [securityShapeInv] using hshape) with
      ⟨pk, sk, hks, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [CKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
    have hz' : ∃ c key pk' sk',
        (c, key) ∈ support (kem.encaps pk) ∧
        (pk', sk') ∈ support kem.keygen ∧
        (some ((c, pk'), key),
          ({ stA := State.recvReady sk, stB := State.recvReady sk',
             rhoA := none, rhoB := some (c, pk'),
             keyA := none, keyB := some key,
             correct := corr, lastAction := some .sendB,
             tA := tA, tB := tB + 1 } : SecurityState K PK SK C)) = z := by
      simpa [CKAScheme.validStep, scheme, send] using hz
    obtain ⟨c, key, pk', sk', hck, hks', rfl⟩ := hz'
    refine ⟨?_, he3, ?_⟩
    · exact ⟨pk, sk, c, key, pk', sk', hks, hck, hks', rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [preTraceA] at htrace ⊢
      grind

private lemma preInvA_preserved_sendA_rleak [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (hσ : preInvA kem gp σ)
    (z : Option (Message C PK × K × leak.Rand) × SecurityState K PK SK C)
    (hz : z ∈ support ((securityImpl kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run σ)) :
    preInvA kem gp z.2 := by
  obtain ⟨hshape, he3, htrace⟩ := hσ
  change z ∈ support ((CKAScheme.oracleSendA_rleak gp (scheme kem hDet leak) ()).run σ) at hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
  cases hGuard : CKAScheme.validStep last .sendA
  case false =>
    have hzEq : z = (none, ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩) := by
      simpa [CKAScheme.oracleSendA_rleak, hGuard, stateT_run] using hz
    subst hzEq
    exact ⟨hshape, he3, htrace⟩
  case true =>
    by_cases hPCS : max (tA + 1) tB + gp.ΔPCS ≤ gp.challengeEpoch
    · rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;>
        simp [CKAScheme.validStep] at hGuard
      all_goals (
        rcases (by simpa [securityShapeInv] using hshape) with
          ⟨pk, sk, hks, rfl, rfl, rfl, rfl, rfl, rfl⟩
        rw [CKAScheme.oracleSendA_rleak, StateT.run_bind, StateT.run_get] at hz
        have hz' : ∃ c key rEnc pk' sk' rKG,
            ((c, key), rEnc) ∈ support (leak.encaps_rleak pk) ∧
            ((pk', sk'), rKG) ∈ support leak.keygen_rleak ∧
            (some ((c, pk'), key, (rEnc, rKG)),
              ({ stA := State.recvReady sk', stB := State.recvReady sk,
                 rhoA := some (c, pk'), rhoB := none,
                 keyA := some key, keyB := none,
                 correct := corr, lastAction := some .sendA,
                 tA := tA + 1, tB := tB } : SecurityState K PK SK C)) = z := by
          simpa [CKAScheme.validStep, CKAScheme.allowCorrPCS, hPCS, scheme,
            send_rleak] using hz
        obtain ⟨c, key, rEnc, pk', sk', rKG, hck, hks', rfl⟩ := hz'
        refine ⟨?_, he3, ?_⟩
        · exact ⟨pk, sk, c, key, pk', sk', hks,
            mem_support_encaps_of_encaps_rleak kem leak hck,
            mem_support_keygen_of_keygen_rleak kem leak hks',
            rfl, rfl, rfl, rfl, rfl, rfl⟩
        · simp only [preTraceA] at htrace ⊢
          omega)
    · have hzEq : z = (none, ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩) := by
        simpa [CKAScheme.oracleSendA_rleak, hGuard, CKAScheme.allowCorrPCS, hPCS,
          stateT_run] using hz
      subst hzEq
      exact ⟨hshape, he3, htrace⟩

private lemma preInvA_preserved_sendB_rleak [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hΔ : 2 ≤ gp.ΔPCS)
    (hodd : gp.challengeEpoch % 2 = 1)
    (σ : SecurityState K PK SK C)
    (hσ : preInvA kem gp σ)
    (z : Option (Message C PK × K × leak.Rand) × SecurityState K PK SK C)
    (hz : z ∈ support ((securityImpl kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run σ)) :
    preInvA kem gp z.2 := by
  obtain ⟨hshape, he3, htrace⟩ := hσ
  change z ∈ support ((CKAScheme.oracleSendB_rleak gp (scheme kem hDet leak) ()).run σ) at hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
  cases hGuard : CKAScheme.validStep last .sendB
  case false =>
    have hzEq : z = (none, ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩) := by
      simpa [CKAScheme.oracleSendB_rleak, hGuard, stateT_run] using hz
    subst hzEq
    exact ⟨hshape, he3, htrace⟩
  case true =>
    by_cases hPCS : max tA (tB + 1) + gp.ΔPCS ≤ gp.challengeEpoch
    · rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;>
        simp [CKAScheme.validStep] at hGuard
      rcases (by simpa [securityShapeInv] using hshape) with
        ⟨pk, sk, hks, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [CKAScheme.oracleSendB_rleak, StateT.run_bind, StateT.run_get] at hz
      have hz' : ∃ c key rEnc pk' sk' rKG,
          ((c, key), rEnc) ∈ support (leak.encaps_rleak pk) ∧
          ((pk', sk'), rKG) ∈ support leak.keygen_rleak ∧
          (some ((c, pk'), key, (rEnc, rKG)),
            ({ stA := State.recvReady sk, stB := State.recvReady sk',
               rhoA := none, rhoB := some (c, pk'),
               keyA := none, keyB := some key,
               correct := corr, lastAction := some .sendB,
               tA := tA, tB := tB + 1 } : SecurityState K PK SK C)) = z := by
        simpa [CKAScheme.validStep, CKAScheme.allowCorrPCS, hPCS, scheme,
          send_rleak] using hz
      obtain ⟨c, key, rEnc, pk', sk', rKG, hck, hks', rfl⟩ := hz'
      refine ⟨?_, he3, ?_⟩
      · exact ⟨pk, sk, c, key, pk', sk', hks,
          mem_support_encaps_of_encaps_rleak kem leak hck,
          mem_support_keygen_of_keygen_rleak kem leak hks',
          rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp only [preTraceA] at htrace ⊢
        omega
    · have hzEq : z = (none, ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩) := by
        simpa [CKAScheme.oracleSendB_rleak, hGuard, CKAScheme.allowCorrPCS, hPCS,
          stateT_run] using hz
      subst hzEq
      exact ⟨hshape, he3, htrace⟩

/-! ## The coupling relation, challenged party A

The two split prefixes are coupled through four phases.  Before the injecting
send the states are equal and satisfy the pre-injection invariant.  After the
injecting send the states differ exactly in B's stored secret (`skStar` on the
injected side, the discarded fresh draw on the reduction side), and the
recorded message carries `pkStar` together with a ciphertext that decapsulates
correctly under A's current key.  After A receives that message both sides sit
at `sendReady pkStar` waiting for the challenge query.  Once the challenged
party's counter passes the challenge epoch neither side can pause, so no
output tracking is needed. -/

/-- Coupling relation between the injected state `σH` and reduction state `σR`
for the prefix-injection argument when party `A` is challenged. -/
def coupleRelA
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (skStar : SK)
    (σH σR : SecurityState K PK SK C) : Prop :=
  (σH = σR ∧ preInvA kem gp σR)
  ∨ (∃ skA cInj kInj skR,
      σR.stA = State.recvReady skA ∧ σR.stB = State.recvReady skR ∧
      σR.rhoB = some (cInj, pkStar) ∧ σR.keyB = some kInj ∧
      hDet.decapsDet skA cInj = some kInj ∧
      σR.lastAction = some .sendB ∧ σR.tB + 1 = gp.challengeEpoch ∧
      σR.tA + 2 = gp.challengeEpoch ∧
      σH = { σR with stB := State.recvReady skStar })
  ∨ (σR.stA = State.sendReady pkStar ∧ willChallengeA gp σR = true ∧
      epochCounterInv σR ∧ σH = { σR with stB := State.recvReady skStar })
  ∨ (challengePassed gp σH ∧ challengePassed gp σR)

/-- Postcondition of the prefix coupling: either both runs finished, or both
paused at the challenge query with the same continuation, in the state shapes
the challenge bridges expect. -/
def couplePostA
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (skStar : SK) {α : Type} :
    CKAChallengeStepResult leak α × SecurityState K PK SK C →
      CKAChallengeStepResult leak α × SecurityState K PK SK C → Prop :=
  fun z z' =>
    ((∃ a, z.1 = CKAChallengeStepResult.done a) ∧
      (∃ a', z'.1 = CKAChallengeStepResult.done a'))
    ∨ ∃ cont base,
        z = (.pausedA cont, preAToBHonestState base pkStar skStar) ∧
        z' = (.pausedA cont, preAToBReductionState base pkStar) ∧
        epochCounterInv base ∧ willChallengeA gp base = true

/-! ## The coupled oracle steps, phase by phase

One lemma per live phase of `coupleRelA`: stepping the two prefix
implementations from related states gives equal outputs and related states
again.  The splitter-level analysis — the pause and the guards of the
challenge arms — stays in the induction. -/

/-- One coupled oracle step from equal states inside the pre-injection
invariant.  The injecting B-send is the transition into the injected phase;
every other oracle preserves the invariant. -/
private lemma coupleRelA_step_pre [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hparty : gp.challengedParty = CKAScheme.CKAParty.A)
    (hΔ : 2 ≤ gp.ΔPCS)
    (hodd : gp.challengeEpoch % 2 = 1)
    (pkStar : PK) (skStar : SK)
    (t : (securitySpec leak).Domain)
    (σ : SecurityState K PK SK C)
    (hpre : preInvA kem gp σ) :
    RelTriple
      ((securityImplWithChallengeKeyPair kem hDet leak gp false pkStar skStar t).run σ)
      ((prefixImpl kem hDet leak gp pkStar t).run σ)
      (fun p q => p.1 = q.1 ∧ coupleRelA kem hDet gp pkStar skStar p.2 q.2) := by
  have hWA : willChallengeA gp σ = false :=
    willChallengeA_eq_false_of_preInvA kem gp σ hpre
  have hWB : willChallengeB gp σ = false := by
    simp [willChallengeB, hparty]
  rcases t with
    (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
      uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
  all_goals
    try cases uSendA
    try cases uRecvA
    try cases uSendB
    try cases uRecvB
    try cases uChallA
    try cases uChallB
    try cases uCorrA
    try cases uCorrB
    try cases uRLeakA
    try cases uRLeakB
  · -- adversary randomness: the same lifted draw on both sides
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run σ)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run σ) _
    have hrun : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run σ =
        (QueryImpl.ofLift unifSpec ProbComp n >>= fun y => pure (y, σ)) := by
      change (CKAScheme.oracleUnif (State PK SK) K (Message C PK) n).run σ = _
      simp [CKAScheme.oracleUnif, StateT.run_monadLift, monadLift_self]
    rw [hrun]
    refine relTriple_bind (relTriple_refl _) ?_
    intro y y' hy
    cases hy
    exact relTriple_pure_pure ⟨rfl, Or.inl ⟨rfl, hpre⟩⟩
  · -- O-Send-A: the inject guard is off for an A-challenge
    change RelTriple
      ((oracleSendAWithChallengeKeyPair kem gp pkStar skStar ()).run σ)
      ((oracleSendAWithChallengePk kem gp pkStar ()).run σ) _
    have hg : sendAInjectsChallengeKey gp { σ with tA := σ.tA + 1 } = false := by
      simp [sendAInjectsChallengeKey, hparty]
    rw [oracleSendAWithChallengeKeyPair_run_eq_of_not_inject kem hDet leak gp pkStar
        skStar σ hg,
      oracleSendAWithChallengePk_run_eq_of_not_inject kem hDet leak gp pkStar σ hg]
    exact relTriple_refl_support_post fun p hsup => ⟨rfl, Or.inl ⟨rfl,
      preInvA_preserved_sendA kem hDet leak gp σ hpre p hsup⟩⟩
  · -- O-Recv-A: the same oracle on the same state
    exact relTriple_refl_support_post fun p hsup => ⟨rfl, Or.inl ⟨rfl,
      preInvA_preserved_recvA kem hDet leak hkem gp σ hpre p hsup⟩⟩
  · -- O-Send-B: the injecting send when the guard fires, honest otherwise
    change RelTriple
      ((oracleSendBWithChallengeKeyPair kem gp pkStar skStar ()).run σ)
      ((oracleSendBWithChallengePk kem gp pkStar ()).run σ) _
    by_cases hgB : sendBInjectsChallengeKey gp { σ with tB := σ.tB + 1 } = true
    · by_cases hvalid : CKAScheme.validStep σ.lastAction .sendB = true
      · -- the injecting send: enter the injected phase
        obtain ⟨hshape, he3, htrace⟩ := hpre
        rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
        rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;>
          simp [CKAScheme.validStep] at hvalid
        rcases (by simpa [securityShapeInv] using hshape) with
          ⟨pk, sk, hks, rfl, rfl, rfl, rfl, rfl, rfl⟩
        simp only [preTraceA] at htrace
        have htBe : tB + 1 = gp.challengeEpoch - 1 := by
          simpa [sendBInjectsChallengeKey, hparty] using hgB
        rw [oracleSendBWithChallengeKeyPair_run_sendReady kem gp pkStar skStar
            ⟨State.recvReady sk, State.sendReady pk, none, none, none, none, corr,
              some .recvB, tA, tB⟩ pk rfl rfl,
          oracleSendBWithChallengePk_run_sendReady kem gp pkStar
            ⟨State.recvReady sk, State.sendReady pk, none, none, none, none, corr,
              some .recvB, tA, tB⟩ pk rfl rfl]
        simp only [hgB, ↓reduceIte]
        refine relTriple_bind (relTriple_refl_support (kem.encaps pk)) ?_
        rintro ck ck' ⟨rfl, hck⟩
        obtain ⟨c, key⟩ := ck
        refine relTriple_bind (relTriple_refl_support kem.keygen) ?_
        rintro ks ks' ⟨rfl, hks'⟩
        obtain ⟨pkG, skG⟩ := ks
        have hdec : hDet.decapsDet sk c = some key :=
          decapsDet_eq_some_of_mem_support kem hDet hkem hks hck
        exact relTriple_pure_pure ⟨rfl, Or.inr (Or.inl ⟨sk, c, key, skG, rfl, rfl,
          rfl, rfl, hdec, rfl, (show tB + 1 + 1 = gp.challengeEpoch by omega),
          (show tA + 2 = gp.challengeEpoch by omega), rfl⟩)⟩
      · -- the guard fired on an invalid step: both sides are no-ops
        have hF : CKAScheme.validStep σ.lastAction .sendB = false :=
          Bool.eq_false_of_not_eq_true hvalid
        have hH : (oracleSendBWithChallengeKeyPair kem gp pkStar skStar ()).run σ =
            pure (none, σ) := by
          simp [oracleSendBWithChallengeKeyPair, hF]
        have hR : (oracleSendBWithChallengePk kem gp pkStar ()).run σ =
            pure (none, σ) := by
          simp [oracleSendBWithChallengePk, hF]
        rw [hH, hR]
        exact relTriple_pure_pure ⟨rfl, Or.inl ⟨rfl, hpre⟩⟩
    · -- ordinary B-send: both sides generate honestly
      have hg : sendBInjectsChallengeKey gp { σ with tB := σ.tB + 1 } = false :=
        Bool.eq_false_of_not_eq_true hgB
      rw [oracleSendBWithChallengeKeyPair_run_eq_of_not_inject kem hDet leak gp pkStar
          skStar σ hg,
        oracleSendBWithChallengePk_run_eq_of_not_inject kem hDet leak gp pkStar σ hg]
      exact relTriple_refl_support_post fun p hsup => ⟨rfl, Or.inl ⟨rfl,
        preInvA_preserved_sendB_of_not_inject kem hDet leak gp hparty hodd σ hpre hg
          p hsup⟩⟩
  · -- O-Recv-B: the same oracle on the same state
    exact relTriple_refl_support_post fun p hsup => ⟨rfl, Or.inl ⟨rfl,
      preInvA_preserved_recvB kem hDet leak hkem gp σ hpre p hsup⟩⟩
  · -- O-Chall-A: the guard is false inside the invariant
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σ)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σ) _
    rw [securityImpl_challA_run_of_not_will kem hDet leak gp false σ hWA]
    exact relTriple_pure_pure ⟨rfl, Or.inl ⟨rfl, hpre⟩⟩
  · -- O-Chall-B: wrong party, the guard is false
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σ)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σ) _
    rw [securityImpl_challB_run_of_not_will kem hDet leak gp false σ hWB]
    exact relTriple_pure_pure ⟨rfl, Or.inl ⟨rfl, hpre⟩⟩
  · -- O-Corrupt-A: never writes the state
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run σ)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run σ) _
    have hrun : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run σ =
        pure (if CKAScheme.allowCorr gp σ .A then some σ.stA else none, σ) := by
      change (CKAScheme.oracleCorruptA gp (State PK SK) K (Message C PK) ()).run σ = _
      cases h : CKAScheme.allowCorr gp σ .A <;> simp [CKAScheme.oracleCorruptA, h]
    rw [hrun]
    exact relTriple_pure_pure ⟨rfl, Or.inl ⟨rfl, hpre⟩⟩
  · -- O-Corrupt-B: never writes the state
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run σ)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run σ) _
    have hrun : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run σ =
        pure (if CKAScheme.allowCorr gp σ .B then some σ.stB else none, σ) := by
      change (CKAScheme.oracleCorruptB gp (State PK SK) K (Message C PK) ()).run σ = _
      cases h : CKAScheme.allowCorr gp σ .B <;> simp [CKAScheme.oracleCorruptB, h]
    rw [hrun]
    exact relTriple_pure_pure ⟨rfl, Or.inl ⟨rfl, hpre⟩⟩
  · -- O-Send-A-rleak: the same oracle on the same state
    exact relTriple_refl_support_post fun p hsup => ⟨rfl, Or.inl ⟨rfl,
      preInvA_preserved_sendA_rleak kem hDet leak gp σ hpre p hsup⟩⟩
  · -- O-Send-B-rleak: the same oracle on the same state
    exact relTriple_refl_support_post fun p hsup => ⟨rfl, Or.inl ⟨rfl,
      preInvA_preserved_sendB_rleak kem hDet leak gp hΔ hodd σ hpre p hsup⟩⟩

/-- One coupled oracle step in the injected phase.  The states differ exactly
in B's stored secret; A's receive of the injected message is the transition
into the challenge phase, every other oracle is a no-op or leaves the
divergent slot untouched. -/
private lemma coupleRelA_step_inj [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hparty : gp.challengedParty = CKAScheme.CKAParty.A)
    (hΔ : 2 ≤ gp.ΔPCS)
    (hFS : gp.ΔFS = 0)
    (pkStar : PK) (skStar : SK)
    (skA : SK) (cInj : C) (kInj : K) (skR : SK)
    (ρA : Option (Message C PK)) (kA : Option K) (corr : Bool) (tA tB : ℕ)
    (hdec : hDet.decapsDet skA cInj = some kInj)
    (htB : tB + 1 = gp.challengeEpoch)
    (htA : tA + 2 = gp.challengeEpoch)
    (t : (securitySpec leak).Domain) :
    RelTriple
      ((securityImplWithChallengeKeyPair kem hDet leak gp false pkStar skStar t).run
        ⟨State.recvReady skA, State.recvReady skStar, ρA, some (cInj, pkStar),
          kA, some kInj, corr, some CKAScheme.CKAAction.sendB, tA, tB⟩)
      ((prefixImpl kem hDet leak gp pkStar t).run
        ⟨State.recvReady skA, State.recvReady skR, ρA, some (cInj, pkStar),
          kA, some kInj, corr, some CKAScheme.CKAAction.sendB, tA, tB⟩)
      (fun p q => p.1 = q.1 ∧ coupleRelA kem hDet gp pkStar skStar p.2 q.2) := by
  set σHl : SecurityState K PK SK C :=
    ⟨State.recvReady skA, State.recvReady skStar, ρA, some (cInj, pkStar),
      kA, some kInj, corr, some CKAScheme.CKAAction.sendB, tA, tB⟩ with hσHl
  set σRl : SecurityState K PK SK C :=
    ⟨State.recvReady skA, State.recvReady skR, ρA, some (cInj, pkStar),
      kA, some kInj, corr, some CKAScheme.CKAAction.sendB, tA, tB⟩ with hσRl
  have hrelSame : coupleRelA kem hDet gp pkStar skStar σHl σRl :=
    Or.inr (Or.inl ⟨skA, cInj, kInj, skR, rfl, rfl, rfl, rfl, hdec, rfl, htB, htA, rfl⟩)
  rcases t with
    (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
      uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
  all_goals
    try cases uSendA
    try cases uRecvA
    try cases uSendB
    try cases uRecvB
    try cases uChallA
    try cases uChallB
    try cases uCorrA
    try cases uCorrB
    try cases uRLeakA
    try cases uRLeakB
  · -- adversary randomness
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run σRl) _
    have hrun : ∀ σ : SecurityState K PK SK C,
        (securityImpl kem hDet leak gp false
          (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run σ =
        (QueryImpl.ofLift unifSpec ProbComp n >>= fun y => pure (y, σ)) := by
      intro σ
      change (CKAScheme.oracleUnif (State PK SK) K (Message C PK) n).run σ = _
      simp [CKAScheme.oracleUnif, StateT.run_monadLift, monadLift_self]
    rw [hrun σHl, hrun σRl]
    refine relTriple_bind (relTriple_refl _) ?_
    intro y y' hy
    cases hy
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Send-A: not A's turn
    change RelTriple
      ((oracleSendAWithChallengeKeyPair kem gp pkStar skStar ()).run σHl)
      ((oracleSendAWithChallengePk kem gp pkStar ()).run σRl) _
    have hH : (oracleSendAWithChallengeKeyPair kem gp pkStar skStar ()).run σHl =
        pure (none, σHl) := by
      simp [oracleSendAWithChallengeKeyPair, CKAScheme.validStep, hσHl]
    have hR : (oracleSendAWithChallengePk kem gp pkStar ()).run σRl =
        pure (none, σRl) := by
      simp [oracleSendAWithChallengePk, CKAScheme.validStep, hσRl]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Recv-A: A receives the injected message; enter the challenge phase
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run σRl) _
    have hH : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run σHl =
        pure ((), ⟨State.sendReady pkStar, State.recvReady skStar, ρA, none,
          kA, none, corr, some CKAScheme.CKAAction.recvA, tA + 1, tB⟩) := by
      change (CKAScheme.oracleRecvA (scheme kem hDet leak) ()).run σHl = _
      simp [CKAScheme.oracleRecvA, CKAScheme.validStep, scheme, recv, hdec, hσHl]
    have hR : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run σRl =
        pure ((), ⟨State.sendReady pkStar, State.recvReady skR, ρA, none,
          kA, none, corr, some CKAScheme.CKAAction.recvA, tA + 1, tB⟩) := by
      change (CKAScheme.oracleRecvA (scheme kem hDet leak) ()).run σRl = _
      simp [CKAScheme.oracleRecvA, CKAScheme.validStep, scheme, recv, hdec, hσRl]
    rw [hH, hR]
    refine relTriple_pure_pure ⟨rfl, Or.inr (Or.inr (Or.inl ⟨rfl, ?_, ?_, rfl⟩))⟩
    · simp [willChallengeA, CKAScheme.validStep, hparty]
      omega
    · simp only [epochCounterInv]
      omega
  · -- O-Send-B: not B's turn
    change RelTriple
      ((oracleSendBWithChallengeKeyPair kem gp pkStar skStar ()).run σHl)
      ((oracleSendBWithChallengePk kem gp pkStar ()).run σRl) _
    have hH : (oracleSendBWithChallengeKeyPair kem gp pkStar skStar ()).run σHl =
        pure (none, σHl) := by
      simp [oracleSendBWithChallengeKeyPair, CKAScheme.validStep, hσHl]
    have hR : (oracleSendBWithChallengePk kem gp pkStar ()).run σRl =
        pure (none, σRl) := by
      simp [oracleSendBWithChallengePk, CKAScheme.validStep, hσRl]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Recv-B: not a receive slot
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run σRl) _
    have hH : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run σHl =
        pure ((), σHl) := by
      change (CKAScheme.oracleRecvB (scheme kem hDet leak) ()).run σHl = _
      simp [CKAScheme.oracleRecvB, CKAScheme.validStep, hσHl]
    have hR : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run σRl =
        pure ((), σRl) := by
      change (CKAScheme.oracleRecvB (scheme kem hDet leak) ()).run σRl = _
      simp [CKAScheme.oracleRecvB, CKAScheme.validStep, hσRl]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Chall-A: the guard is false right after the injecting send
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σRl) _
    have hWAH : willChallengeA gp σHl = false := by
      simp [willChallengeA, CKAScheme.validStep, hσHl]
    have hWAR : willChallengeA gp σRl = false := by
      simp [willChallengeA, CKAScheme.validStep, hσRl]
    rw [securityImpl_challA_run_of_not_will kem hDet leak gp false σHl hWAH,
      securityImpl_challA_run_of_not_will kem hDet leak gp false σRl hWAR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Chall-B: wrong party
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σRl) _
    have hWBH : willChallengeB gp σHl = false := by
      simp [willChallengeB, hparty]
    have hWBR : willChallengeB gp σRl = false := by
      simp [willChallengeB, hparty]
    rw [securityImpl_challB_run_of_not_will kem hDet leak gp false σHl hWBH,
      securityImpl_challB_run_of_not_will kem hDet leak gp false σRl hWBR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Corrupt-A: A's state is shared; the outputs agree
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run σRl) _
    have hrun : ∀ σ : SecurityState K PK SK C,
        (securityImpl kem hDet leak gp false
          (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run σ =
        pure (if CKAScheme.allowCorr gp σ .A then some σ.stA else none, σ) := by
      intro σ
      change (CKAScheme.oracleCorruptA gp (State PK SK) K (Message C PK) ()).run σ = _
      cases h : CKAScheme.allowCorr gp σ .A <;> simp [CKAScheme.oracleCorruptA, h]
    rw [hrun σHl, hrun σRl,
      show (if CKAScheme.allowCorr gp σHl .A then some σHl.stA else none) =
        (if CKAScheme.allowCorr gp σRl .A then some σRl.stA else none) from rfl]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Corrupt-B: gated off one epoch before the challenge
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run σRl) _
    have htBpred : tB = gp.challengeEpoch - 1 := by omega
    have hpcs : CKAScheme.allowCorrPCS gp σRl = false :=
      allowCorrPCS_false_of_two_le_deltaPCS_of_tB_pred gp σRl hΔ htBpred
    have hcB : CKAScheme.allowCorr gp σRl .B = false := by
      simp [CKAScheme.allowCorr, hpcs, CKAScheme.allowCorrFS, hFS,
        (show σRl.tB = tB from rfl)]
      omega
    have hrun : ∀ σ : SecurityState K PK SK C,
        (securityImpl kem hDet leak gp false
          (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run σ =
        pure (if CKAScheme.allowCorr gp σ .B then some σ.stB else none, σ) := by
      intro σ
      change (CKAScheme.oracleCorruptB gp (State PK SK) K (Message C PK) ()).run σ = _
      cases h : CKAScheme.allowCorr gp σ .B <;> simp [CKAScheme.oracleCorruptB, h]
    rw [hrun σHl, hrun σRl,
      show CKAScheme.allowCorr gp σHl .B = CKAScheme.allowCorr gp σRl .B from rfl,
      hcB]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Send-A-rleak: not a send slot
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run σRl)
      _
    have hH : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run
        σHl = pure (none, σHl) := by
      change (CKAScheme.oracleSendA_rleak gp (scheme kem hDet leak) ()).run σHl = _
      simp [CKAScheme.oracleSendA_rleak, CKAScheme.validStep, hσHl]
    have hR : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run
        σRl = pure (none, σRl) := by
      change (CKAScheme.oracleSendA_rleak gp (scheme kem hDet leak) ()).run σRl = _
      simp [CKAScheme.oracleSendA_rleak, CKAScheme.validStep, hσRl]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Send-B-rleak: not a send slot
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run σRl)
      _
    have hH : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run
        σHl = pure (none, σHl) := by
      change (CKAScheme.oracleSendB_rleak gp (scheme kem hDet leak) ()).run σHl = _
      simp [CKAScheme.oracleSendB_rleak, CKAScheme.validStep, hσHl]
    have hR : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run
        σRl = pure (none, σRl) := by
      change (CKAScheme.oracleSendB_rleak gp (scheme kem hDet leak) ()).run σRl = _
      simp [CKAScheme.oracleSendB_rleak, CKAScheme.validStep, hσRl]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩

/-- One coupled oracle step in the challenge phase.  Both sides sit at
`sendReady pkStar`; an ordinary A-send or a fired challenge query moves both
past the challenge epoch, everything else is a no-op or leaves the divergent
slot untouched. -/
private lemma coupleRelA_step_chall [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hparty : gp.challengedParty = CKAScheme.CKAParty.A)
    (hΔ : 2 ≤ gp.ΔPCS)
    (hFS : gp.ΔFS = 0)
    (pkStar : PK) (skStar : SK)
    (sB : State PK SK) (ρA ρB : Option (Message C PK)) (kA kB : Option K)
    (corr : Bool) (last : Option CKAScheme.CKAAction) (tA tB : ℕ)
    (hWill : willChallengeA gp
      (⟨State.sendReady pkStar, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩ :
        SecurityState K PK SK C) = true)
    (hInv : epochCounterInv
      (⟨State.sendReady pkStar, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩ :
        SecurityState K PK SK C))
    (t : (securitySpec leak).Domain) :
    RelTriple
      ((securityImplWithChallengeKeyPair kem hDet leak gp false pkStar skStar t).run
        ⟨State.sendReady pkStar, State.recvReady skStar, ρA, ρB, kA, kB, corr,
          last, tA, tB⟩)
      ((prefixImpl kem hDet leak gp pkStar t).run
        ⟨State.sendReady pkStar, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩)
      (fun p q => p.1 = q.1 ∧ coupleRelA kem hDet gp pkStar skStar p.2 q.2) := by
  set σHl : SecurityState K PK SK C :=
    ⟨State.sendReady pkStar, State.recvReady skStar, ρA, ρB, kA, kB, corr,
      last, tA, tB⟩ with hσHl
  set σRl : SecurityState K PK SK C :=
    ⟨State.sendReady pkStar, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩ with hσRl
  have hrelSame : coupleRelA kem hDet gp pkStar skStar σHl σRl :=
    Or.inr (Or.inr (Or.inl ⟨rfl, hWill, hInv, rfl⟩))
  obtain ⟨hvalidChall, htAe⟩ : CKAScheme.validStep last .challA = true ∧
      tA + 1 = gp.challengeEpoch := by
    simpa [willChallengeA, hparty] using hWill
  have hlastD : last = none ∨ last = some CKAScheme.CKAAction.recvA := by
    cases hl : last with
    | none => exact Or.inl rfl
    | some act =>
        cases act <;> simp [CKAScheme.validStep, hl] at hvalidChall
        exact Or.inr rfl
  have htAB : tA = tB := by
    rcases hlastD with rfl | rfl <;> simpa [epochCounterInv] using hInv
  rcases t with
    (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
      uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
  all_goals
    try cases uSendA
    try cases uRecvA
    try cases uSendB
    try cases uRecvB
    try cases uChallA
    try cases uChallB
    try cases uCorrA
    try cases uCorrB
    try cases uRLeakA
    try cases uRLeakB
  · -- adversary randomness
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run σRl) _
    have hrun : ∀ σ : SecurityState K PK SK C,
        (securityImpl kem hDet leak gp false
          (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run σ =
        (QueryImpl.ofLift unifSpec ProbComp n >>= fun y => pure (y, σ)) := by
      intro σ
      change (CKAScheme.oracleUnif (State PK SK) K (Message C PK) n).run σ = _
      simp [CKAScheme.oracleUnif, StateT.run_monadLift, monadLift_self]
    rw [hrun σHl, hrun σRl]
    refine relTriple_bind (relTriple_refl _) ?_
    intro y y' hy
    cases hy
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Send-A: the adversary skips the challenge; both counters pass the epoch
    change RelTriple
      ((oracleSendAWithChallengeKeyPair kem gp pkStar skStar ()).run σHl)
      ((oracleSendAWithChallengePk kem gp pkStar ()).run σRl) _
    have hvalidA : CKAScheme.validStep last .sendA = true := by
      rcases hlastD with rfl | rfl <;> rfl
    have hgH : sendAInjectsChallengeKey gp { σHl with tA := σHl.tA + 1 } = false := by
      simp [sendAInjectsChallengeKey, hparty]
    have hgR : sendAInjectsChallengeKey gp { σRl with tA := σRl.tA + 1 } = false := by
      simp [sendAInjectsChallengeKey, hparty]
    rw [oracleSendAWithChallengeKeyPair_run_sendReady kem gp pkStar skStar σHl pkStar
        hvalidA rfl,
      oracleSendAWithChallengePk_run_sendReady kem gp pkStar σRl pkStar hvalidA rfl]
    simp only [hgH, hgR, Bool.false_eq_true, ↓reduceIte]
    refine relTriple_bind (relTriple_refl_support (kem.encaps pkStar)) ?_
    rintro ck ck' ⟨rfl, hck⟩
    obtain ⟨c, key⟩ := ck
    refine relTriple_bind (relTriple_refl_support kem.keygen) ?_
    rintro ks ks' ⟨rfl, hks'⟩
    obtain ⟨pkG, skG⟩ := ks
    refine relTriple_pure_pure ⟨rfl, Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))⟩ <;>
      · simp only [challengePassed, hparty, hσHl, hσRl]
        omega
  · -- O-Recv-A: not a receive slot
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run σRl) _
    have hvF : CKAScheme.validStep last .recvA = false := by
      rcases hlastD with rfl | rfl <;> rfl
    have hH : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run σHl =
        pure ((), σHl) := by
      change (CKAScheme.oracleRecvA (scheme kem hDet leak) ()).run σHl = _
      simp [CKAScheme.oracleRecvA, hσHl, hvF]
    have hR : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run σRl =
        pure ((), σRl) := by
      change (CKAScheme.oracleRecvA (scheme kem hDet leak) ()).run σRl = _
      simp [CKAScheme.oracleRecvA, hσRl, hvF]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Send-B: not B's turn
    change RelTriple
      ((oracleSendBWithChallengeKeyPair kem gp pkStar skStar ()).run σHl)
      ((oracleSendBWithChallengePk kem gp pkStar ()).run σRl) _
    have hvF : CKAScheme.validStep last .sendB = false := by
      rcases hlastD with rfl | rfl <;> rfl
    have hH : (oracleSendBWithChallengeKeyPair kem gp pkStar skStar ()).run σHl =
        pure (none, σHl) := by
      simp [oracleSendBWithChallengeKeyPair, hσHl, hvF]
    have hR : (oracleSendBWithChallengePk kem gp pkStar ()).run σRl =
        pure (none, σRl) := by
      simp [oracleSendBWithChallengePk, hσRl, hvF]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Recv-B: not a receive slot
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run σRl) _
    have hvF : CKAScheme.validStep last .recvB = false := by
      rcases hlastD with rfl | rfl <;> rfl
    have hH : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run σHl =
        pure ((), σHl) := by
      change (CKAScheme.oracleRecvB (scheme kem hDet leak) ()).run σHl = _
      simp [CKAScheme.oracleRecvB, hσHl, hvF]
    have hR : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run σRl =
        pure ((), σRl) := by
      change (CKAScheme.oracleRecvB (scheme kem hDet leak) ()).run σRl = _
      simp [CKAScheme.oracleRecvB, hσRl, hvF]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Chall-A: the challenge fires at the implementation level on both sides
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σRl) _
    have hrun : ∀ st : State PK SK,
        (securityImpl kem hDet leak gp false
          (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
          ⟨State.sendReady pkStar, st, ρA, ρB, kA, kB, corr, last, tA, tB⟩ =
        (do
          let (c, key) ← kem.encaps pkStar
          let (pkG, skG) ← kem.keygen
          pure (some ((c, pkG), key),
            (⟨State.recvReady skG, st, some (c, pkG), ρB, some key, kB, corr,
              some CKAScheme.CKAAction.challA, tA + 1, tB⟩ :
              SecurityState K PK SK C))) := by
      intro st
      change (CKAScheme.oracleChallA gp false (scheme kem hDet leak) ()).run _ = _
      simp [CKAScheme.oracleChallA, hvalidChall, CKAScheme.isChallengeEpoch,
        CKAScheme.GameState.tP, hparty, htAe, scheme, send]
      rfl
    rw [show σHl = ⟨State.sendReady pkStar, State.recvReady skStar, ρA, ρB, kA, kB,
        corr, last, tA, tB⟩ from rfl,
      show σRl = ⟨State.sendReady pkStar, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
        from rfl,
      hrun (State.recvReady skStar), hrun sB]
    refine relTriple_bind (relTriple_refl_support (kem.encaps pkStar)) ?_
    rintro ck ck' ⟨rfl, hck⟩
    obtain ⟨c, key⟩ := ck
    refine relTriple_bind (relTriple_refl_support kem.keygen) ?_
    rintro ks ks' ⟨rfl, hks'⟩
    obtain ⟨pkG, skG⟩ := ks
    refine relTriple_pure_pure ⟨rfl, Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))⟩ <;>
      · simp only [challengePassed, hparty]
        omega
  · -- O-Chall-B: wrong party
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σRl) _
    have hWBH : willChallengeB gp σHl = false := by
      simp [willChallengeB, hparty]
    have hWBR : willChallengeB gp σRl = false := by
      simp [willChallengeB, hparty]
    rw [securityImpl_challB_run_of_not_will kem hDet leak gp false σHl hWBH,
      securityImpl_challB_run_of_not_will kem hDet leak gp false σRl hWBR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Corrupt-A: A's state is shared; the outputs agree
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run σRl) _
    have hrun : ∀ σ : SecurityState K PK SK C,
        (securityImpl kem hDet leak gp false
          (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run σ =
        pure (if CKAScheme.allowCorr gp σ .A then some σ.stA else none, σ) := by
      intro σ
      change (CKAScheme.oracleCorruptA gp (State PK SK) K (Message C PK) ()).run σ = _
      cases h : CKAScheme.allowCorr gp σ .A <;> simp [CKAScheme.oracleCorruptA, h]
    rw [hrun σHl, hrun σRl,
      show (if CKAScheme.allowCorr gp σHl .A then some σHl.stA else none) =
        (if CKAScheme.allowCorr gp σRl .A then some σRl.stA else none) from rfl]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Corrupt-B: gated off one epoch before the challenge
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run σRl) _
    have htBpred : tB = gp.challengeEpoch - 1 := by omega
    have hpcs : CKAScheme.allowCorrPCS gp σRl = false :=
      allowCorrPCS_false_of_two_le_deltaPCS_of_tB_pred gp σRl hΔ htBpred
    have hcB : CKAScheme.allowCorr gp σRl .B = false := by
      simp [CKAScheme.allowCorr, hpcs, CKAScheme.allowCorrFS, hFS,
        (show σRl.tB = tB from rfl)]
      omega
    have hrun : ∀ σ : SecurityState K PK SK C,
        (securityImpl kem hDet leak gp false
          (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run σ =
        pure (if CKAScheme.allowCorr gp σ .B then some σ.stB else none, σ) := by
      intro σ
      change (CKAScheme.oracleCorruptB gp (State PK SK) K (Message C PK) ()).run σ = _
      cases h : CKAScheme.allowCorr gp σ .B <;> simp [CKAScheme.oracleCorruptB, h]
    rw [hrun σHl, hrun σRl,
      show CKAScheme.allowCorr gp σHl .B = CKAScheme.allowCorr gp σRl .B from rfl,
      hcB]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Send-A-rleak: the PCS gate fails at the challenge epoch
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run σRl)
      _
    have hvalidA : CKAScheme.validStep last .sendA = true := by
      rcases hlastD with rfl | rfl <;> rfl
    have hpcs : ¬ (max (tA + 1) tB + gp.ΔPCS ≤ gp.challengeEpoch) := by omega
    have hH : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run
        σHl = pure (none, σHl) := by
      change (CKAScheme.oracleSendA_rleak gp (scheme kem hDet leak) ()).run σHl = _
      simp [CKAScheme.oracleSendA_rleak, hvalidA, CKAScheme.allowCorrPCS, hσHl, hpcs]
    have hR : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run
        σRl = pure (none, σRl) := by
      change (CKAScheme.oracleSendA_rleak gp (scheme kem hDet leak) ()).run σRl = _
      simp [CKAScheme.oracleSendA_rleak, hvalidA, CKAScheme.allowCorrPCS, hσRl, hpcs]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Send-B-rleak: not a send slot
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run σRl)
      _
    have hvF : CKAScheme.validStep last .sendB = false := by
      rcases hlastD with rfl | rfl <;> rfl
    have hH : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run
        σHl = pure (none, σHl) := by
      change (CKAScheme.oracleSendB_rleak gp (scheme kem hDet leak) ()).run σHl = _
      simp [CKAScheme.oracleSendB_rleak, hσHl, hvF]
    have hR : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run
        σRl = pure (none, σRl) := by
      change (CKAScheme.oracleSendB_rleak gp (scheme kem hDet leak) ()).run σRl = _
      simp [CKAScheme.oracleSendB_rleak, hσRl, hvF]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩

/-- The injected prefix at bit `false` couples with the reduction prefix.

One induction over the adversary: the phase analysis of each oracle step is in
the three step lemmas; here the splitters are unfolded, the challenge guards
are evaluated, and the paused and finished runs are collected. -/
lemma injectedPrefix_couples_challengePrefix_A
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hparty : gp.challengedParty = CKAScheme.CKAParty.A)
    (hΔ : 2 ≤ gp.ΔPCS)
    (hodd : gp.challengeEpoch % 2 = 1)
    (hFS : gp.ΔFS = 0)
    (pkStar : PK) (skStar : SK)
    {α : Type}
    (adv : OracleComp (securitySpec leak) α)
    (σH σR : SecurityState K PK SK C) :
    coupleRelA kem hDet gp pkStar skStar σH σR →
    RelTriple
      ((injectedChallengePrefix kem hDet leak gp false pkStar skStar adv).run σH)
      ((challengePrefix kem hDet leak gp pkStar adv).run σR)
      (couplePostA leak gp pkStar skStar) := by
  induction adv using OracleComp.inductionOn generalizing σH σR with
  | pure a =>
      intro _
      simp only [injectedChallengePrefix, challengePrefix, construct_pure,
        StateT.run_pure]
      exact relTriple_pure_pure (Or.inl ⟨⟨a, rfl⟩, ⟨a, rfl⟩⟩)
  | query_bind t cont ih =>
      intro hrel
      have hcont : ∀ p q : (securitySpec leak).Range t × SecurityState K PK SK C,
          p.1 = q.1 ∧ coupleRelA kem hDet gp pkStar skStar p.2 q.2 →
          RelTriple
            ((injectedChallengePrefix kem hDet leak gp false pkStar skStar
              (cont p.1)).run p.2)
            ((challengePrefix kem hDet leak gp pkStar (cont q.1)).run q.2)
            (couplePostA leak gp pkStar skStar) := by
        rintro ⟨u, σH'⟩ ⟨v, σR'⟩ ⟨huv, hrel'⟩
        obtain rfl : u = v := huv
        exact ih u σH' σR' hrel'
      rcases hrel with ⟨rfl, hpre⟩ | hInj | hChall | hDead
      · -- Pre: the challenge guards are false; every arm steps the implementations
        have hWA : willChallengeA gp σH = false :=
          willChallengeA_eq_false_of_preInvA kem gp σH hpre
        have hWB : willChallengeB gp σH = false := by
          simp [willChallengeB, hparty]
        rcases t with
          (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
            uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
        all_goals
          try cases uSendA
          try cases uRecvA
          try cases uSendB
          try cases uRecvB
          try cases uChallA
          try cases uChallB
          try cases uCorrA
          try cases uCorrB
          try cases uRLeakA
          try cases uRLeakB
        all_goals
          simp only [injectedChallengePrefix, challengePrefix, construct_query_bind,
            stateT_run, hWA, hWB, Bool.false_eq_true,
            ↓reduceIte]
        all_goals
          exact relTriple_bind
            (coupleRelA_step_pre kem hDet hkem leak gp hparty hΔ hodd pkStar skStar _
              σH hpre) hcont
      · -- Inj: normalize the two states to literals, then step
        obtain ⟨skA, cInj, kInj, skR, hstA, hstB, hrhoB, hkeyB, hdec, hlast, htB, htA,
          hσH⟩ := hInj
        rcases σR with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
        obtain rfl : sA = State.recvReady skA := hstA
        obtain rfl : sB = State.recvReady skR := hstB
        obtain rfl : ρB = some (cInj, pkStar) := hrhoB
        obtain rfl : kB = some kInj := hkeyB
        obtain rfl : last = some CKAScheme.CKAAction.sendB := hlast
        subst hσH
        have htB' : tB + 1 = gp.challengeEpoch := htB
        have htA' : tA + 2 = gp.challengeEpoch := htA
        rw [show ({ (⟨State.recvReady skA, State.recvReady skR, ρA,
              some (cInj, pkStar), kA, some kInj, corr,
              some CKAScheme.CKAAction.sendB, tA, tB⟩ :
              SecurityState K PK SK C) with stB := State.recvReady skStar } :
            SecurityState K PK SK C) =
            ⟨State.recvReady skA, State.recvReady skStar, ρA, some (cInj, pkStar),
              kA, some kInj, corr, some CKAScheme.CKAAction.sendB, tA, tB⟩ from rfl]
        have hWA' : ∀ st : State PK SK, willChallengeA gp
            (⟨State.recvReady skA, st, ρA, some (cInj, pkStar), kA, some kInj, corr,
              some CKAScheme.CKAAction.sendB, tA, tB⟩ :
              SecurityState K PK SK C) = false := fun st => by
          simp [willChallengeA, CKAScheme.validStep]
        have hWB' : ∀ st : State PK SK, willChallengeB gp
            (⟨State.recvReady skA, st, ρA, some (cInj, pkStar), kA, some kInj, corr,
              some CKAScheme.CKAAction.sendB, tA, tB⟩ :
              SecurityState K PK SK C) = false := fun st => by
          simp [willChallengeB, hparty]
        rcases t with
          (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
            uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
        all_goals
          try cases uSendA
          try cases uRecvA
          try cases uSendB
          try cases uRecvB
          try cases uChallA
          try cases uChallB
          try cases uCorrA
          try cases uCorrB
          try cases uRLeakA
          try cases uRLeakB
        all_goals
          simp only [injectedChallengePrefix, challengePrefix, construct_query_bind,
            stateT_run, hWA', hWB', Bool.false_eq_true,
            ↓reduceIte]
        all_goals
          exact relTriple_bind
            (coupleRelA_step_inj kem hDet leak gp hparty hΔ hFS pkStar skStar skA cInj
              kInj skR ρA kA corr tA tB hdec htB' htA' _) hcont
      · -- Chall: the challenge query pauses; every other arm steps
        obtain ⟨hstA, hWill, hInv, hσH⟩ := hChall
        rcases σR with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
        obtain rfl : sA = State.sendReady pkStar := hstA
        subst hσH
        rw [show ({ (⟨State.sendReady pkStar, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩ :
              SecurityState K PK SK C) with stB := State.recvReady skStar } :
            SecurityState K PK SK C) =
            ⟨State.sendReady pkStar, State.recvReady skStar, ρA, ρB, kA, kB, corr,
              last, tA, tB⟩ from rfl]
        have hWill' : ∀ st : State PK SK, willChallengeA gp
            (⟨State.sendReady pkStar, st, ρA, ρB, kA, kB, corr, last, tA, tB⟩ :
              SecurityState K PK SK C) = true := fun st => hWill
        have hWB' : ∀ st : State PK SK, willChallengeB gp
            (⟨State.sendReady pkStar, st, ρA, ρB, kA, kB, corr, last, tA, tB⟩ :
              SecurityState K PK SK C) = false := fun st => by
          simp [willChallengeB, hparty]
        rcases t with
          (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
            uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
        all_goals
          try cases uSendA
          try cases uRecvA
          try cases uSendB
          try cases uRecvB
          try cases uChallA
          try cases uChallB
          try cases uCorrA
          try cases uCorrB
          try cases uRLeakA
          try cases uRLeakB
        all_goals
          simp only [injectedChallengePrefix, challengePrefix, construct_query_bind,
            stateT_run, hWill', hWB',
            Bool.false_eq_true, ↓reduceIte]
        all_goals
          first
            | exact relTriple_bind
                (coupleRelA_step_chall kem hDet leak gp hparty hΔ hFS pkStar skStar sB
                  ρA ρB kA kB corr last tA tB hWill hInv _) hcont
            | exact relTriple_pure_pure (Or.inr ⟨cont,
                ⟨State.sendReady pkStar, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩,
                rfl, rfl, hInv, hWill⟩)
      · -- Dead: the challenge is passed on both sides; neither prefix can pause
        refine relTriple_post_mono
          (relTriple_prod
            (P := fun z => ∃ a, z.1 = CKAChallengeStepResult.done a)
            (Q := fun z' => ∃ a', z'.1 = CKAChallengeStepResult.done a')
            (fun z hz =>
              injectedChallengePrefix_run_done_of_challengePassed kem hDet leak gp
                false pkStar skStar _ σH z hDead.1 hz)
            (fun z' hz' =>
              challengePrefix_run_done_of_challengePassed kem hDet leak gp pkStar
                _ σR z' hDead.2 hz')) ?_
        intro z z' hzz
        exact Or.inl hzz


end kemCKA
