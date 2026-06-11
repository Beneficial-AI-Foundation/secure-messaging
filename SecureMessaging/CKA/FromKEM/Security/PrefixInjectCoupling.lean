/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Security.PrefixInjectCouplingA
import SecureMessaging.CKA.FromKEM.Security.PrefixInjectCouplingB

/-!
# CKA from KEM — Injected-Prefix Coupling

`ckaSecurityFixedBranchWithInjectedChallengeKey` and
`ckaReductionINDCPABranchRawKeygenSwapped` behave the same up to the first
challenge query whose `willChallengeA`/`willChallengeB` guard holds.
Splitting both games at that query, the runs that never reach such a query are
bit-independent and cancel inside each game's own gap, while the paused runs
land in the challenge-bridge shapes.  The party-specific couplings live in
`PrefixInjectCouplingA` and `PrefixInjectCouplingB`; this file assembles them
into the gap-level bound `cka_injected_honest_gap_le_keygen_swapped_raw_gap`,
the missing hop in the top-level advantage chain.
-/

open OracleSpec OracleComp ENNReal KEMScheme
open OracleComp.ProgramLogic.Relational

namespace kemCKA

variable {K PK SK C : Type}

/-! ## Splitting a success probability over the first pause

Both split games are a prefix bound to a resume.  Replacing the resume's
finished-run guesses by `false` isolates the paused runs' contribution; the
finished runs' contribution is bit-free because the prefix runs at bit
`false`.  The success probability of the game is the sum of the two. -/

private lemma probOutput_true_bind_add_of_pointwise {α : Type} (mx : ProbComp α)
    (f g h : α → ProbComp Bool)
    (hpt : ∀ z, Pr[= true | f z] = Pr[= true | g z] + Pr[= true | h z]) :
    Pr[= true | mx >>= f] = Pr[= true | mx >>= g] + Pr[= true | mx >>= h] := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum,
    ← ENNReal.tsum_add]
  exact tsum_congr fun z => by rw [hpt z, mul_add]

/-- As resuming with `injectedChallengeResume`, with finished runs' guesses
replaced by `false`: the paused runs' contribution to the success
probability. -/
private def injResumeKilled [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (b : Bool)
    (pkStar : PK) (skStar : SK)
    (z : CKAChallengeStepResult leak Bool × SecurityState K PK SK C) :
    ProbComp Bool :=
  match z.1 with
  | .done _ => pure false
  | _ => Prod.fst <$>
      injectedChallengeResume kem hDet leak gp b pkStar skStar z.1 z.2

/-- The finished runs' guesses; paused runs contribute `false`. -/
private def injDone
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : RandLeak kem)
    (z : CKAChallengeStepResult leak Bool × SecurityState K PK SK C) :
    ProbComp Bool :=
  match z.1 with
  | .done g => pure g
  | _ => pure false

/-- The reduction game's continuation after its prefix: the challenge
ciphertext draw, the random key draw, and `finishChallengeStepRaw` at the
selected key. -/
private def rawResume [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (b : Bool)
    (pkStar : PK)
    (z : CKAChallengeStepResult leak Bool × SecurityState K PK SK C) :
    ProbComp Bool := do
  let ck ← kem.encaps pkStar
  let kRand ← ($ᵗ K : ProbComp K)
  finishChallengeStepRaw kem hDet leak gp z.1 z.2 ck.1 (if b then ck.2 else kRand)

/-- As `rawResume`, with finished runs' guesses replaced by `false`. -/
private def rawResumeKilled [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (b : Bool)
    (pkStar : PK)
    (z : CKAChallengeStepResult leak Bool × SecurityState K PK SK C) :
    ProbComp Bool :=
  match z.1 with
  | .done _ => pure false
  | _ => rawResume kem hDet leak gp b pkStar z

/-- Pointwise split of the injected game's resume into its paused and
finished contributions. -/
private lemma injResume_probOutput_decomp [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (b : Bool)
    (pkStar : PK) (skStar : SK)
    (z : CKAChallengeStepResult leak Bool × SecurityState K PK SK C) :
    Pr[= true |
        Prod.fst <$> injectedChallengeResume kem hDet leak gp b pkStar skStar
          z.1 z.2] =
      Pr[= true | injResumeKilled kem hDet leak gp b pkStar skStar z] +
        Pr[= true | injDone leak z] := by
  rcases z with ⟨res, σ⟩
  cases res with
  | done g => simp [injectedChallengeResume, injResumeKilled, injDone]
  | pausedA cont => simp [injResumeKilled, injDone]
  | pausedB cont => simp [injResumeKilled, injDone]

/-- Pointwise split of the reduction game's resume into its paused and
finished contributions.  In the finished case the unused challenge and key
draws integrate out. -/
private lemma rawResume_probOutput_decomp [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (b : Bool)
    (pkStar : PK)
    (z : CKAChallengeStepResult leak Bool × SecurityState K PK SK C) :
    Pr[= true | rawResume kem hDet leak gp b pkStar z] =
      Pr[= true | rawResumeKilled kem hDet leak gp b pkStar z] +
        Pr[= true | injDone leak z] := by
  rcases z with ⟨res, σ⟩
  cases res with
  | done g =>
      simp only [rawResume, finishChallengeStepRaw, rawResumeKilled, injDone]
      rw [probOutput_bind_const]
      simp only [HasEvalPMF.probFailure_eq_zero, tsub_zero, one_mul]
      rw [probOutput_bind_const]
      simp [HasEvalPMF.probFailure_eq_zero]
  | pausedA cont => simp [rawResumeKilled, injDone]
  | pausedB cont => simp [rawResumeKilled, injDone]

/-! ## The four sub-games

Each split game decomposes into a paused part (the resume with finished
guesses replaced by `false`) and a finished part.  The finished parts read
nothing bit-dependent: the prefixes run at bit `false` and `injDone` ignores
the challenge bit, so the two finished sub-games are bit-free terms. -/

private def injectedKilledGame [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (b : Bool) : ProbComp Bool := do
  let (pk0, sk0) ← kem.keygen
  let (pkStar, skStar) ← kem.keygen
  let σ0 :=
    CKAScheme.initGameState
      (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
        State.sendReady pkStar
      else
        State.sendReady pk0)
      (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
        State.recvReady skStar
      else
        State.recvReady sk0)
  let z ← (injectedChallengePrefix kem hDet leak gp false pkStar skStar adv).run σ0
  injResumeKilled kem hDet leak gp b pkStar skStar z

private def injectedDoneGame [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams) : ProbComp Bool := do
  let (pk0, sk0) ← kem.keygen
  let (pkStar, skStar) ← kem.keygen
  let σ0 :=
    CKAScheme.initGameState
      (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
        State.sendReady pkStar
      else
        State.sendReady pk0)
      (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
        State.recvReady skStar
      else
        State.recvReady sk0)
  let z ← (injectedChallengePrefix kem hDet leak gp false pkStar skStar adv).run σ0
  injDone leak z

private def reductionKilledGame [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (b : Bool) : ProbComp Bool := do
  let (pk0, sk0) ← kem.keygen
  let (pkStar, _skStar) ← kem.keygen
  let σ0 :=
    CKAScheme.initGameState
      (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
        State.sendReady pkStar
      else
        State.sendReady pk0)
      (State.recvReady sk0)
  let z ← (challengePrefix kem hDet leak gp pkStar adv).run σ0
  rawResumeKilled kem hDet leak gp b pkStar z

private def reductionDoneGame [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams) : ProbComp Bool := do
  let (pk0, sk0) ← kem.keygen
  let (pkStar, _skStar) ← kem.keygen
  let σ0 :=
    CKAScheme.initGameState
      (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
        State.sendReady pkStar
      else
        State.sendReady pk0)
      (State.recvReady sk0)
  let z ← (challengePrefix kem hDet leak gp pkStar adv).run σ0
  injDone leak z

/-- The injected game's success probability splits over the first pause. -/
private lemma injected_probOutput_eq_killed_add_done
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (b : Bool) :
    Pr[= true | ckaSecurityFixedBranchWithInjectedChallengeKey kem hDet leak adv gp b] =
      Pr[= true | injectedKilledGame kem hDet leak adv gp b] +
        Pr[= true | injectedDoneGame kem hDet leak adv gp] := by
  rw [ckaSecurityFixedBranchWithInjectedChallengeKey_eq_split]
  simp only [injectedKilledGame, injectedDoneGame]
  refine probOutput_true_bind_add_of_pointwise kem.keygen _ _ _ fun ks0 => ?_
  obtain ⟨pk0, sk0⟩ := ks0
  refine probOutput_true_bind_add_of_pointwise kem.keygen _ _ _ fun ksS => ?_
  obtain ⟨pkStar, skStar⟩ := ksS
  refine probOutput_true_bind_add_of_pointwise _ _ _ _ fun z => ?_
  exact injResume_probOutput_decomp kem hDet leak gp b pkStar skStar z

/-- The reduction game's success probability splits over the first pause. -/
private lemma reduction_probOutput_eq_killed_add_done
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (b : Bool) :
    Pr[= true | ckaReductionINDCPABranchRawKeygenSwapped kem hDet leak adv gp b] =
      Pr[= true | reductionKilledGame kem hDet leak adv gp b] +
        Pr[= true | reductionDoneGame kem hDet leak adv gp] := by
  simp only [ckaReductionINDCPABranchRawKeygenSwapped, reductionKilledGame,
    reductionDoneGame]
  refine probOutput_true_bind_add_of_pointwise kem.keygen _ _ _ fun ks0 => ?_
  obtain ⟨pk0, sk0⟩ := ks0
  refine probOutput_true_bind_add_of_pointwise kem.keygen _ _ _ fun ksS => ?_
  obtain ⟨pkStar, skStar⟩ := ksS
  refine probOutput_true_bind_add_of_pointwise _ _ _ _ fun z => ?_
  exact rawResume_probOutput_decomp kem hDet leak gp b pkStar z

/-! ## Toward the paused-run chains

For Boolean computations without failure, equal success probabilities give the
equality-relation triple, which is the form the killed-game chain composes.
The two support lemmas pin the counters after a fired challenge query: the
challenged party's counter is bumped once, the other counter is unchanged.
The apexes' `injectionPassed`/`challengePassed` hypotheses follow from them at
the paused states. -/

private lemma relTriple_eqRel_of_probOutput_true_eq
    {mx my : ProbComp Bool}
    (h : Pr[= true | mx] = Pr[= true | my]) :
    RelTriple mx my (EqRel Bool) := by
  refine relTriple_eqRel_of_probOutput_eq fun x => ?_
  cases x
  · simp only [probOutput_false_eq_sub, HasEvalPMF.probFailure_eq_zero, h]
  · exact h

private lemma challA_run_support_counters [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (b : Bool)
    (σ : SecurityState K PK SK C) (pk : PK)
    (hstA : σ.stA = State.sendReady pk)
    (hWill : willChallengeA gp σ = true)
    (z : Option (Message C PK × K) × SecurityState K PK SK C)
    (hz : z ∈ support ((securityImpl kem hDet leak gp b
      (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σ)) :
    z.2.tA = σ.tA + 1 ∧ z.2.tB = σ.tB := by
  have hWill' := hWill
  simp only [willChallengeA, Bool.and_eq_true, beq_iff_eq] at hWill'
  obtain ⟨⟨hvalid, hpartyEq⟩, htA⟩ := hWill'
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
  obtain rfl : sA = State.sendReady pk := hstA
  have hrun : (securityImpl kem hDet leak gp b
      (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
      ⟨State.sendReady pk, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩ =
      (do
        let ck ← kem.encaps pk
        let ks ← kem.keygen
        let outKey ← if b then ($ᵗ K : ProbComp K) else pure ck.2
        pure (some ((ck.1, ks.1), outKey),
          (⟨State.recvReady ks.2, sB, some (ck.1, ks.1), ρB, some ck.2, kB, corr,
            some CKAScheme.CKAAction.challA, tA + 1, tB⟩ :
            SecurityState K PK SK C))) := by
    change (CKAScheme.oracleChallA gp b (scheme kem hDet leak) ()).run _ = _
    cases b <;>
      simp [CKAScheme.oracleChallA, hvalid, CKAScheme.isChallengeEpoch,
        CKAScheme.GameState.tP, hpartyEq, htA, scheme, send]
    all_goals rfl
  rw [hrun] at hz
  cases b
  all_goals (
    simp only [↓reduceIte] at hz
    vcv_support hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact ⟨rfl, rfl⟩)

private lemma challB_run_support_counters [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (b : Bool)
    (σ : SecurityState K PK SK C) (pk : PK)
    (hstB : σ.stB = State.sendReady pk)
    (hWill : willChallengeB gp σ = true)
    (z : Option (Message C PK × K) × SecurityState K PK SK C)
    (hz : z ∈ support ((securityImpl kem hDet leak gp b
      (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σ)) :
    z.2.tB = σ.tB + 1 ∧ z.2.tA = σ.tA := by
  have hWill' := hWill
  simp only [willChallengeB, Bool.and_eq_true, beq_iff_eq] at hWill'
  obtain ⟨⟨hvalid, hpartyEq⟩, htB⟩ := hWill'
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
  obtain rfl : sB = State.sendReady pk := hstB
  have hrun : (securityImpl kem hDet leak gp b
      (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
      ⟨sA, State.sendReady pk, ρA, ρB, kA, kB, corr, last, tA, tB⟩ =
      (do
        let ck ← kem.encaps pk
        let ks ← kem.keygen
        let outKey ← if b then ($ᵗ K : ProbComp K) else pure ck.2
        pure (some ((ck.1, ks.1), outKey),
          (⟨sA, State.recvReady ks.2, ρA, some (ck.1, ks.1), kA, some ck.2, corr,
            some CKAScheme.CKAAction.challB, tA, tB + 1⟩ :
            SecurityState K PK SK C))) := by
    change (CKAScheme.oracleChallB gp b (scheme kem hDet leak) ()).run _ = _
    cases b <;>
      simp [CKAScheme.oracleChallB, hvalid, CKAScheme.isChallengeEpoch,
        CKAScheme.GameState.tP, hpartyEq, htB, scheme, send]
    all_goals rfl
  rw [hrun] at hz
  cases b
  all_goals (
    simp only [↓reduceIte] at hz
    vcv_support hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact ⟨rfl, rfl⟩)

end kemCKA
