module

public import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.OneStep
public import SecureMessaging.SCKA.OppUniKEM.Correctness.Invariant.SendA
public import SecureMessaging.SCKA.OppUniKEM.Correctness.Invariant.RecvB
public import SecureMessaging.SCKA.OppUniKEM.Correctness.Invariant.SendB
public import SecureMessaging.SCKA.OppUniKEM.Correctness.Invariant.RecvA
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Opp-UniKEM-CKA Tracked-State Projection

Projection means forgetting the failure flag `b` of a tracked state `(s, b)`.
The main results are:

* `correctnessExp_eq_final_map` — the correctness experiment is a
  final-state map over the simulated run;
* `trackedCorrectnessImpl_preserves` — every query preserves the tracked
  invariant;
* `tracked_initial_inv` — the initial tracked state satisfies the invariant;
* `correctness_failure_le_of_tracked_bad` — a bound on the final tracked
  failure flag bounds the failure probability of the ordinary correctness game.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}
variable [DecidableEq Sym]

open SCKAScheme.sckaCorrectnessSpec

namespace Reduction.Internal

/-- The ordinary correctness experiment is the final state's correctness bit
mapped over the simulated correctness-game run from its initial state. -/
lemma correctnessExp_eq_final_map [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym)) :
    SCKAScheme.correctnessExp
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv =
      (fun z => z.2.correct) <$>
        (simulateQ
          (SCKAScheme.sckaCorrectnessImpl
            (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) adv).run
          (initialGame kem onoff) := by
  simp [SCKAScheme.correctnessExp, scheme, initKeyGen, initA, initB,
    initialGame, initialA, initialB, map_eq_bind_pure_comp]

/-- Every tracked correctness query preserves the tracked invariant, using the
reachability theorem for the query's uniform, send, or receive transition. -/
lemma trackedCorrectnessImpl_preserves
    [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEkCorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Correct : ecCt0.ec.Correct)
    (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Correct : ecCt1.ec.Correct)
    (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (leak : KEMScheme.OnOffRandLeak kem onoff) :
    QueryImpl.PreservesInv
      (trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak)
      (trackedInv kem onoff hDet ecEk ecCt0 ecCt1) := by
  refine trackedImpl_preserves _ _ _ fun t s hreach hfailOld y hy => ?_
  have hcurrent : CurrentKEMCorrect kem onoff hDet s :=
    currentKEMFailure_eq_false_implies_current kem onoff hDet ecEk ecCt0 ecCt1
      s hreach hfailOld
  match t with
  | OUnif n =>
      exact SCKAScheme.oracleUnif_preservesInv _ n s hreach y hy
  | OSendA =>
      exact oracleSendA_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1
        leak hEkPos () s hreach y hy
  | OSendB =>
      exact oracleSendB_preserves_reachableInv kem onoff hDet ecEk ecCt0 hCt0Pos
        ecCt1 hCt1Pos leak () s hreach y hy
  | ORecvA n =>
      exact oracleRecvA_preserves_reachableInv kem onoff hDet ecEk ecCt0
        hCt0Correct ecCt1 hCt1Correct hCt1Pos leak n s hreach hcurrent y hy
  | ORecvB n =>
      exact oracleRecvB_preserves_reachableInv kem onoff hDet ecEk hEkCorrect hEkPos
        ecCt0 ecCt1 leak n s hreach y hy

omit [DecidableEq Sym] in
/-- The initial game state with an unset failure flag satisfies the
tracked invariant. -/
lemma tracked_initial_inv [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (hEkPos : 0 < ecEk.ec.nchunk) (hCt0Pos : 0 < ecCt0.ec.nchunk) :
    trackedInv kem onoff hDet ecEk ecCt0 ecCt1
      (initialGame (Sym := Sym) kem onoff, false) := by
  right
  refine ⟨?_, ?_⟩
  · simpa [initialGame, initialA, initialB] using
      reachableInv_init kem onoff ecEk ecCt0 ecCt1 hEkPos hCt0Pos
  · simp [currentKEMFailure, initialGame, initialA, initialB,
      SCKAScheme.initGameState]

/-- A bound on the probability that the final tracked failure bit is set
gives the same bound on the failure probability of the correctness game. -/
lemma correctness_failure_le_of_tracked_bad [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEkCorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Correct : ecCt0.ec.Correct)
    (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Correct : ecCt1.ec.Correct)
    (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym)) (δ : ℝ≥0∞)
    (hbad :
      Pr{let z ← ((simulateQ
          (trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) adv).run
          (initialGame (Sym := Sym) kem onoff, false))}[z.2.2 = true] ≤ δ) :
    Pr{let x ← (SCKAScheme.correctnessExp
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv)}[x = false] ≤ δ :=
  SCKAScheme.correctness_failure_le_of_tracked_bad _ _ (reachableInv kem onoff ecEk ecCt0 ecCt1)
    (fun _ ⟨_T, hConsistent⟩ => hConsistent.correct)
    (trackedCorrectnessImpl_preserves kem onoff hDet ecEk hEkCorrect hEkPos
      ecCt0 hCt0Correct hCt0Pos ecCt1 hCt1Correct hCt1Pos leak) adv _
    (tracked_initial_inv kem onoff hDet ecEk ecCt0 ecCt1 hEkPos hCt0Pos)
    (correctnessExp_eq_final_map kem onoff hDet ecEk ecCt0 ecCt1 leak adv) δ hbad

end Reduction.Internal

end oppUniKemCKA
