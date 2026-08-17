/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Construction
import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect.Invariant
import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect.SendA
import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect.RecvB
import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect.SendB
import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect.RecvA
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Opp-UniKEM-CKA — Game Invariant and Perfect Correctness

We prove perfect correctness of Opp-UniKEM — `correctness_of_perfectKEM`:
for a perfectly correct KEM and correct erasure codes with positive reconstruction thresholds,
`Pr[G(Adv) = true] = 1`, where `G(Adv) := SCKAScheme.correctnessExp Π Adv`
and `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak`.

## Proof outline

1. We define transcripts `T : Transcript` mapping each epoch of a game run
   to the samples it has drawn (`EpochTranscript`).
2. We define the predicate `TranscriptConsistent T s`: the game state `s`
   is consistent with `T` and `s.correct = true`.
3. We show that `reachableInv s := ∃ T, TranscriptConsistent T s` holds
   initially and is preserved by every oracle call; the receive oracles are
   analysed for every recorded message, in any order and any multiplicity.
4. We prove that A's decapsulated key always equals B's recorded key: by
   consistency with `T` both come from an honest key pair and
   encapsulation, so perfect KEM correctness applies.
5. We conclude `Pr[G(Adv) = true] = 1`.

The invariant also underlies the probabilistic bounds in
`Correctness.Reduction`.

## Modules

The shared module `SecureMessaging.ErasureCode.Payload` provides the
natural-indexed honest chunk representation and threshold decoding lemmas used
throughout the proof.

The Opp-UniKEM proof is split across:

* `Perfect.Invariant` — `EpochTranscript`, `Transcript`,
  `TranscriptConsistent`, `reachableInv` (steps 1–2); initialization, the
  uniform oracle, and `CurrentKEMCorrect` (step 4);
* `Perfect.SendA`, `Perfect.SendB`, `Perfect.RecvA`, `Perfect.RecvB` —
  preservation of `reachableInv` by each protocol oracle.

## Composition

This file derives `correctness_of_perfectKEM` from the submodule results.
Let `s₀` be the initial game state.  For an oracle `o` and a game state
`s`,

`Run o s := ((SCKAScheme.sckaCorrectnessImpl Π) o).run s`

is the probabilistic computation answering the call; its outputs are pairs
`(r, s')` of a reply and a next state.  `supp X` denotes the set of
positive-probability outputs of `X`.  The submodules provide

```text
reachableInv s₀                                        (reachableInv_init)
reachableInv s ∧ (r, s') ∈ supp (Run o s) → reachableInv s'
                                        (oracle*_preserves_reachableInv)
```

In this file,
- `correctnessImpl_preserves` combines the five per-oracle lemmas, and
- the VCVio lemma `OracleComp.simulateQ_run_preservesInv` extends them along
  the adversary's entire run.

Therefore every final state of positive probability has `correct = true`.
Since the game never fails (`probFailure_eq_zero`), the
main theorem `correctness_of_perfectKEM` follows: `Pr[G(Adv) = true] = 1`.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}

open SCKAScheme.sckaCorrectnessSpec

/-- Assume:
- the KEM is perfectly correct (`hkem`) and its decapsulation is
  deterministic (`hDet`),
- the erasure codes for the three chunked payloads — A's public key and
  B's two ciphertext parts — are correct (`hEkCorrect`, `hCt0Correct`,
  `hCt1Correct`), and
- their reconstruction thresholds are positive (`hEkPos`, `hCt0Pos`,
  `hCt1Pos`).

Then every oracle in the SCKA correctness implementation preserves
`reachableInv`. -/
private lemma correctnessImpl_preserves
  [DecidableEq Sym] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEkCorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Correct : ecCt0.ec.Correct)
    (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Correct : ecCt1.ec.Correct)
    (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak))
      (reachableInv kem onoff ecEk ecCt0 ecCt1) := by
  intro t s hs z hz
  match t with
  | OUnif n =>
      simpa [SCKAScheme.sckaCorrectnessImpl] using
        oracleUnif_preserves_reachableInv kem onoff ecEk ecCt0 ecCt1 n s hs z hz
  | OSendA =>
      simpa [SCKAScheme.sckaCorrectnessImpl] using
        oracleSendA_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1
          leak hEkPos () s hs z hz
  | OSendB =>
      simpa [SCKAScheme.sckaCorrectnessImpl] using
        oracleSendB_preserves_reachableInv kem onoff hDet ecEk ecCt0 hCt0Pos
          ecCt1 hCt1Pos leak () s hs z hz
  | ORecvA n =>
      simpa [SCKAScheme.sckaCorrectnessImpl] using
        oracleRecvA_preserves_reachableInv kem onoff hDet hkem ecEk ecCt0
          hCt0Correct ecCt1 hCt1Correct hCt1Pos leak n s hs z hz
  | ORecvB n =>
      simpa [SCKAScheme.sckaCorrectnessImpl] using
        oracleRecvB_preserves_reachableInv kem onoff hDet ecEk hEkCorrect hEkPos
          ecCt0 ecCt1 leak n s hs z hz

/-- Perfect correctness of Opp-UniKEM-CKA in the full SCKA correctness game.

The adversary may delay, reorder, duplicate, and replay honest protocol
messages.  Perfect KEM correctness, deterministic decapsulation, and the
three erasure-code correctness assumptions suffice to make every game
assertion hold on every supported execution. -/
theorem correctness_of_perfectKEM [DecidableEq Sym] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (hEkCorrect : ecEk.ec.Correct) (hCt0Correct : ecCt0.ec.Correct)
    (hCt1Correct : ecCt1.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk) (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym)) :
    Pr[= true |
      SCKAScheme.correctnessExp
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] = 1
    := by
  rw [← probEvent_eq_eq_probOutput, probEvent_eq_one_iff]
  refine ⟨probFailure_eq_zero, ?_⟩
  intro b hb
  unfold SCKAScheme.correctnessExp at hb
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨⟨⟩, _hik, hb⟩
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨stA, hstA, hb⟩
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨stB, hstB, hb⟩
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨out, hout, hb⟩
  have hstA' : stA =
      ({ dkA := none
         ekA := none
         ct0 := none
         t := 1
         ich := 0
         lch := ∅
         ack := { ekRec := false, ctRec := false } } : StA onoff Sym) := by
    simpa [scheme, initA, mem_support_pure_iff] using hstA
  subst stA
  have hstB' : stB =
      ({ ekA := none
         ct0 := none
         ct1 := none
         stCt := none
         t := 1
         ich := 0
         lch := ∅
         ack := { ekRec := false, ctRec := false } } : StB onoff Sym) := by
    simpa [scheme, initB, mem_support_pure_iff] using hstB
  subst stB
  have hInv : reachableInv kem onoff ecEk ecCt0 ecCt1 out.2 := by
    exact OracleComp.simulateQ_run_preservesInv
      (impl := SCKAScheme.sckaCorrectnessImpl
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak))
      (Inv := reachableInv kem onoff ecEk ecCt0 ecCt1)
      (correctnessImpl_preserves kem onoff hDet ecEk hEkCorrect hEkPos
        ecCt0 hCt0Correct hCt0Pos ecCt1 hCt1Correct hCt1Pos leak hkem)
      adv
      (SCKAScheme.initGameState
        ({ dkA := none
           ekA := none
           ct0 := none
           t := 1
           ich := 0
           lch := ∅
           ack := { ekRec := false, ctRec := false } } : StA onoff Sym)
        ({ ekA := none
           ct0 := none
           ct1 := none
           stCt := none
           t := 1
           ich := 0
           lch := ∅
           ack := { ekRec := false, ctRec := false } } : StB onoff Sym))
      (reachableInv_init kem onoff ecEk ecCt0 ecCt1 hEkPos hCt0Pos)
      out hout
  have hb' : b = out.2.correct := by simpa [mem_support_pure_iff] using hb
  rcases hInv with ⟨_T, hConsistent⟩
  exact hb'.trans hConsistent.correct

end oppUniKemCKA
