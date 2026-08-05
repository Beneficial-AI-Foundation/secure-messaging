/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Construction
import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect.ErasureCode
import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect.Invariant
import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect.SendA
import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect.RecvB
import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect.SendB
import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect.RecvA
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Opp-UniKEM-CKA — Game Invariant and Perfect Correctness

We introduce a reachability invariant for the SCKA correctness game with respect to an
Opp-UniKEM SCKA scheme and prove that it is preserved by every oracle call.

From this invariant, we derive perfect correctness of Opp-UniKEM — `correctness_of_perfectKEM`:
for a perfectly correct KEM and correct erasure codes with positive reconstruction thresholds,
`Pr[G(Adv) = true] = 1` with `G(Adv) := SCKAScheme.correctnessExp Π Adv`.

This invariant also underlies the probabilistic bounds in `Correctness.Reduction`.

`supp X` denotes the set of positive-probability outputs of
`X : ProbComp α`.

## Transcripts

An `EpochTranscript` records the elements one epoch `t` has sampled:

```text
T t = (kpₜ, offₜ, onₜ) : Option (PK × SK) × Option (St × C₀) × Option (C₁ × K)
```

with membership proofs

```text
kpₜ  = some (pk, sk)  → (pk, sk)  ∈ supp kem.keygen
offₜ = some (st, ct₀) → (st, ct₀) ∈ supp onoff.encapsOff
kpₜ = some (pk, sk) ∧ offₜ = some (st, ct₀) ∧ onₜ = some (ct₁, k)
  → (ct₁, k) ∈ supp (onoff.encapsOn st pk)
onₜ ≠ none → kpₜ ≠ none ∧ offₜ ≠ none.
```

## Invariant

`WorldInv T s`, with `tA := s.stA.t` and `tB := s.stB.t`, asserts:

* flag and epochs — `s.correct = true`; `tB ≤ tA ≤ tB + 1`; `0 < tA, tB`;
  `s.tcurA ≤ tA - 1`; `s.tcurB ≤ tB - 1`;
* current samples — `kp_tA = pair? s.stA.ekA s.stA.dkA`,
  `off_tB = pair? s.stB.stCt s.stB.ct0`, `on_tB.map fst = s.stB.ct1`,
  where `pair?` pairs two options when both are present;
* decoded values are honest — `s.stB.ekA = some pk → ∃ sk, kp_tB = some (pk, sk)`;
  `s.stA.ct0 = some ct₀ → ∃ st, off_tA = some (st, ct₀)`;
* chunk buffers (`ChunksA`, `ChunksB`) — each buffer is an honest chunk set
  of the payload in transit: strictly below the reconstruction threshold
  while undecoded, exactly at it once decoded;
* history — `on_t ≠ none` for `0 < t < tA`; `kp_t = none` for `tA < t`;
  `off_t = on_t = none` for `tB < t`;
* key tables — with `key (T t) := on_t.map snd`:
  `s.keyA t = key (T t)` for `0 < t < tA` and `none` otherwise;
  `s.keyB t = key (T t)`;
* messages — every recorded message is generated from `T`
  (`HonestMessageA`, `HonestMessageB`), reports receiving epoch
  `sending epoch - 1`, and its sending epoch is at most the sender's.

## Preservation

With `Run o s := ((SCKAScheme.sckaCorrectnessImpl Π) o).run s` and
`I s := ∃ T, WorldInv T s` (`reachableInv`):

```text
I s₀                                                   (reachableInv_init)
I s ∧ (r, s') ∈ supp (Run o s) → I s'       (oracle*_preserves_reachableInv)
```

The receive oracles are quantified over every index of the message tables,
so preservation covers delivery in any order and any multiplicity.  The
only KEM-dependent step is `RecvA` completing an epoch, where the game
asserts that A's decapsulation returns B's recorded key
(`CurrentKEMCorrect`); by the invariant both values come from supported
samples, and perfect KEM correctness gives
`hDet.decapsDet sk (onoff.split⁻¹ (ct₀, ct₁)) = some k`
(`decapsDet_eq_some_of_mem_support`, `mem_support_encaps_of_onoff`).

## Erasure codes

For an honest chunk set of a payload `x` indexed by `J ⊆ Fin N`:

```text
|J| < nchunk → decode = none                    (decode_payloadChunks_none)
|J| = nchunk → decode = some x                       (decode_payloadChunks)
```

and inserting one honest chunk either stays strictly below the threshold or
reaches it exactly and decodes to `x` (`decode_insert_honest`).

By preservation every supported final state has `correct = true`, and
`G(Adv)` is total, so `Pr[G(Adv) = true] = 1`.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

universe u

variable {m : Type → Type u} {K PK SK C Sym : Type}

open SCKAScheme.sckaCorrectnessSpec

/-- `recvB` reports the epoch carried by the delivered message, independently
of B's current local epoch.  In particular, a delayed old message does not get
mislabelled with the current epoch. -/
theorem recvB_receivingEpoch
    [Monad m] (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    [DecidableEq Sym]
    (ecEk : ErasureCodePayload PK Sym) (stB : StB onoff Sym)
    (ch? : Option (ℕ × Sym)) (ack : Ack) (t : ℕ) (b? : Option Bit) :
    (recvB kem onoff ecEk stB (ch?, ack, t, b?)).map (fun out => out.2.1) =
      some (t - 1) := by
  simp [recvB]

/-- Every oracle in the SCKA correctness implementation preserves
`reachableInv`, by dispatching to the corresponding oracle-specific theorem. -/
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
  rcases hInv with ⟨_world, hWorld⟩
  exact hb'.trans hWorld.correct

end oppUniKemCKA
