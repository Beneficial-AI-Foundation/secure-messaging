/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import SecureMessaging.SCKA.OppBiKEM.Correctness.MainInvariant.SendTotal

/-!
# Opp-BiKEM-CKA — Correctness for a perfectly correct KEM

A perfectly correct KEM has `ε = 0`, so `correctness_true_ge` already gives success with
probability one (`correctness_of_perfectKEM'`), but only for an adversary with a bound on its
send queries. This file proves the facts from which `correctness_of_perfectKEM` in
`Correctness` derives the same conclusion for every adversary.

With a perfectly correct KEM no KEM instance can fail: decapsulation recovers the encapsulated
key for every key pair and encapsulation the KEM can output (`DecapsCorrectOnSupport`, obtained
from `decapsCorrectOnSupport_of_perfectlyCorrect`). The `DecapsReady` hypothesis of
`gameInv_step_of` therefore holds at every state (`transcriptDecaps_of_support`), every oracle
preserves `GameInv` (`gameInv_preserved`), and `GameInv` holds at every reachable state
(`simulateQ_gameInv`). The argument needs no failure flag and no potential, hence no query
bound. Since `GameInv s` contains `s.correct = true`, the game succeeds with probability one
(`correctness_of_perfectKEM` in `Correctness`); since `GameInv` also gives `send_ne_none`,
neither party's `send` is ever rejected (`sends_never_rejected_of_perfectKEM`).
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- For every key pair `(pk, sk)` in the support of key generation and every `(c, k)` in the
support of encapsulation to `pk`, deterministic decapsulation of `c` with `sk` returns `k`. -/
def DecapsCorrectOnSupport (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps) : Prop :=
  ∀ pk sk c k, (pk, sk) ∈ support kem.keygen → (c, k) ∈ support (kem.encaps pk) →
    hDet.decapsDet sk c = some k

/-- A perfectly correct KEM satisfies `DecapsCorrectOnSupport`. -/
lemma decapsCorrectOnSupport_of_perfectlyCorrect [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp) :
    DecapsCorrectOnSupport kem hDet := by
  intro pk sk c k hkp henc
  have hone : Pr[= true | kem.CorrectExp] = 1 := hkem
  rw [probOutput_eq_one_iff] at hone
  obtain ⟨-, hsupp⟩ := hone
  by_contra hne
  have hfalse : false ∈ support kem.CorrectExp := by
    unfold KEMScheme.CorrectExp
    rw [mem_support_bind_iff]
    refine ⟨(pk, sk), hkp, ?_⟩
    rw [mem_support_bind_iff]
    refine ⟨(c, k), henc, ?_⟩
    rw [mem_support_bind_iff]
    refine ⟨hDet.decapsDet sk c, ?_, ?_⟩
    · rw [hDet.decaps_eq]
      simp
    · simp [hne]
  rw [hsupp] at hfalse
  simp at hfalse

/-- If decapsulation never fails on honest outputs (i.e., `DecapsCorrectOnSupport` holds), then
in every epoch of every transcript the recorded secret key decapsulates the recorded ciphertext
to the recorded key. -/
lemma transcriptDecaps_of_support {kem : KEMScheme ProbComp K PK SK C}
    (hDet : kem.DeterministicDecaps) (hdec : DecapsCorrectOnSupport kem hDet)
    (T : Transcript kem) (e : ℤ) :
    ∀ pk sk c k, (T e).keypair = some (pk, sk) → (T e).enc = some (c, k) →
      hDet.decapsDet sk c = some k :=
  fun pk sk c k hkp henc =>
    hdec pk sk c k ((T e).keypair_mem pk sk hkp) ((T e).enc_mem pk sk c k hkp henc)

/-- If `DecapsCorrectOnSupport` holds and both erasure codes are correct, every
correctness-game oracle preserves `GameInv`. -/
lemma gameInv_preserved [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)
    (hdec : DecapsCorrectOnSupport kem hDet) :
    QueryImpl.PreservesInv (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak))
      (GameInv kem ecEk ecCt) := by
  intro t s hs z hz
  refine gameInv_step_of kem hDet ecEk ecCt hEk hCt leak t s hs ?_ z hz
  intro T _ _
  exact ⟨fun q _ _ => transcriptDecaps_of_support hDet hdec T q,
    fun q _ _ => transcriptDecaps_of_support hDet hdec T q⟩

/-- Let `adv` be a correctness adversary. Assume:

* `kem` has deterministic decapsulation, correct on every honestly generated key pair and
  encapsulation (`DecapsCorrectOnSupport`);
* `ecEk` and `ecCt` are correct erasure codes;
* `stA` and `stB` are possible initial states of A and B.

Then every final state of `adv`'s execution from `initGameState stA stB` satisfies
`GameInv`. -/
lemma simulateQ_gameInv [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)
    (hdec : DecapsCorrectOnSupport kem hDet)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (stA : StA PK SK C Sym) (stB : StB PK SK C Sym)
    (hA : stA ∈ support (initA () : ProbComp (StA PK SK C Sym)))
    (hB : stB ∈ support (initB () : ProbComp (StB PK SK C Sym)))
    (z : Bool × SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hz : z ∈ support ((simulateQ
      (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak)) adv).run
      (SCKAScheme.initGameState stA stB))) :
    GameInv kem ecEk ecCt z.2 :=
  simulateQ_run_preservesInv _ _ (gameInv_preserved kem hDet ecEk ecCt hEk hCt leak hdec) adv _
    (gameInv_init kem ecEk ecCt stA stB hA hB) z hz

/-- Assume:

* `kem` has deterministic decapsulation and is perfectly correct;
* `ecEk` and `ecCt` are correct erasure codes.

Then, for every adversary, neither party's `send` returns `none` at any reachable state of the
Opp-BiKEM-CKA correctness game. -/
theorem sends_never_rejected_of_perfectKEM [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (z : Bool × SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hz : z ∈ support ((simulateQ
      (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak)) adv).run
      (SCKAScheme.initGameState (initialState .A) (initialState .B)))) :
    none ∉ support (sendA kem ecEk ecCt z.2.stA) ∧
      none ∉ support (sendB kem ecEk ecCt z.2.stB) := by
  have hinv := simulateQ_gameInv kem hDet ecEk ecCt hEk hCt leak
    (decapsCorrectOnSupport_of_perfectlyCorrect kem hDet hkem) adv
    (initialState .A) (initialState .B) (by simp [initA, init, initialState])
    (by simp [initB, init, initialState]) z hz
  exact ⟨sendA_ne_none kem ecEk ecCt _ hinv, sendB_ne_none kem ecEk ecCt _ hinv⟩

end oppBiKemCKA
