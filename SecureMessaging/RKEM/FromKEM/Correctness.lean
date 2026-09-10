/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SecureMessaging.RKEM.FromKEM.Construction

/-!
# RKEM from KEM — Correctness

This file proves `RKEMScheme.deltaCorrect` for the generic RKEM-from-KEM construction of
`SecureMessaging.RKEM.FromKEM.Construction`, under the hypothesis that the underlying KEM is
perfectly correct: the construction is then exactly `(0, 0)`-correct in the sense of
[TripleRatchet, Def. 5.3], matching [TripleRatchet, Appendix A.1, Theorem A.1].
-/

open OracleSpec OracleComp ENNReal KEMScheme RKEMScheme

namespace kemRKEM

variable {K PK SK C : Type}

/-- From KEM correctness at the monadic probability level, every reachable decapsulation of an
honest ciphertext returns the encapsulated key. -/
private lemma decaps_eq_some_of_mem_support [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    {pk : PK} {sk : SK} (hks : (pk, sk) ∈ support kem.keygen)
    {c : C} {k : K} (hck : (c, k) ∈ support (kem.encaps pk))
    {kOpt : Option K} (hkOpt : kOpt ∈ support (kem.decaps sk c)) :
    kOpt = some k := by
  have hmem : decide (kOpt = some k) ∈ support kem.CorrectExp := by
    simp only [KEMScheme.CorrectExp, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff, decide_eq_decide, exists_prop, Prod.exists]
    exact ⟨pk, sk, hks, c, k, hck, kOpt, hkOpt, Iff.rfl⟩
  simpa [((probOutput_eq_one_iff (mx := kem.CorrectExp) (x := true)).mp hkem).2] using hmem

/-- The parties agree on the shared key with probability 1. -/
theorem probOutput_correctExpA_eq_one [DecidableEq K] (kem : KEMScheme ProbComp K PK SK C)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp) :
    Pr[= true | RKEMScheme.correctExpA (scheme kem)] = 1 := by
  rw [← probEvent_eq_eq_probOutput, probEvent_eq_one_iff]
  refine ⟨probFailure_eq_zero, ?_⟩
  intro b hb
  unfold RKEMScheme.correctExpA at hb
  simp only [scheme, rkeygen, renc, rdec, pure_bind, mem_support_bind_iff,
    mem_support_pure_iff] at hb
  obtain ⟨⟨ekA, dkA⟩, -, ⟨ekB, dkB⟩, hksB, rencRes,
    ⟨⟨ct, key⟩, hck, ⟨ekAHat, dkAHat⟩, -, hrenc⟩, res, ⟨r, hr, hres⟩, hb⟩ := hb
  subst hrenc
  obtain rfl := decaps_eq_some_of_mem_support kem hkem hksB hck hr
  simp only [mem_support_pure_iff] at hres
  subst hres
  simpa using hb

/-- `probOutput_bind_of_const` specialized to `ProbComp`, where the outer computation never
fails, so the missing-mass factor `1 - Pr[⊥ | mx]` is always exactly `1`. -/
private lemma probOutput_bind_of_const' {α β : Type} (mx : ProbComp α) {my : α → ProbComp β}
    {y : β} {r : ℝ≥0∞} (h : ∀ x ∈ support mx, Pr[= y | my x] = r) :
    Pr[= y | mx >>= my] = r := by
  rw [probOutput_bind_of_const mx h, probFailure_eq_zero]
  simp

/-- The distribution of `ratchetRoundOutputA` is the same as sampling a fresh pair of keys. -/
theorem evalDist_ratchetRoundOutputA_eq [DecidableEq K] (kem : KEMScheme ProbComp K PK SK C)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp) :
    (𝒟[RKEMScheme.ratchetRoundOutputA (scheme kem)] : SPMF (Option (PK × SK))) =
      𝒟[(do let keys ← kem.keygen; return (some keys) : ProbComp (Option (PK × SK)))] := by
  unfold RKEMScheme.ratchetRoundOutputA
  simp only [scheme, rkeygen, renc, rdec, pure_bind, bind_assoc]
  refine evalDist_ext fun y => ?_
  refine probOutput_bind_of_const' kem.keygen fun _ _ => ?_
  refine probOutput_bind_of_const' kem.keygen fun p hks => ?_
  obtain ⟨ekB, dkB⟩ := p
  refine probOutput_bind_of_const' (kem.encaps ekB) fun q hck => ?_
  obtain ⟨ct, key⟩ := q
  refine probOutput_bind_congr fun s _ => ?_
  obtain ⟨ekAHat, dkAHat⟩ := s
  refine probOutput_bind_of_const' (kem.decaps dkB ct) fun r hr => ?_
  obtain rfl := decaps_eq_some_of_mem_support kem hkem hks hck hr
  rfl

/-- If the underlying KEM is correct, then the constructed RKEM also is correct. -/
-- ANCHOR: deltaCorrect
theorem deltaCorrect [DecidableEq K] (kem : KEMScheme ProbComp K PK SK C)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp) :
    RKEMScheme.deltaCorrect (scheme kem) ProbCompRuntime.probComp 0 0 := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · unfold RKEMScheme.correctnessErrorA
    change 1 - Pr[= true | RKEMScheme.correctExpA (scheme kem)] ≤ 0
    rw [probOutput_correctExpA_eq_one kem hkem]
    simp
  · unfold RKEMScheme.correctnessErrorB
    change 1 - Pr[= true | RKEMScheme.correctExpB (scheme kem)] ≤ 0
    rw [show (scheme kem).correctExpB = (scheme kem).correctExpA by rfl,
        probOutput_correctExpA_eq_one kem hkem]
    simp
  · unfold RKEMScheme.updateKeyDistErrorA
    change ‖SPMF.tvDist (𝒟[RKEMScheme.ratchetRoundOutputA (scheme kem)])
      (𝒟[(do let keys ← kem.keygen; pure (some keys) : ProbComp (Option (PK × SK)))])‖ₑ ≤ 0
    rw [evalDist_ratchetRoundOutputA_eq kem hkem]
    simp
  · unfold RKEMScheme.updateKeyDistErrorB
    change ‖SPMF.tvDist (𝒟[RKEMScheme.ratchetRoundOutputB (scheme kem)])
      (𝒟[(do let keys ← kem.keygen; pure (some keys) : ProbComp (Option (PK × SK)))])‖ₑ ≤ 0
    rw [show (scheme kem).ratchetRoundOutputB = (scheme kem).ratchetRoundOutputA by rfl,
        evalDist_ratchetRoundOutputA_eq kem hkem]
    simp
-- ANCHOR_END: deltaCorrect

end kemRKEM
