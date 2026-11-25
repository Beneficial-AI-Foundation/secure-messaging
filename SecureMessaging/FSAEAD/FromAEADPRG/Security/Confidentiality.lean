/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.FromAEADPRG.Security.Confidentiality.AeadRed
public import SecureMessaging.FSAEAD.FromAEADPRG.Security.Confidentiality.End
public import ToVCVio.EvalDist.HybridTelescope

/-!
# FS-AEAD from AEAD and PRG — confidentiality

Step 4 of the proof of Theorem 5 of [ACD19]: the confidentiality term `|Pr_{G_rej}[b = b'] - 1/2|`.

Write `m` for the smallest position that a corruption reveals, capped at `L` (`expoIdx`), and
`G_v` for the hybrid with uniform chain steps `1, …, v` and uniform challenge ciphertexts at the
positions `1, …, v`. The gap `confGap(Γ, E) = Pr_Γ[b = b' ∧ E] - Pr_Γ[E] / 2` splits along `m`
(`ToVCVio.prEvent_hybrid_telescope`, once for `b = b'` and once for the sure event):
```text
Pr_{G_0}[b = b'] - 1/2 = Σ_{v ≤ L} confGap(G_v, m = v)
                       + Σ_{j < L} (confGap(G_j, m ≥ j + 1) - confGap(G_{j+1}, m ≥ j + 1))
```
- `confGap(G_v, m = v) = 0` for `v < L` (`confGap_confHyb_expo_eq_zero`), and the term for `v = L`
  is at most half the probability of a challenge above `L` (`abs_confGap_confHyb_expo_le`).
- The step from `G_j` to `G_{j+1}` goes through `G_{j+1,j}` (PRG, `confGap_le_prgAdvantage`) and
  `G'_{j+1}` (an independent key for the challenge at `j + 1`, `prEvent_confHybKey_eq`), then to
  `G_{j+1}` (AEAD, `confGap_confHybKey_sub_eq`).

So (`abs_prEvent_securityExpRej_sub_le`)
```text
|Pr_{G_rej}[b = b'] - 1/2| ≤ Σ_{j=1..L} (Adv^prg(P'_j) + Adv^aead-dist(E'_j)) + Pr_{G_L}[C_{>L}] / 2
```
where `C_{>L}` is a challenge at a position above `L`. `Adv^aead-dist` is the advantage in the
one-time IND-CCA game of `SecureMessaging.AEAD.Defs` with `lenM = len`. The reductions `E'_j`
never call the decryption oracle.

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the
  Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf
  — Theorem 5.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal AEADScheme

namespace FSAEADScheme

namespace FromAEADPRG

variable {W Kae Cae AD M : Type} [DecidableEq AD] [DecidableEq Cae] [LenSampleable Cae]

/-- A run reveals no position below `j + 1 ≤ L` exactly when `m ≥ j + 1`. -/
theorem le_expoIdx_iff {L j : ℕ} (hj : j < L) (h : ConfHist) :
    j + 1 ≤ expoIdx L h ↔ ¬LowExpo (j + 1) h := by
  unfold expoIdx LowExpo
  rcases he : h.expo with _ | r
  · simp only [Option.getD_none, min_self, reduceCtorEq, false_and, exists_false,
      not_false_eq_true, iff_true]
    omega
  · simp only [Option.getD_some, Option.some.injEq, exists_eq_left', not_lt, le_min_iff]
    omega

/-- `G_0` with uniform ciphertexts at no position is `G_conf^0` for the construction: no challenge
is at position `0`. -/
theorem confImplWith_randUpTo_zero (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (len : M → ℕ) (clen : ℕ → ℕ) (b : Bool) :
    confImplWith ae G len clen (randUpTo 0) (fun _ => false) 0 b =
      confImplWith ae G len clen (fun _ => .real) (fun _ => false) 0 b := by
  have h : oracleChallMode ae G len clen (randUpTo 0) b =
      oracleChallMode ae G len clen (fun _ => .real) b := by
    funext q
    refine StateT.ext fun st => oracleChallMode_run_congr ae len clen G _ _ b q st ?_
    simp only [randUpTo, Nat.add_eq_zero_iff, one_ne_zero, and_false, nonpos_iff_eq_zero,
      ↓reduceIte]
  simp only [confImplWith, h]

/-- `G_rej` for the construction returns `b = b'` with the probability of `b = b'` in `G_0`. -/
theorem prEvent_securityExpRej_eq_confHyb [SampleableType W] [SampleableType Kae]
    {ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae} (hae : ae.Correct)
    (prg : PRGScheme W (W × Kae)) (len : M → ℕ) (clen : ℕ → ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :
    Pr{let x ← securityExpRej (fromAEADPRG ae prg) len Prod.fst adversary}[x = true] =
      Pr{let r ← confHyb ae prg len clen adversary 0 0 0}[r.1 = r.2.1] := by
  rw [prEvent_securityExpRej_eq_confRun hae prg len clen adversary]
  simp only [confHyb, sampleTab, pure_bind, confRun, confImpl, confImplWith_randUpTo_zero]
  rfl

/-- **One step of the confidentiality telescope.** The gap between `G_n` and `G_{n+1}` on runs with
`m ≥ n + 1` is at most `Adv^prg(P'_{n+1}) + Adv^aead-dist(E'_{n+1})`. -/
theorem abs_confGap_step_le [SampleableType W] [SampleableType Kae]
    {ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae} (hkg : ae.keygen =ᵈ ($ᵗ Kae : ProbComp Kae))
    (prg : PRGScheme W (W × Kae)) (len : M → ℕ) (clen : ℕ → ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (n : ℕ) :
    |confGap (confHyb ae prg len clen adversary 0 n n) (fun h => ¬LowExpo (n + 1) h) -
        confGap (confHyb ae prg len clen adversary 0 (n + 1) (n + 1))
          (fun h => ¬LowExpo (n + 1) h)| ≤
      (prg.prgAdvantage (confPrgRed ae prg len clen adversary n)).toReal +
        distAdvantage ae len clen (confAeadRed ae prg len clen adversary n) := by
  have hprg := confGap_le_prgAdvantage ae prg len clen adversary n
  have haead := confGap_confHybKey_sub_eq ae len clen hkg prg adversary n
  have hmix : confGap (confHybKey ae prg len clen adversary (n + 1) n)
      (fun h => ¬LowExpo (n + 1) h) =
      confGap (confHyb ae prg len clen adversary 0 (n + 1) n) (fun h => ¬LowExpo (n + 1) h) := by
    rw [confGap_confHyb_eq_low, confGap, confGap,
      prEvent_confHybKey_eq ae prg len clen adversary n fun r => r.1 = r.2.1 ∧ ¬LowExpo (n + 1)
        r.2.2,
      prEvent_confHybKey_eq ae prg len clen adversary n fun r => ¬LowExpo (n + 1) r.2.2]
  rw [← confGap_confHyb_eq_low, hmix] at haead
  calc _ = |(confGap (confHyb ae prg len clen adversary 0 n n) (fun h => ¬LowExpo (n + 1) h) -
          confGap (confHyb ae prg len clen adversary 0 (n + 1) n) (fun h => ¬LowExpo (n + 1) h)) +
        (confGap (confHyb ae prg len clen adversary 0 (n + 1) n) (fun h => ¬LowExpo (n + 1) h) -
          confGap (confHyb ae prg len clen adversary 0 (n + 1) (n + 1))
            (fun h => ¬LowExpo (n + 1) h))| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hprg (le_of_eq haead))

/-- **Step 4, confidentiality.** Let `ae` be a correct AEAD scheme with a uniform key, let
`prg : W → W × Kae` be a PRG, let `A` be an FS-AEAD adversary, and let `L ∈ ℕ`. Write `C_{>L}`
for a challenge at a position above `L` in the hybrid `G_L`. Then
```text
|Pr_{G_rej}[b = b'] - 1/2| ≤ Σ_{j=1..L} (Adv^prg(P'_j) + Adv^aead-dist(E'_j)) + Pr_{G_L}[C_{>L}] / 2
```
where `P'_j` is `confPrgRed … (j - 1)` and `E'_j` is `confAeadRed … (j - 1)`. `Adv^aead-dist` is
the advantage in the one-time IND-CCA game with `lenM = len`. -/
theorem abs_prEvent_securityExpRej_sub_le [SampleableType W] [SampleableType Kae]
    {ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae} (hae : ae.Correct)
    (hkg : ae.keygen =ᵈ ($ᵗ Kae : ProbComp Kae)) (prg : PRGScheme W (W × Kae))
    (len : M → ℕ) (clen : ℕ → ℕ) (L : ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :
    |(Pr{let x ← securityExpRej (fromAEADPRG ae prg) len Prod.fst adversary}[x = true]).toReal -
        1 / 2| ≤
      ∑ n ∈ Finset.range L, ((prg.prgAdvantage (confPrgRed ae prg len clen adversary n)).toReal +
        distAdvantage ae len clen (confAeadRed ae prg len clen adversary n)) +
      (Pr{let r ← confHyb ae prg len clen adversary 0 L L}[ChalAbove L r.2.2]).toReal / 2 := by
  set H : ℕ → ProbComp (Bool × Bool × ConfHist) := fun j => confHyb ae prg len clen adversary 0 j j
  have hf : ∀ r : Bool × Bool × ConfHist, expoIdx L r.2.2 ≤ L := fun r => min_le_left _ _
  have t₁ := ToVCVio.prEvent_hybrid_telescope H (fun r => r.1 = r.2.1)
    (fun r => expoIdx L r.2.2) L hf
  have t₂ := ToVCVio.prEvent_hybrid_telescope H (fun _ => True) (fun r => expoIdx L r.2.2) L hf
  simp only [true_and] at t₂
  have hone : (Pr{let r ← H 0}[True]).toReal = 1 := by
    rw [prEvent_true_eq_one, ENNReal.toReal_one]
  -- the gap of `G_0` as a telescope of gaps
  have hdiag : ∑ v ∈ Finset.range (L + 1), confGap (H v) (fun h => expoIdx L h = v) =
      ∑ v ∈ Finset.range (L + 1), (Pr{let x ← H v}[x.1 = x.2.1 ∧ expoIdx L x.2.2 = v]).toReal -
        (∑ v ∈ Finset.range (L + 1), (Pr{let x ← H v}[expoIdx L x.2.2 = v]).toReal) / 2 := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    rfl
  have hgap : ∑ j ∈ Finset.range L, (confGap (H j) (fun h => j + 1 ≤ expoIdx L h) -
        confGap (H (j + 1)) (fun h => j + 1 ≤ expoIdx L h)) =
      ∑ j ∈ Finset.range L, ((Pr{let x ← H j}[x.1 = x.2.1 ∧ j + 1 ≤ expoIdx L x.2.2]).toReal -
        (Pr{let x ← H (j + 1)}[x.1 = x.2.1 ∧ j + 1 ≤ expoIdx L x.2.2]).toReal) -
      (∑ j ∈ Finset.range L, ((Pr{let x ← H j}[j + 1 ≤ expoIdx L x.2.2]).toReal -
        (Pr{let x ← H (j + 1)}[j + 1 ≤ expoIdx L x.2.2]).toReal)) / 2 := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [confGap]
    ring
  have key : (Pr{let x ← H 0}[x.1 = x.2.1]).toReal - 1 / 2 =
      ∑ v ∈ Finset.range (L + 1), confGap (H v) (fun h => expoIdx L h = v) +
        ∑ j ∈ Finset.range L, (confGap (H j) (fun h => j + 1 ≤ expoIdx L h) -
          confGap (H (j + 1)) (fun h => j + 1 ≤ expoIdx L h)) := by
    rw [hdiag, hgap]
    linarith [t₁, t₂, hone]
  -- the diagonal terms
  have hdiag0 : ∑ v ∈ Finset.range (L + 1), confGap (H v) (fun h => expoIdx L h = v) =
      confGap (H L) (fun h => expoIdx L h = L) := by
    rw [Finset.sum_range_succ, Finset.sum_eq_zero fun v hv => ?_, zero_add]
    exact confGap_confHyb_expo_eq_zero ae prg len clen adversary (Finset.mem_range.mp hv)
  -- the gap terms
  have hstep : ∀ j ∈ Finset.range L, |confGap (H j) (fun h => j + 1 ≤ expoIdx L h) -
      confGap (H (j + 1)) (fun h => j + 1 ≤ expoIdx L h)| ≤
      (prg.prgAdvantage (confPrgRed ae prg len clen adversary j)).toReal +
        distAdvantage ae len clen (confAeadRed ae prg len clen adversary j) := by
    intro j hj
    have hE : (fun h => j + 1 ≤ expoIdx L h) = fun h => ¬LowExpo (j + 1) h :=
      funext fun h => propext (le_expoIdx_iff (Finset.mem_range.mp hj) h)
    rw [hE]
    exact abs_confGap_step_le hkg prg len clen adversary j
  rw [prEvent_securityExpRej_eq_confHyb hae prg len clen adversary]
  change |(Pr{let x ← H 0}[x.1 = x.2.1]).toReal - 1 / 2| ≤ _
  rw [key, hdiag0, add_comm]
  refine (abs_add_le _ _).trans (add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum hstep)) ?_)
  exact abs_confGap_confHyb_expo_le ae prg len clen adversary L

end FromAEADPRG


end FSAEADScheme
