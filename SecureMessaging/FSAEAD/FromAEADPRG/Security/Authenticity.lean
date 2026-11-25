/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.FromAEADPRG.Security.Authenticity.AeadRed
public import ToVCVio.EvalDist.BoolDist
public import ToVCVio.EvalDist.HybridTelescope

/-!
# FS-AEAD from AEAD and PRG — authenticity

Step 3 of the proof of Theorem 5 of [ACD19]: the authenticity term `Pr[win]` of `fs-aead-nd`.

Write `W_p` for the event "the first win is at index `p`" in `G_auth^0`, and `H_j` for the
hybrid with uniform chain steps `1, …, j`. Split the first wins with `p ≤ L` by `p`
(`ToVCVio.prEvent_hybrid_telescope`):
```text
Pr_{H_0}[W_{≤L}] = Σ_{p ≤ L} Pr_{H_p}[W_p]
                 + Σ_{j < L} (Pr_{H_j}[W_{[j+1, L]}] - Pr_{H_{j+1}}[W_{[j+1, L]}])
```
- `Pr_{H_0}[W_0] = 0`: B accepts no index 0.
- `Pr_{H_p}[W_p] = Adv^aead-dist(E_p)` for `p ≥ 1` (`distAdvantage_aeadRed`).
- The gap between `H_j` and `H_{j+1}` is at most `Adv^prg(P_{j+1})`
  (`prgReal_prgRed`, `prgIdeal_prgRed`).

So (`prEvent_winExp_le`)
```text
Pr_{fs-aead-nd}[win] ≤ Σ_{j=1..L} (Adv^prg(P_j) + Adv^aead-dist(E_j)) + Pr_{H_0}[W_{>L}]
```
The last term is the probability of a first win above `L`. `Adv^aead-dist` is the advantage in
the one-time IND-CCA game of `SecureMessaging.AEAD.Defs`, whose decryption oracle rejects only
the challenge pair (deviation D1). Figure 1 of [ACD19] rejects every query with the challenge
ciphertext, so the bound uses the AEAD assumption for the pair guard.

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

variable {W Kae Cae AD M : Type} [DecidableEq AD] [DecidableEq Cae]

/-- The gap between `H_n` and `H_{n+1}` on a first win in `[n + 1, L]` is at most the advantage of
the PRG reduction `P_{n+1}`. -/
theorem hybExp_gap_le_prgAdvantage [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (L : ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (n : ℕ) :
    (Pr{let z ← hybExp ae prg len 0 adversary n}[winIn (n + 1) L z.2.2 = true]).toReal -
        (Pr{let z ← hybExp ae prg len 0 adversary (n + 1)}[winIn (n + 1) L z.2.2 = true]).toReal ≤
      (prg.prgAdvantage (prgRed ae prg len L adversary n)).toReal := by
  rw [← prgReal_prgRed, ← prgIdeal_prgRed, PRGScheme.prgAdvantage,
    ToVCVio.toReal_boolDist_evalDist]
  exact le_abs_self _

/-- In every hybrid, B accepts no injection at index 0, so no first win is at 0. -/
theorem prEvent_hybExp_firstWin_zero [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (j : ℕ) :
    Pr{let z ← hybExp ae prg len 0 adversary j}[z.2.2.firstWin = some 0] = 0 := by
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => ?_
  simp only [hybExp, authExp, mem_support_bind_iff] at hz
  obtain ⟨U, -, k, -, b, -, hz⟩ := hz
  have := (authInv_authRun ae _ len b 0 adversary k z hz).firstWin 0 h
  omega

/-- Let every injection of the adversary have an index at most `N ≤ L`. Then no first win in a
hybrid is above `L`. -/
theorem prEvent_hybExp_firstWin_above_eq_zero [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (s : ℕ) {adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)}
    {N L : ℕ} (hN : InjectIndexBound Prod.fst adversary N) (hNL : N ≤ L) (j : ℕ) :
    Pr{let z ← hybExp ae prg len s adversary j}[∃ p, z.2.2.firstWin = some p ∧ L < p] = 0 := by
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ⟨p, hp, hLp⟩ => ?_
  simp only [hybExp, authExp, mem_support_bind_iff] at hz
  obtain ⟨U, -, k, -, b, -, hz⟩ := hz
  have := firstWin_le_of_injectIndexBound (rcvIndex_fromAEADChain ae _) len b s _ hN _ z hz p hp
  omega

/-- **The hybrid argument.** Let the AEAD key be uniform. Then the probability of a first win at
an index `p ≤ L` in `H_0` is at most
`Σ_{j=1..L} (Adv^prg(P_j) + Adv^aead-dist(E_j))`. -/
theorem prEvent_hybExp_le [SampleableType W] [SampleableType Kae] [LenSampleable Cae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (hkg : ae.keygen =ᵈ ($ᵗ Kae : ProbComp Kae))
    (prg : PRGScheme W (W × Kae)) (len lenM : M → ℕ) (clen : ℕ → ℕ) (L : ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :
    (Pr{let z ← hybExp ae prg len 0 adversary 0}[∃ p, z.2.2.firstWin = some p ∧ p ≤ L]).toReal ≤
      ∑ n ∈ Finset.range L, ((prg.prgAdvantage (prgRed ae prg len L adversary n)).toReal +
        distAdvantage ae lenM clen (aeadRed ae prg len adversary (n + 1))) := by
  set H := fun j => hybExp ae prg len 0 adversary j
  set X : Bool × (CState W Kae AD M Cae × AuthHist) → Prop :=
    fun z => ∃ p, z.2.2.firstWin = some p ∧ p ≤ L
  set f : Bool × (CState W Kae AD M Cae × AuthHist) → ℕ :=
    fun z => min (z.2.2.firstWin.getD 0) L
  have ht := ToVCVio.prEvent_hybrid_telescope H X f L fun z => min_le_right _ _
  -- the diagonal terms
  have hdiag (v : ℕ) (hv : v ≤ L) (mx : ProbComp (Bool × (CState W Kae AD M Cae × AuthHist))) :
      Pr{let z ← mx}[X z ∧ f z = v] = Pr{let z ← mx}[z.2.2.firstWin = some v] := by
    refine prEvent_congr mx _ _ fun z => ?_
    simp only [X, f]
    rcases z.2.2.firstWin with _ | q
    · simp only [reduceCtorEq, false_and, exists_false]
    · simp only [Option.some.injEq, exists_eq_left', Option.getD_some]
      constructor
      · rintro ⟨hq, rfl⟩
        exact (min_eq_left hq).symm
      · rintro rfl
        exact ⟨hv, min_eq_left hv⟩
  -- the gap terms
  have hgap (j : ℕ) (mx : ProbComp (Bool × (CState W Kae AD M Cae × AuthHist))) :
      Pr{let z ← mx}[X z ∧ j + 1 ≤ f z] = Pr{let z ← mx}[winIn (j + 1) L z.2.2 = true] := by
    refine prEvent_congr mx _ _ fun z => ?_
    simp only [X, f, winIn]
    rcases z.2.2.firstWin with _ | q
    · simp only [reduceCtorEq, false_and, exists_false, Bool.false_eq_true]
    · simp only [Option.some.injEq, exists_eq_left', Option.getD_some, decide_eq_true_eq]
      constructor
      · rintro ⟨hq, hj⟩
        exact ⟨by rw [min_eq_left hq] at hj; exact hj, hq⟩
      · rintro ⟨hj, hq⟩
        exact ⟨hq, by rw [min_eq_left hq]; exact hj⟩
  rw [ht, Finset.sum_range_succ', hdiag 0 (Nat.zero_le _),
    prEvent_hybExp_firstWin_zero, ENNReal.toReal_zero, add_zero, Finset.sum_add_distrib,
    add_comm]
  refine add_le_add (Finset.sum_le_sum fun j hj => ?_) (le_of_eq (Finset.sum_congr rfl
    fun n hn => ?_))
  · rw [hgap, hgap]
    exact hybExp_gap_le_prgAdvantage ae prg len L adversary j
  · rw [Finset.mem_range] at hn
    rw [hdiag (n + 1) (by omega), distAdvantage_aeadRed hkg]
    refine congrArg ENNReal.toReal (prEvent_congr _ _ _ fun z => ?_)
    simp only [winIn]
    rcases z.2.2.firstWin with _ | q
    · simp only [reduceCtorEq, Bool.false_eq_true]
    · simp only [Option.some.injEq, decide_eq_true_eq]
      omega

end FromAEADPRG

open FromAEADPRG

variable {W Kae Cae AD M : Type} [DecidableEq AD] [DecidableEq Cae]

/-- **Step 3, authenticity.** Let `ae` be a correct AEAD scheme with a uniform key, and let
`prg : W → W × Kae` be a PRG. Let `A` be an FS-AEAD adversary and `L ∈ ℕ`. Write `W_{>L}` for a
first win at an index above `L` in `H_0`. Then
```text
Pr_{fs-aead-nd}[win] ≤ Σ_{j=1..L} (Adv^prg(P_j) + Adv^aead-dist(E_j)) + Pr_{H_0}[W_{>L}]
```
where `P_j` is `prgRed … (j - 1)` and `E_j` is `aeadRed … j`. `Adv^aead-dist` is the advantage
in the AEAD game with the guard on the challenge pair (deviation D1). -/
theorem prEvent_winExp_le [SampleableType W] [SampleableType Kae] [LenSampleable Cae]
    {ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae} (hae : ae.Correct)
    (hkg : ae.keygen =ᵈ ($ᵗ Kae : ProbComp Kae)) (prg : PRGScheme W (W × Kae))
    (len lenM : M → ℕ) (clen : ℕ → ℕ) (L : ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :
    (Pr{let x ← winExp (fromAEADPRG ae prg) len adversary}[x = true]).toReal ≤
      ∑ n ∈ Finset.range L, ((prg.prgAdvantage (prgRed ae prg len L adversary n)).toReal +
        distAdvantage ae lenM clen (aeadRed ae prg len adversary (n + 1))) +
      (Pr{let z ← hybExp ae prg len 0 adversary 0}[
        ∃ p, z.2.2.firstWin = some p ∧ L < p]).toReal := by
  have h₀ : Pr{let x ← winExp (fromAEADPRG ae prg) len adversary}[x = true] =
      Pr{let z ← hybExp ae prg len 0 adversary 0}[z.2.2.firstWin.isSome = true] := by
    rw [winExp, prEvent_map, hybExp_zero]
    exact prEvent_noDeliverWin_win_eq_authExp hae (fun _ => prg.gen) len adversary
  have h₁ : Pr{let z ← hybExp ae prg len 0 adversary 0}[z.2.2.firstWin.isSome = true] ≤
      Pr{let z ← hybExp ae prg len 0 adversary 0}[∃ p, z.2.2.firstWin = some p ∧ p ≤ L] +
        Pr{let z ← hybExp ae prg len 0 adversary 0}[∃ p, z.2.2.firstWin = some p ∧ L < p] := by
    refine le_trans (prEvent_mono _ _ _ fun z hz => ?_) (prEvent_or_le _ _ _)
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hz
    rcases Nat.lt_or_ge L p with h | h
    · exact .inr ⟨p, hp, h⟩
    · exact .inl ⟨p, hp, h⟩
  rw [h₀]
  refine le_trans (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _,
    prEvent_ne_top _⟩) h₁) ?_
  rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)]
  exact add_le_add_left (prEvent_hybExp_le ae hkg prg len lenM clen L adversary) _

end FSAEADScheme
