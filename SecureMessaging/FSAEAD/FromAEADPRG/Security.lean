/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.FromAEADPRG.Security.Authenticity
public import SecureMessaging.FSAEAD.FromAEADPRG.Security.Confidentiality

/-!
# FS-AEAD from AEAD and PRG — security

Theorem 5 of [ACD19]: the FS-AEAD scheme from a correct AEAD scheme and a PRG is secure.

Let the adversary make at most `q` calls of `O-Transmit-A` and `O-Chall-A` together
(`SendQueryBound`), and let every injection have an index at most `N` (`InjectIndexBound`). Let
`L = max q N`. The proof has six steps:

- Step 0. `fs-aead` and `fs-aead-nd` (no win by `O-Deliver-B`) are the same game, because `ae` is
  correct (`fromAEADPRG_securityExp_eq_noDeliverWin`).
- Step 1. The advantage in `fs-aead-nd` is at most `Pr[win] + |Pr_{G_rej}[b = b'] - 1/2|`
  (`advantage_noDeliverWin_le`).
- Step 2. `O-Deliver-B^lk` delivers an honest ciphertext by lookup in `trans`, without `Dec`.
  `G_rej` with `O-Deliver-B^lk` is `G_rej` (`gameRun_rej_eq_lookup`), and `fs-aead-nd` with
  `O-Deliver-B^lk` is identical to `fs-aead-nd` until `win` (`prEvent_gameRun_mon_win_eq_lookup`).
- Step 3. `Pr[win] ≤ Σ_{j=1..L} (Adv^prg(P_j) + Adv^aead-dist(E_j)) + Pr_{H_0}[W_{>L}]`
  (`prEvent_winExp_le`). No first win is above `N` (`prEvent_hybExp_firstWin_above_eq_zero`).
- Step 4. `|Pr_{G_rej}[b = b'] - 1/2| ≤ Σ_{j=1..L} (Adv^prg(P'_j) + Adv^aead-dist(E'_j))
  + Pr_{G_L}[C_{>L}] / 2` (`abs_prEvent_securityExpRej_sub_le`). No challenge is above `q`
  (`prEvent_confHyb_chalAbove_eq_zero`).
- Step 5. This file adds the bounds.

Each row below is one game hop: the games, the file (relative to
`SecureMessaging/FSAEAD/FromAEADPRG/Security/`), the main lemma, and the term that the hop adds to
the bound. In Steps 3 and 4, `1 ≤ j ≤ L` and `1 ≤ p ≤ L`.

| Hop | File | Lemma | Term |
|---|---|---|---|
| `fs-aead` → `fs-aead-nd` | `../Correctness` | `fromAEADPRG_securityExp_eq_noDeliverWin` | 0 |
| `fs-aead-nd` → `win`, `G_rej` | `../../Security/Reject` | `advantage_noDeliverWin_le` | split |
| `O-Deliver-B` → `O-Deliver-B^lk` | `Chain/Lookup` | `prEvent_gameRun_mon_win_eq_lookup` | 0 |
| `fs-aead-nd` → `H_0` | `Authenticity/Game` | `prEvent_noDeliverWin_win_eq_authExp` | 0 |
| `H_{j-1}` → `H_j` | `Authenticity/Hybrid` | `prgReal_prgRed` | `Adv^prg(P_j)` |
| `W_p` in `H_p` | `Authenticity/AeadRed` | `distAdvantage_aeadRed` | `Adv^aead-dist(E_p)` |
| `W_{>L}` in `H_0` | `Authenticity` | `prEvent_hybExp_firstWin_above_eq_zero` | 0 |
| `G_rej` → `G_0` | `Confidentiality` | `prEvent_securityExpRej_eq_confHyb` | 0 |
| `G_{j-1}` → `G_{j,j-1}` | `Confidentiality/Hybrid` | `confGap_le_prgAdvantage` | `Adv^prg(P'_j)` |
| `G_{j,j-1}` → `G'_j` | `Confidentiality/Mix` | `prEvent_confHybKey_eq` | 0 |
| `G'_j` → `G_j` | `Confidentiality/AeadRed` | `confGap_confHybKey_sub_eq` | `Adv^aead-dist(E'_j)` |
| `m = v` in `G_v`, `v < L` | `Confidentiality/End` | `confGap_confHyb_expo_eq_zero` | 0 |
| `m = L` in `G_L` | `Confidentiality/End` | `abs_confGap_confHyb_expo_le` | `Pr_{G_L}[C_{>L}]/2` |
| `C_{>L}` in `G_L` | `Confidentiality/End` | `prEvent_confHyb_chalAbove_eq_zero` | 0 |

The second row splits the advantage into the authenticity term `Pr[win]` (Step 3) and the
confidentiality term of `G_rej` (Step 4). `Chain/` holds what both steps use: delivery by lookup,
the game states on a chain, the hybrid chains, and the monad of the AEAD reductions.

`Adv^aead-dist` is the advantage in the one-time IND-CCA game of `SecureMessaging.AEAD.Defs`,
whose decryption oracle rejects only the challenge pair (deviation D1). [ACD19] states the bound
`q · (ε_aead + ε_prg)`. Here it is `2L · (ε_prg + ε_aead)`
(`advantage_fromAEADPRG_le_of_le`): the factor 2 comes from the separate authenticity and
confidentiality arguments, and `L` replaces `q` because an injection can reach an index above
`q`.

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the
  Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf
  — Theorem 5.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal AEADScheme

namespace FSAEADScheme

open FromAEADPRG

variable {W Kae Cae AD M : Type} [DecidableEq AD] [DecidableEq M] [DecidableEq Cae]
  [SampleableType W] [SampleableType Kae] [LenSampleable Cae]

/-- **Theorem 5 of [ACD19].** Let `ae` be a correct AEAD scheme with a uniform key, and let
`prg : W → W × Kae` be a PRG. Let `A` be an FS-AEAD adversary that makes at most `q` calls of
`O-Transmit-A` and `O-Chall-A` together, and whose injections all have an index at most `N`. Let
`L = max q N`. Then
```text
Adv^fs-aead(A) ≤ Σ_{j=1..L} (Adv^prg(P_j) + Adv^aead-dist(E_j)
                          + Adv^prg(P'_j) + Adv^aead-dist(E'_j))
```
where `P_j` is `prgRed … (j - 1)`, `E_j` is `aeadRed … j`, `P'_j` is `confPrgRed … (j - 1)` and
`E'_j` is `confAeadRed … (j - 1)`.

The bound grows with `N`, the largest injected index, and the reductions sample up to `L` chain
steps. The theorem is therefore useful only when `N` is polynomial in the run time of `A`.

The statement holds for every `clen`, but it is meaningful only when `clen` is the ciphertext
length of `ae`: otherwise the length of the challenge ciphertext separates the real and random
worlds, and `Adv^aead-dist(E_j)` and `Adv^aead-dist(E'_j)` can be close to 1. -/
-- ANCHOR: advantage_fromAEADPRG_le
theorem advantage_fromAEADPRG_le {ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae}
    (hae : ae.Correct) (hkg : ae.keygen =ᵈ ($ᵗ Kae : ProbComp Kae)) (prg : PRGScheme W (W × Kae))
    (len : M → ℕ) (clen : ℕ → ℕ) {q N : ℕ}
    {adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)}
    (hq : SendQueryBound adversary q) (hN : InjectIndexBound Prod.fst adversary N) :
    advantage (fromAEADPRG ae prg) len adversary ≤
      ∑ n ∈ Finset.range (max q N),
        ((prg.prgAdvantage (prgRed ae prg len (max q N) adversary n)).toReal +
          distAdvantage ae len clen (aeadRed ae prg len adversary (n + 1)) +
          (prg.prgAdvantage (confPrgRed ae prg len clen adversary n)).toReal +
          distAdvantage ae len clen (confAeadRed ae prg len clen adversary n))
-- ANCHOR_END: advantage_fromAEADPRG_le
    := by
  have h₃ := prEvent_winExp_le hae hkg prg len len clen (max q N) adversary
  have h₄ := abs_prEvent_securityExpRej_sub_le hae hkg prg len clen (max q N) adversary
  rw [prEvent_hybExp_firstWin_above_eq_zero ae prg len 0 hN (le_max_right q N) 0,
    ENNReal.toReal_zero, add_zero] at h₃
  rw [prEvent_confHyb_chalAbove_eq_zero ae prg len clen hq (le_max_left q N), ENNReal.toReal_zero,
    zero_div, add_zero] at h₄
  rw [advantage, fromAEADPRG_securityExp_eq_noDeliverWin ae prg hae]
  refine (advantage_noDeliverWin_le (rcvIndex_fromAEADChain ae _) len adversary).trans ?_
  calc _ ≤ _ := add_le_add h₃ h₄
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring

/-- **Theorem 5 of [ACD19] with uniform bounds.** Under the hypotheses of
`advantage_fromAEADPRG_le`, let `ε_prg` bound the advantage of each PRG reduction and `ε_aead` the
advantage of each AEAD reduction. Then `Adv^fs-aead(A) ≤ 2L · (ε_prg + ε_aead)`. -/
theorem advantage_fromAEADPRG_le_of_le {ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae}
    (hae : ae.Correct) (hkg : ae.keygen =ᵈ ($ᵗ Kae : ProbComp Kae)) (prg : PRGScheme W (W × Kae))
    (len : M → ℕ) (clen : ℕ → ℕ) {q N : ℕ}
    {adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)}
    (hq : SendQueryBound adversary q) (hN : InjectIndexBound Prod.fst adversary N)
    {εprg εaead : ℝ}
    (hprg : ∀ n < max q N,
      (prg.prgAdvantage (prgRed ae prg len (max q N) adversary n)).toReal ≤ εprg ∧
        (prg.prgAdvantage (confPrgRed ae prg len clen adversary n)).toReal ≤ εprg)
    (haead : ∀ n < max q N,
      distAdvantage ae len clen (aeadRed ae prg len adversary (n + 1)) ≤ εaead ∧
        distAdvantage ae len clen (confAeadRed ae prg len clen adversary n) ≤ εaead) :
    advantage (fromAEADPRG ae prg) len adversary ≤ 2 * max q N * (εprg + εaead) := by
  refine (advantage_fromAEADPRG_le hae hkg prg len clen hq hN).trans ?_
  calc _ ≤ ∑ _n ∈ Finset.range (max q N), (εprg + εaead + εprg + εaead) :=
        Finset.sum_le_sum fun n hn => by
          obtain ⟨h₁, h₂⟩ := hprg n (Finset.mem_range.mp hn)
          obtain ⟨h₃, h₄⟩ := haead n (Finset.mem_range.mp hn)
          gcongr
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

end FSAEADScheme
