/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromEtM.Security.PrfHop
import SecureMessaging.AEAD.FromEtM.Security.Auth.Hop
import SecureMessaging.AEAD.FromEtM.Security.EncHop
import SecureMessaging.AEAD.FromEtM.Security.RandHop

/-!
# Encrypt-then-MAC — Security

Security theorem for the EtM construction: the one-time IND-CCA advantage of
`etmAEAD se prf` is bounded by the PRF advantage of `prf`, the IND$-CPA
advantage of `se`, and `q_d/|T|` (tag-guessing probability per decryption
query, where `q_d` upper-bounds the adversary's decryption queries).

## Paper References

The *notion* targeted here is ACD19's (defined in `AEAD/Defs.lean`); the *proof*
follows NRS14. Both use the same ind$ (random-ciphertext) notion, so the
adaptation is faithful.

Our construction adapts **scheme A5** (= A2.100_111) from NRS14 Figure 2.
The security proof adapts **Theorem 1** (for A5), with:
- Concrete bound from **Figure 9**: `Adv^nAE ≤ Adv^prf + Adv^ivE + q_d/2^τ`
- Proof structure from **Lemma 3** (common opening) + **Appendix A.2** (auth bound)

## Structure

The proof uses an **OracleSpec-polymorphic game skeleton** so that games
(instantiated with `spec = unifSpec` = `ProbComp`) and reductions
(instantiated with `spec = PRFOracleSpec` or the IND$-CPA spec) are direct
instantiations of the same definition. The hop proofs use `simulateQ`
compositionality.

Note: intermediate games cannot be `AEADScheme` instances because game hops
change internal components (e.g., replacing PRF with random oracle) while
preserving the oracle interface.

## NRS14 Correspondence

| Lean definition | NRS14 reference |
|---|---|
| `etmAEAD` | Figure 2, scheme A5, adapted: no nonce, one-time keys |
| `DetSEAlg` / `distAdvantage` | Section 2, ivE scheme / `Adv^ivE` (one query) |
| `PRFScheme` / `prfAdvantage` | Section 2, function family F / `Adv^prf` |
| `decryptQueryBound` / `q_d` | `q_d` in Appendix A.2; `IsQueryBoundP` on decrypt index |
| `game0` | Lemma 3 starting game (Figure 4 left: `Enc` + `Dec`) |
| `game1` | Lemma 3 eq. (4): replace F^tag with random ρ |
| `game2` | Appendix A.2: disable decryption (forgery bound) |
| `game3` | Figure 4 right column: `$` + `⊥` oracles |
| `game0_game1_le_prf` | Lemma 3 eq. (4): PRF hop, cost `Adv^prf` |
| `game1_game2_le_auth` | Appendix A.2, A5 Case 1: auth bound `q_d/2^τ` (see note) |
| `game2_game3_le_enc` | Lemma 3, privacy reduction D₁: cost `Adv^ivE` |
| `etmAEAD_security` | Theorem 1 for A5; Figure 9 bound |
| `prfReduction` | Lemma 3: adversary B(A) |
| `encReduction` | Lemma 3: privacy reduction D₁(A) |

Note on `game1_game2_le_auth`: the `q_d` factor is proved *directly*, by
per-distinct-point lazy-sampling accounting (`probForge_le_queryBound_div_card`),
**not** via NRS14's Lemma-2 single-decryption-query hybrid.
-/

open OracleSpec OracleComp ENNReal PRFScheme AEADScheme

variable {K_e K_m M AD C_e T : Type}
  [DecidableEq AD] [DecidableEq C_e] [DecidableEq T]
  [Inhabited C_e] [Inhabited T]
  [SampleableType C_e] [SampleableType T]

/-! ## Main security theorem -/

/-- **EtM one-time IND-CCA security** (NRS14 Theorem 1 for A5, adapted).

The one-time IND-CCA distinguishing advantage of `etmAEAD se prf` is bounded
by the PRF advantage, the tag-guessing probability per decryption query, and
the IND$-CPA advantage:

  `Adv^{ot-cca-ror}_{EtM}(A) ≤ Adv^{prf}(B) + q_d/|T| + Adv^{ind$}(D)`

where `B = prfReduction se adv` and `D = encReduction se adv` are explicit
reductions (skeleton instantiations), and `q_d` upper-bounds the adversary's
number of decryption queries (tied to `adv` via `decryptQueryBound`, i.e.
`IsQueryBoundP` on the decrypt-oracle index).

NRS14 Figure 9 bound: `Adv^nAE ≤ Adv^prf_F(B) + Adv^ivE_E(D₁) + q_d/2^τ`.
Our one-time adaptation: `Adv^ivE → Adv^{ind$-cpa}`, `2^τ → |T|`. -/
theorem etmAEAD_security [Inhabited K_e]
    (se : DetSEAlg K_e M C_e) (prf : PRFScheme K_m (AD × C_e) T)
    (adv : OneTimeCCAAdversary AD M (C_e × T))
    (q_d : ℕ) [Fintype T]
    (hqd : AEADScheme.decryptQueryBound adv q_d)
    (hkm : Pr[⊥ | prf.keygen] = 0) :
    AEADScheme.distAdvantage (etmAEAD se prf) adv ≤
      PRFScheme.prfAdvantage prf (prfReduction se adv) +
      ↑q_d * (Fintype.card T : ℝ)⁻¹ +
      DetSEAlg.distAdvantage se (encReduction se adv) := by
  -- NRS14 Theorem 1 / Figure 9: triangle inequality over the game sequence.
  -- distAdvantage = |Pr[rand = 1] - Pr[real = 1]|
  --              = |Pr[game3 = 1] - Pr[game0 = 1]|    (by game0_eq_real, game3_eq_rand)
  -- By triangle inequality:
  --   |game3 - game0| ≤ |game0 - game1| + |game1 - game2| + |game2 - game3|
  -- Substituting the three hop bounds gives the result.
  unfold AEADScheme.distAdvantage
  rw [← game3_eq_rand se prf adv hkm, ← game0_eq_real se prf adv]
  calc |(Pr[= true | game3 se adv]).toReal -
        (Pr[= true | game0 se prf adv]).toReal|
    _ ≤ |(Pr[= true | game0 se prf adv]).toReal -
         (Pr[= true | game1 se adv]).toReal| +
        |(Pr[= true | game1 se adv]).toReal -
         (Pr[= true | game2 se adv]).toReal| +
        |(Pr[= true | game2 se adv]).toReal -
         (Pr[= true | game3 se adv]).toReal| := by
          set g0 := (Pr[= true | game0 se prf adv]).toReal
          set g1 := (Pr[= true | game1 se adv]).toReal
          set g2 := (Pr[= true | game2 se adv]).toReal
          set g3 := (Pr[= true | game3 se adv]).toReal
          have h1 := abs_sub_le g3 g2 g0
          have h2 := abs_sub_le g2 g1 g0
          have h3 : |g2 - g3| = |g3 - g2| := abs_sub_comm g2 g3
          have h4 : |g1 - g2| = |g2 - g1| := abs_sub_comm g1 g2
          have h5 : |g0 - g1| = |g1 - g0| := abs_sub_comm g0 g1
          linarith
    _ ≤ PRFScheme.prfAdvantage prf (prfReduction se adv) +
        ↑q_d * (Fintype.card T : ℝ)⁻¹ +
        DetSEAlg.distAdvantage se (encReduction se adv) :=
      add_le_add (add_le_add (game0_game1_le_prf se prf adv)
        (game1_game2_le_auth se adv q_d hqd)) (game2_game3_le_enc se adv)
