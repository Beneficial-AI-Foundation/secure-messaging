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

Security theorem for the EtM construction `etmAEAD se prf`.

## Main result

`etmAEAD_security`: the one-time IND-CCA distinguishing advantage of
`etmAEAD se prf` is bounded by the PRF advantage of `prf`, the IND$-CPA
advantage of `se`, and a tag-guessing term:

  `Adv^{ot-cca-ror}(A) ≤ Adv^{prf}(B) + q_d/|T| + Adv^{ind$-cpa}(D)`

where `B = prfReduction se A` and `D = encReduction se A`, and `q_d`
upper-bounds the number of the adversary's decryption queries.

## Notation

| Symbol | Meaning |
|---|---|
| `se` | inner deterministic symmetric cipher (`DetSEAlg`) |
| `prf` | PRF used to compute the authentication tag (`PRFScheme`) |
| `A` (`adv`) | the one-time IND-CCA adversary |
| `q_d` | upper bound on `A`'s number of decryption queries (`decryptQueryBound`) |
| `\|T\|` | size of the tag space (`Fintype.card T`) |
| `Adv^{ot-cca-ror}` | one-time IND-CCA (real-or-random) advantage of the AEAD scheme |
| `Adv^{prf}` | PRF distinguishing advantage |
| `Adv^{ind$-cpa}` | one-time IND$-CPA advantage of `se` |

## Reductions

The bound is witnessed by two explicit reductions (both defined in
`Security/Games.lean` as instantiations of the shared game skeleton):

- `prfReduction se A` — used for the `game0 → game1` hop; charges `Adv^{prf}`.
- `encReduction se A` — used for the `game2 → game3` hop; charges `Adv^{ind$-cpa}`.

## Proof sketch: game hops

The proof walks a sequence of four games `game0 … game3`. `game0` is the real
one-time IND-CCA experiment and `game3` is the ideal one (random ciphertext +
always-reject decryption), so
`Adv^{ot-cca-ror}(A) = |Pr[game3 = 1] − Pr[game0 = 1]|`. The triangle inequality
over the three hops gives the bound. Each hop changes exactly one component:

```text
        encrypt oracle      tag oracle      decrypt oracle    hop cost  (reduction)
        ──────────────      ──────────      ──────────────    ────────────────────
game0   c = Enc_ke(m)       F_km(ad,c)      verify F, then Dec
  │                                                           Adv^{prf}   (prfReduction)
  ▼   replace PRF F with a lazy random oracle ρ
game1   c = Enc_ke(m)       ρ(ad,c)         verify ρ, then Dec
  │                                                           q_d / |T|   (forgery bound)
  ▼   disable decryption: a fresh verify point accepts w.p. 1/|T|
game2   c = Enc_ke(m)       ρ(ad,c)         ⊥ (always reject)
  │                                                           Adv^{ind$}  (encReduction)
  ▼   replace the real ciphertext and tag with uniform samples
game3   c ←$ C_e            t ←$ T          ⊥ (always reject)

  game0 = real one-time IND-CCA experiment
  game3 = ideal experiment ($ ciphertext, ⊥ decryption)
```

## Tag queries

After the `game0 → game1` hop the PRF is replaced by a lazily-sampled random
oracle on `(AD × C_e)`. From then on, both tag *computation* (in encryption) and
tag *verification* (in decryption) are **random-oracle queries** — these are
internal to the proof (an artifact of lazy-sampling the tag function), **not**
part of the ACD19 AEAD game: the adversary `A` still only ever sees the encrypt
and decrypt oracles.

## Structure

Games and reductions are both instantiations of one **OracleSpec-polymorphic
game skeleton** (`etmGameSkeleton`, `Security/Games.lean`): the four `game*`
instantiate it at `spec = unifSpec` (= `ProbComp`), while the reductions
instantiate the *same* skeleton at the PRF / IND$-CPA spec, forwarding only the
adversary's uniform-sampling queries through a `unifImpl` (the `SubSpec` lift).
So a reduction is itself a game, just over a richer oracle spec.

The intermediate games are not `AEADScheme` instances, because the hops change
internal components (e.g. PRF → random oracle) while keeping the encrypt/decrypt
oracle interface the adversary sees fixed.

File layout: this file holds only the main theorem; the games, reductions, and
per-hop lemmas live under `Security/` (`Games.lean`, `PrfHop.lean`,
`Auth/Hop.lean`, `EncHop.lean`, `RandHop.lean`). Generic, scheme-independent
lemmas live under `ToVCVio/`.

## Paper References

The *notion* targeted here is ACD19's (defined in `AEAD/Defs.lean`); the *proof*
is an EtM argument adapted from **NRS14 scheme A5**. The two line up because
ACD19's one-time real-or-random notion and NRS14's ivE/nAE rest on the same
ind$ (random-*ciphertext*) family; the precise, game-by-game correspondence
that backs this is the `## NRS14 Correspondence` table below (not the single
shared-family observation on its own).

Our construction adapts **scheme A5** (= A2.100_111) from NRS14 Figure 2.
The security proof adapts **Theorem 1** (for A5), with:
- Concrete bound from **Figure 9**: `Adv^nAE ≤ Adv^prf + Adv^ivE + q_d/2^τ`
- Proof structure from **Lemma 3** (common opening) + **Appendix A.2** (auth bound)

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
| `game1_game2_le_auth` | Appendix A.2 Case 1: `q_d/|T|` (proved directly, not a per-query hybrid) |
| `game2_game3_le_enc` | Lemma 3, privacy reduction D₁: cost `Adv^ivE` |
| `etmAEAD_security` | Theorem 1 for A5; Figure 9 bound |
| `prfReduction` | Lemma 3: adversary B(A) |
| `encReduction` | Lemma 3: privacy reduction D₁(A) |

## ACD19 vs NRS14: decryption suppression

One place the two notions differ: ACD19's decrypt oracle (`AEAD/Defs.oracleDecrypt`) rejects
**every** query sharing the challenge ciphertext `e*` — any `(a', e*)`, ignoring the associated
data — whereas NRS14 nAE (and Boneh–Shoup §9.10) reject only the exact returned pair `(a*, e*)`.
ACD19 is thus the stronger notion. The gap is immaterial for EtM: a query `(a', e*)` with
`a' ≠ a*` still has to produce the challenge-independent tag on `(a', C*)`, which after the
`game1` PRF hop is a fresh random `ρ`-value — exactly what the `q_d/|T|` authenticity term
(`game1_game2_le_auth`) already bounds.
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


The `NeverFail prf.keygen` instance (i.e. `Pr[⊥ | prf.keygen] = 0`) is the explicit form
of a losslessness property NRS14 has implicitly: there keys are sampled from a set, so keygen
cannot fail. Our `prf.keygen : ProbComp K_m` lives in a more permissive, partiality-aware
type, so we state it. It is satisfied by every standard PRF (whose key is a uniform sample
`$ᵗ K_m`), so it doesn't rule out any construction of interest.
NRS14 Figure 9 bound: `Adv^nAE ≤ Adv^prf_F(B) + Adv^ivE_E(D₁) + q_d/2^τ`.
Our one-time adaptation: `Adv^ivE → Adv^{ind$-cpa}`, `2^τ → |T|`. -/
-- ANCHOR: etmAEAD_security
theorem etmAEAD_security [Inhabited K_e]
    (se : DetSEAlg K_e M C_e) (prf : PRFScheme K_m (AD × C_e) T)
    (adv : OneTimeCCAAdversary AD M (C_e × T))
    (q_d : ℕ) [Fintype T]
    (hqd : AEADScheme.decryptQueryBound adv q_d)
    [NeverFail prf.keygen] :
    AEADScheme.distAdvantage (etmAEAD se prf) adv ≤
      PRFScheme.prfAdvantage prf (prfReduction se adv) +
      ↑q_d * (Fintype.card T : ℝ)⁻¹ +
      DetSEAlg.distAdvantage se (encReduction se adv)
-- ANCHOR_END: etmAEAD_security
  := by
  -- NRS14 Theorem 1 / Figure 9: triangle inequality over the game sequence.
  -- distAdvantage = |Pr[rand = 1] - Pr[real = 1]|
  --              = |Pr[game3 = 1] - Pr[game0 = 1]|    (by game0_eq_real, game3_eq_rand)
  -- By triangle inequality:
  --   |game3 - game0| ≤ |game0 - game1| + |game1 - game2| + |game2 - game3|
  -- Substituting the three hop bounds gives the result.
  unfold AEADScheme.distAdvantage
  rw [← game3_eq_rand se prf adv, ← game0_eq_real se prf adv]
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
