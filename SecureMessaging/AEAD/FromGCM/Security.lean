/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Security.PrfHop
import SecureMessaging.AEAD.FromGCM.Security.AuthHop
import SecureMessaging.AEAD.FromGCM.Security.PrivacyHop
import SecureMessaging.AEAD.FromGCM.Security.NistIrreducible
import SecureMessaging.AEAD.FromGCM.Security.PrpSwitch

/-!
# GCM — Security

Entry point for the security of the one-time GCM AEAD `gcmOneTimeAEAD prp iv L hL`
(`AEAD/FromGCM/Construction.lean`): NIST SP 800-38D GCM-AE at a fixed public 96-bit IV, one
message per key, with the block cipher abstracted as a `PRPScheme K (BitVec 128)`.

## Main result

`gcmOneTimeAEAD_security`, whose only assumption is the pseudorandom-permutation (PRP) security
of the block cipher:

  `Adv^{ot-cca-ror}(A) ≤ Adv^{prp}(B) + (n + 2)(n + 1) / 2¹²⁹ + q_d · maxBlocks L / 2¹²⁸`

Its docstring defines the terms. The proof combines three results, each proved in the files
named above it:

```text
 Games, PrfHop,                  GhashAXU,                   PrpSwitch
 AuthHop, PrivacyHop             NistIrreducible
        │                               │                           │
        ▼                               ▼                           ▼
 gcmOneTimeAEAD_security_of_axu  ghash_isAXU_unconditional   prfAdvantage_le_prpAdvantage_switching
 Adv ≤ Adv^{prf}(B) + q_d · ε    GHASH is AXU with           Adv^{prf}(B) ≤ Adv^{prp}(B)
 for any AXU bound ε             ε = maxBlocks L / 2¹²⁸                     + (n + 2)(n + 1) / 2¹²⁹
        │                               │                           │
        └───────────────────────────────┼───────────────────────────┘
                                        ▼
                             gcmOneTimeAEAD_security
```

The AXU bound needs the GCM polynomial `x¹²⁸ + x⁷ + x² + x + 1` to be irreducible. That is
proved, not assumed: `nistPoly_irreducible` checks Rabin's test by kernel computation.

## Game chain

The advantage compares two experiments (ACD19, Fig. 1). In the real one, encryption returns
`Enc_k(a, m)` and decryption returns `Dec_k(a, e)`, except on the challenge ciphertext. In the
ideal one, encryption returns a uniform `(c, t) ∈ C` and decryption always returns `⊥`. The
proof walks five games `game0 … game4` (`Security/Games.lean`) from the real experiment to the
ideal one, so `Adv^{ot-cca-ror}(A) = |Pr[game4 = 1] − Pr[game0 = 1]|`. Rows are games, which
differ only in the three columns. Each arrow says what the hop changes and what it costs:

```text
        block-cipher outputs    encrypt oracle       decrypt oracle    hop cost
        ────────────────────    ──────────────       ──────────────    ────────
game0   perm k at k ← keygen    (m ^^^ ks, tag)      verify, unmask
  │
  │   replace perm k by a uniform tuple (H, mask, ks)                  Adv^{prf}    (1)
  ▼
game1   uniform, up front       (m ^^^ ks, tag)      verify, unmask
  │
  │   sample the tuple at the first query (greedyLazy)                 0            (2)
  ▼
game2   uniform, 1st query      (m ^^^ ks, tag)      verify, unmask
  │
  │   reject every decryption, sample at encrypt (consumeLazy)         q_d · ε      (3)
  ▼
game3   uniform, at encrypt     (m ^^^ ks, tag)      ⊥
  │
  │   replace the challenge by a uniform one                           0            (4)
  ▼
game4   unused                  (c, t) ←$ C          ⊥

tag = GHASH_H(ad, c) ^^^ mask;  C = BitVec L × BitVec 128;  ε = GHASH's AXU bound
in every game: one encryption, and decrypting the challenge ciphertext returns ⊥
(1) game0_game1_le_prf   (2) game1_eq_game2   (3) game2_game3_le_auth   (4) game3_eq_game4
game0 = real experiment (game0_eq_real), game4 = ideal experiment (game4_eq_rand)
```

Hops (2) and (4) are exact, so only the PRF and authenticity terms survive. This is
`gcmOneTimeAEAD_security_of_axu`, with the almost-XOR-universality (AXU) of GHASH as a
hypothesis `GhashIsAXU L ε`.

The hop order is forced. Hop (4) forgets the cached tuple, which is sound only once decryption
is dead: a live decryption returns `e.1 ^^^ ks` and leaks the keystream.

There is no separate `2⁻¹²⁸` tag-guessing term. `ghashAXU_eps_lower` (`Security/Axu.lean`)
shows `2⁻¹²⁸ ≤ ε` for every witnessing `ε`, so a blind guess is already covered by the AXU
bound.

## Notation

| Symbol | Meaning |
|---|---|
| `prp` | the underlying block cipher, a `PRPScheme K (BitVec 128)` (AES in practice) |
| `iv` | the scheme's fixed public 96-bit IV; `J₀ = j0 iv = iv ‖ 0³¹ ‖ 1` |
| `L` / `hL` | the fixed message length in bits, and `ValidMsgLength L` (`AEAD/GCM.lean`) |
| `n` | `numBlocks L = ⌈L/128⌉`, the number of message blocks |
| `A` (`adv`) | the one-time IND-CCA adversary, an `OneTimeCCAAdversary` |
| `q_d` | upper bound on `A`'s number of decryption queries (`decryptQueryBound`) |
| `maxBlocks L` | `2⁵⁷ + n + 1`, the GHASH degree bound (`Security/Encoding.lean`) |
| `Adv^{ot-cca-ror}` | one-time IND-CCA (real-or-random) advantage, `AEADScheme.distAdvantage` |
| `Adv^{prf}` / `Adv^{prp}` | `PRFScheme.prfAdvantage` / `PRPScheme.prpAdvantage` |

## Scope

- The IV is 96 bits, fixed at construction time, public, and must be independent of the key. Its
  value is arbitrary: every theorem is quantified over `iv`, since `J₀ = iv ‖ 0³¹ ‖ 1` keeps the
  counter blocks away from the GHASH-key input `0¹²⁸` whatever `iv` is
  (`cipherInputs_pairwise_ne`). The non-96-bit GHASH-the-IV path of SP 800-38D is out of scope.
- The message length `L` is fixed and satisfies `ValidMsgLength L` (`L ≤ 2³⁹ − 256` bits and
  `8 ∣ L`), which keeps the GCTR counter from wrapping.
- The tag is the full 128 bits.
- One encryption per key; key non-reuse across invocations is the caller's responsibility.
- Adversaries are failure-free by type (`OracleComp` has only `pure` and `queryBind`). This
  loses nothing: `distAdvantage` compares probabilities of the output `true`, on which aborting
  mass never lands, so replacing every `failure` by `pure false` leaves the advantage unchanged.
- The decrypt oracle rejects the challenge ciphertext under *any* associated data (ACD19), so
  AAD-substitution resistance for the challenge ciphertext is not claimed.
- The forgery bound uses the worst-case AAD length. A post-challenge decryption query forges
  only if `H` is a root of the difference of its GHASH polynomial and the challenge's, whose
  degree is governed by the *longer* of the two encodings: `max(⌈a/128⌉, ⌈a*/128⌉) + n + 1` for
  a query with `a` AAD bits against a challenge with `a*`. A pre-challenge query can only guess
  the tag mask, with probability `2⁻¹²⁸ ≤ ε`, so both kinds are charged `ε`. The theorem
  replaces both AAD lengths by the maximum `2⁵⁷` (`lenAMax_blocks`), which is where
  `maxBlocks L = 2⁵⁷ + n + 1` comes from. So the bound holds whatever AAD lengths are used, but
  overcounts whenever both are shorter than the maximum.

## Paper references

- **NIST SP 800-38D**: the specification of GCM; `gcmOneTimeAEAD` is its §7 GCM-AE at a 96-bit
  IV, and `GhashIsAXU` is the universality of its §6.4 GHASH.
- **ACD19** (Alwen–Coretti–Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization*): the notion targeted here, formalised in `AEAD/Defs.lean`.
- **McGrew–Viega**, *The Security and Performance of the Galois/Counter Mode of Operation*: the
  original GCM security proof, whose shape the game chain follows.
- **Iwata–Ohashi–Minematsu**, *Breaking and Repairing GCM Security Proofs*: the original proof
  is flawed in bounding counter collisions between GHASHed nonces. Their attack needs a
  non-96-bit IV and does not apply to a fixed 96-bit IV, whose counter blocks are distinct by
  construction; their repaired bounds are tighter in that case.
- **Bellare–Rogaway**, *Code-Based Game-Playing Proofs and the Security of Triple Encryption*:
  the PRP/PRF switching lemma.

## Reading order

1. This file: the game chain for an abstract AXU bound, and the main result.
2. `Security/Games.lean`, `Security/PrfHop.lean`, `Security/AuthHop.lean` and
   `Security/PrivacyHop.lean`: the games and the three hops (supporting: `Encoding`, `Axu`,
   `Counter`, `CipherProfile`).
3. `Security/GhashPolynomial.lean`, `Security/GhashAXU.lean`, `Security/NistIrreducible.lean`: the
   GHASH AXU bound and the irreducibility of `nistPoly`.
4. `Security/PrpSwitch.lean`: the PRP/PRF switching inequality at `prfReduction`.

Generic, scheme-independent lemmas live under `ToVCVio/`.
-/

namespace GCM

open OracleSpec OracleComp ENNReal AEADScheme ToVCVio

variable {K : Type}

/-! ## The game chain, for any AXU bound -/

/-- Assembles the game chain of the module doc for any AXU bound `ε` of GHASH:
`Adv^{ot-cca-ror}(adv) ≤ Adv^{prf}(B) + q_d · ε` with `B = prfReduction iv L adv`.
`gcmOneTimeAEAD_security` uses it at `ε = maxBlocks L / 2¹²⁸`.

`hε : ε ≠ ⊤` is necessary: the bound is read in `ℝ` via `ε.toReal`, and `(⊤ : ℝ≥0∞).toReal = 0`
would make the conclusion false at the trivially true `GhashIsAXU L ⊤`. -/
-- ANCHOR: gcmOneTimeAEAD_security_of_axu
theorem gcmOneTimeAEAD_security_of_axu (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d)
    {ε : ℝ≥0∞} (hε : ε ≠ ⊤) (haxu : GhashIsAXU L ε) :
    AEADScheme.distAdvantage (gcmOneTimeAEAD prp iv L hL) adv ≤
      PRFScheme.prfAdvantage prp.toPRFScheme (prfReduction iv L adv) +
      (q_d : ℝ) * ε.toReal
-- ANCHOR_END: gcmOneTimeAEAD_security_of_axu
  := by
  have hg12 : Pr[= true | game1 prp L hL adv] = Pr[= true | game2 prp L hL adv] :=
    probOutput_eq_of_evalDist_eq (game1_eq_game2 prp L hL adv) true
  unfold AEADScheme.distAdvantage
  rw [← game4_eq_rand prp iv L hL adv, ← game0_eq_real prp iv L hL adv,
    ← probOutput_game3_eq_game4 prp L hL adv]
  calc |(Pr[= true | game3 prp L hL adv]).toReal -
        (Pr[= true | game0 prp iv L hL adv]).toReal|
    _ ≤ |(Pr[= true | game1 prp L hL adv]).toReal -
         (Pr[= true | game0 prp iv L hL adv]).toReal| +
        |(Pr[= true | game3 prp L hL adv]).toReal -
         (Pr[= true | game2 prp L hL adv]).toReal| := by
          rw [hg12]
          set g0 := (Pr[= true | game0 prp iv L hL adv]).toReal
          set g2 := (Pr[= true | game2 prp L hL adv]).toReal
          set g3 := (Pr[= true | game3 prp L hL adv]).toReal
          linarith [abs_sub_le g3 g2 g0]
    _ ≤ PRFScheme.prfAdvantage prp.toPRFScheme (prfReduction iv L adv) +
        (q_d : ℝ) * ε.toReal :=
      add_le_add (game0_game1_le_prf prp iv L hL adv)
        (game2_game3_le_auth prp L hL adv q_d hq hε haxu)

/-! ## Main result -/

/-- **One-time IND-CCA security of GCM.** Let `adv` be an adversary against GCM with block
cipher `prp`, 96-bit IV `iv` and `L`-bit messages, making at most `q_d` decryption queries. Its
advantage is at most

  `Adv^{prp}(B) + (n + 2)(n + 1) / 2¹²⁹ + q_d · maxBlocks L / 2¹²⁸`

where `B = prfReduction iv L adv` is an adversary against `prp`, `n = numBlocks L` is the
number of message blocks and `maxBlocks L = 2⁵⁷ + n + 1`. The first term is the PRP advantage
of `B`, the second the cost of replacing the random permutation by a random function, and the
third bounds the probability that a decryption query forges a valid tag. -/
-- ANCHOR: gcmOneTimeAEAD_security
theorem gcmOneTimeAEAD_security (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d) :
    AEADScheme.distAdvantage (gcmOneTimeAEAD prp iv L hL) adv ≤
      PRPScheme.prpAdvantage prp (prfReduction iv L adv) +
      ((numBlocks L : ℝ) + 2) * ((numBlocks L : ℝ) + 1) / 2 ^ 129 +
      (q_d : ℝ) * ((maxBlocks L : ℝ) / 2 ^ 128)
-- ANCHOR_END: gcmOneTimeAEAD_security
  := by
  have hprf := gcmOneTimeAEAD_security_of_axu prp iv L hL adv q_d hq
    (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity))
    (ghash_isAXU_unconditional L)
  rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat] at hprf
  have hswitch := prfAdvantage_le_prpAdvantage_switching prp iv L hL adv
  unfold numBlocks
  linarith

end GCM
