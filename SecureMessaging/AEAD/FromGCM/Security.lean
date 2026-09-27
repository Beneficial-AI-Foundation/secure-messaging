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
# GCM: security

Entry point for the security of the one-time GCM AEAD `gcmOneTimeAEAD prp iv L hL`
(`AEAD/FromGCM/Construction.lean`): NIST SP 800-38D GCM-AE at a fixed public 96-bit IV, one
message per key, with the block cipher abstracted as a `PRPScheme K (BitVec 128)`.

## Main result

`gcmOneTimeAEAD_security`, whose only assumption is the pseudorandom-permutation (PRP) security
of the block cipher:

```text
Adv^{ot-cca-ror}(A) ≤ Adv^{prp}(B) + (n + 2)(n + 1) / 2¹²⁹ + q_d · maxBlocks L / 2¹²⁸
                                     └─────────┬─────────┘   └──────────┬───────────┘
                                    PRP/PRF switching bound       forgery bound
```

The forgery bound caps the probability that some decryption query other than the challenge
would pass tag verification in the always-reject game `game3` (see the game chain below).
`maxBlocks L` bounds the degree of the GHASH polynomial by the number of blocks GCM feeds to
GHASH (`gcmEncode`):

```text
[ zero-padded AAD ] ‖ [ zero-padded ciphertext ] ‖ [ len(AAD)₆₄ ‖ len(C)₆₄ ]
   ≤ 2⁵⁷ blocks                n blocks                     1 block
```

AAD is byte-aligned and at most `2⁶⁴ − 1` bits, hence at most `2⁶⁴ − 8` bits, which pad to at
most `⌈(2⁶⁴ − 8)/128⌉ = 2⁵⁷` blocks (`lenAMax_blocks`). The `L`-bit ciphertext pads to
`n = ⌈L/128⌉` blocks.

The symbols are listed under Notation below. The proof combines three results, each proved in
the files named above it:

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
is dead: a live decryption returns `e.1 ⊕ ks` and leaks the keystream.

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
| `B` | `prfReduction iv L adv`, the adversary against `prp` built from `A` |
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
- The decrypt oracle rejects the challenge ciphertext under *any* associated data (ACD19), so
  AAD-substitution resistance for the challenge ciphertext is not claimed.
- The forgery bound charges every decryption query, before or after the challenge, at the
  maximum AAD length, so it does not improve when shorter AAD is used.

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

/-- **One-time IND-CCA security of GCM, for any AXU bound.** Let

- `gcmOneTimeAEAD prp iv L hL` be GCM with block cipher `prp`, 96-bit IV `iv` and `L`-bit
  messages, whose GHASH is `ε`-AXU on encoded (AAD, `L`-bit message) pairs for a finite `ε`
  (`ε ≠ ⊤`, where `⊤ = ∞` in `ℝ≥0∞`), and
- `adv` be a one-time IND-CCA adversary against it making at most `q_d` decryption queries.

Then

```text
Adv^{ot-cca-ror}(adv) ≤ Adv^{prf}(B) + q_d · ε
```

where `B` (`reduction`) is the adversary `prfReduction iv L adv` against `prp`. The first term
is the PRF advantage of `B`. The second, `forgeryBound`, bounds the probability that a
decryption query forges a valid tag. `gcmOneTimeAEAD_security` uses it at
`ε = maxBlocks L / 2¹²⁸`.

The hypothesis `ε ≠ ⊤` is necessary: `GhashIsAXU L ⊤` holds trivially and `(⊤).toReal = 0`, so
without it the bound would reduce to `Adv^{ot-cca-ror}(adv) ≤ Adv^{prf}(B)`, which is false in
general. -/
-- ANCHOR: gcmOneTimeAEAD_security_of_axu
theorem gcmOneTimeAEAD_security_of_axu (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d)
    {ε : ℝ≥0∞} (hε : ε ≠ ⊤) (haxu : GhashIsAXU L ε) :
    let reduction := prfReduction iv L adv
    let forgeryBound : ℝ := (q_d : ℝ) * ε.toReal
    AEADScheme.distAdvantage (gcmOneTimeAEAD prp iv L hL) adv ≤
      PRFScheme.prfAdvantage prp.toPRFScheme reduction + forgeryBound
-- ANCHOR_END: gcmOneTimeAEAD_security_of_axu
  := by
  dsimp only
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

/-- **One-time IND-CCA security of GCM.** Let

- `gcmOneTimeAEAD prp iv L hL` be GCM with block cipher `prp`, 96-bit IV `iv` and `L`-bit
  messages, and
- `adv` be a one-time IND-CCA adversary against it making at most `q_d` decryption queries.

Then

```text
Adv^{ot-cca-ror}(adv) ≤ Adv^{prp}(B) + (n + 2)(n + 1) / 2¹²⁹ + q_d · (2⁵⁷ + n + 1) / 2¹²⁸
```

where `B` (`reduction`) is the adversary `prfReduction iv L adv` against `prp`, and
`n = ⌈L/128⌉` (`blocks`) is the number of message blocks. The first term is the PRP advantage
of `B`. The second, `switchingBound`, is the cost of replacing the random permutation by a
random function. The third, `forgeryBound`, bounds the probability that a decryption query
forges a valid tag; its `2⁵⁷ + n + 1` is `maxBlocks L`. -/
-- ANCHOR: gcmOneTimeAEAD_security
theorem gcmOneTimeAEAD_security (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d) :
    let blocks : ℕ := (L + 127) / 128
    let reduction := prfReduction iv L adv
    let switchingBound : ℝ := ((blocks : ℝ) + 2) * ((blocks : ℝ) + 1) / 2 ^ 129
    let forgeryBound : ℝ := (q_d : ℝ) * ((2 ^ 57 + (blocks : ℝ) + 1) / 2 ^ 128)
    AEADScheme.distAdvantage (gcmOneTimeAEAD prp iv L hL) adv ≤
      PRPScheme.prpAdvantage prp reduction + switchingBound + forgeryBound
-- ANCHOR_END: gcmOneTimeAEAD_security
  := by
  dsimp only
  have hmax : (maxBlocks L : ℝ) = 2 ^ 57 + (((L + 127) / 128 : ℕ) : ℝ) + 1 := by
    simp only [maxBlocks, lenAMax_blocks]
    push_cast
    ring
  have hprf := gcmOneTimeAEAD_security_of_axu prp iv L hL adv q_d hq
    (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity))
    (ghash_isAXU_unconditional L)
  dsimp only at hprf
  rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat, hmax] at hprf
  have hswitch := prfAdvantage_le_prpAdvantage_switching prp iv L hL adv
  linarith

end GCM
