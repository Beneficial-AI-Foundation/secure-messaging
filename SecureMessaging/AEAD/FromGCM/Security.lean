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

`gcmOneTimeAEAD_security`, with `n = ⌈L/128⌉` and the pseudorandom-permutation (PRP)
security of the block cipher as its only assumption:

  `Adv^{ot-cca-ror}(A) ≤ Adv^{prp}(B) + (n + 2)(n + 1) / 2¹²⁹ + q_d · maxBlocks L / 2¹²⁸`

* `B = prfReduction iv L A` (`Security/PrfHop.lean`) is the explicit reduction. It queries the
  block cipher at the `n + 2` fixed points one GCM encryption uses (the GHASH key, the tag mask,
  one keystream block per message block), whatever `A` does.
* `(n + 2)(n + 1) / 2¹²⁹` is the PRP/PRF switching term, a birthday bound in those `n + 2` calls
  (`Security/PrpSwitch.lean`).
* `q_d · maxBlocks L / 2¹²⁸` bounds the forgery probability: each decryption query forges with
  probability at most `maxBlocks L / 2¹²⁸`, the GHASH polynomial's degree over the tag-field
  size (`Security/GhashAXU.lean`), and there are at most `q_d` such queries.

The GHASH bound counts roots of a nonzero polynomial over `𝔽₂[x]/(nistPoly)`, which is a field
because the GCM polynomial `x¹²⁸ + x⁷ + x² + x + 1` is irreducible. That fact is a theorem here,
not a hypothesis: `nistPoly_irreducible` (`Security/NistIrreducible.lean`) proves it by Rabin's
test with the two conditions checked by kernel computation.

## Game chain

The proof walks five games `game0 … game4` (`Security/Games.lean`), `game0` the real one-time
IND-CCA experiment and `game4` the ideal one, so
`Adv^{ot-cca-ror}(A) = |Pr[game4 = 1] − Pr[game0 = 1]|`. Each hop changes one component:

```text
        block-cipher source          encrypt oracle        decrypt oracle
        ───────────────────          ──────────────        ──────────────
game0   real `perm k`                c = m ^^^ ks          verify tag, then unmask
  │                            Adv^{prf}   (game0_game1_le_prf)
  ▼   replace `perm k` by one uniform tuple `(H, mask, ks)` drawn at the top level
game1   uniform tuple, eager         c = m ^^^ ks          verify tag, then unmask
  │                            0           (game1_eq_game2)
  ▼   move the tuple draw inside the oracles (`greedyLazy`); same distribution
game2   uniform tuple, lazy          c = m ^^^ ks          verify tag, then unmask
  │                            q_d · ε     (game2_game3_le_auth)
  ▼   suppress decryption: each forgery needs a fresh GHASH collision, w.p. ≤ ε
game3   tuple drawn at `OEncrypt`    c = m ^^^ ks          ⊥ (always reject)
  │                            0           (game3_eq_game4)
  ▼   replace the real challenge by a uniform one; exactly equidistributed
game4   the tuple draw is dead       (c, t) ←$ C           ⊥ (always reject)

  game0 = the real ACD19 experiment                  (game0_eq_real)
  game4 = the ideal one ($ ciphertext, ⊥ decrypt)    (game4_eq_rand)
```

Two hops are exact distribution equalities, so after the triangle inequality only the PRF and
the authenticity summands survive. `gcmOneTimeAEAD_security_of_axu` below assembles the chain
with the almost-XOR-universality (AXU) of GHASH as a hypothesis `GhashIsAXU L ε`; the theorems
after it discharge that hypothesis and trade the PRF advantage for the PRP one.

There is no separate `2⁻¹²⁸` tag-guessing term: a blind guess succeeds with probability exactly
`2⁻¹²⁸`, and `ghashAXU_eps_lower` (`Security/Axu.lean`) shows `2⁻¹²⁸ ≤ ε` for every witnessing
`ε`, so guessing is already inside the AXU bound.

The hop order is forced: the privacy hop forgets the cached tuple, which is sound only once
decryption is dead, since a live decryption returns `e.1 ^^^ ks` and leaks the keystream.

Adversaries are failure-free by type (`OracleComp` has only `pure` and `queryBind`), and this
loses nothing: `distAdvantage` compares probabilities of the output `true`, on which aborting
mass never lands, so replacing every `failure` by `pure false` leaves the advantage unchanged.

Games and the reduction are instantiations of one oracle-spec-polymorphic skeleton
(`gcmGameSkeleton`, `Security/Games.lean`); the lazy-sampling caches carried by `game2`/`game3`
are proof artifacts, invisible to the adversary.

## Notation

| Symbol | Meaning |
|---|---|
| `prp` | the underlying block cipher, a `PRPScheme K (BitVec 128)` (AES in practice) |
| `iv` | the scheme's fixed public 96-bit IV; `J₀ = j0 iv = iv ‖ 0³¹ ‖ 1` |
| `L` / `hL` | the fixed message length in bits, and `ValidMsgLength L` (`AEAD/GCM.lean`) |
| `n` | `⌈L/128⌉ = (L + 127) / 128`, the number of message blocks |
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
- The decrypt oracle rejects the challenge ciphertext under *any* associated data (ACD19), so
  AAD-substitution resistance for the challenge ciphertext is not claimed.
- The forgery bound uses the worst-case AAD length. A query with `a` AAD bits forges with
  probability at most `(⌈a/128⌉ + n + 1) / 2¹²⁸`; the theorem replaces `⌈a/128⌉` by its maximum
  `2⁵⁷` (`lenAMax_blocks`) for every query, which is where `maxBlocks L = 2⁵⁷ + n + 1` comes
  from. So the bound holds whatever AAD lengths the adversary uses, but overcounts every
  query whose AAD is shorter than the maximum.

## Paper references

- **NIST SP 800-38D**: the specification of GCM; `gcmOneTimeAEAD` is its §7 GCM-AE at a 96-bit
  IV, and `GhashIsAXU` is the universality of its §6.4 GHASH.
- **ACD19** (Alwen–Coretti–Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization*): the notion targeted here, formalised in `AEAD/Defs.lean`.
- **McGrew–Viega**, *The Security and Performance of the Galois/Counter Mode of Operation*: the
  original GCM security proof, whose shape the game chain follows.
- **Iwata–Ohashi–Minematsu**, *Breaking and Repairing GCM Security Proofs*: their attack concerns
  the non-96-bit-IV path, where the IV itself is GHASHed; the 96-bit IV fixed here is the regime
  their repair leaves intact.
- **Bellare–Rogaway**, *Code-Based Game-Playing Proofs and the Security of Triple Encryption*:
  the PRP/PRF switching lemma.

## Reading order

1. This file: the assembled reduction and the hypothesis-free statements.
2. `Security/Games.lean`, `Security/PrfHop.lean`, `Security/AuthHop.lean` and
   `Security/PrivacyHop.lean`: the games and the three hops (supporting: `Encoding`, `Axu`,
   `Counter`, `CipherProfile`, `OneTimePad`).
3. `Security/Polynomial.lean`, `Security/GhashAXU.lean`, `Security/NistIrreducible.lean`: the
   GHASH AXU bound and the irreducibility of `nistPoly`.
4. `Security/PrpSwitch.lean`: the PRP/PRF switching inequality at `prfReduction`.

Generic, scheme-independent lemmas live under `ToVCVio/`.
-/

namespace GCM

open OracleSpec OracleComp ENNReal AEADScheme ToVCVio

variable {K : Type}

/-! ## The general reduction -/

/-- **GCM one-time IND-CCA security**, with the AXU parameter `ε` of GHASH left as a hypothesis:

  `Adv^{ot-cca-ror}_{GCM}(A) ≤ Adv^{prf}(B) + q_d · ε`

for the explicit distinguisher `B = prfReduction iv L adv`. No upper bound on `ε` is assumed; it
is instantiated downstream (`gcmOneTimeAEAD_security_maxBlocks`).

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

/-! ## The concrete constant -/

theorem one_le_maxBlocks (L : ℕ) : 1 ≤ maxBlocks L := by
  unfold maxBlocks; omega

theorem maxBlocks_lt_two_pow (L : ℕ) (hL : ValidMsgLength L) : maxBlocks L < 2 ^ 128 := by
  have h := hL.1
  unfold maxBlocks
  rw [lenAMax_blocks]
  have : (L + 127) / 128 ≤ (2 ^ 39 - 256 + 127) / 128 := Nat.div_le_div_right (by omega)
  norm_num at this ⊢
  omega

/-- The concrete AXU constant sits between the blind-guess floor and `1`. The upper half needs
`ValidMsgLength L`, since `maxBlocks L` grows with `L`. A sanity check that the bound is not
vacuous; the main theorem does not use it. -/
theorem maxBlocks_div_nontrivial (L : ℕ) (hL : ValidMsgLength L) :
    ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ ≤ (maxBlocks L : ℝ≥0∞) / 2 ^ (128 : ℕ) ∧
      (maxBlocks L : ℝ≥0∞) / 2 ^ (128 : ℕ) < 1 := by
  refine ⟨?_, ?_⟩
  · rw [← one_div]
    exact ENNReal.div_le_div_right (by exact_mod_cast one_le_maxBlocks L) _
  · rw [ENNReal.div_lt_iff (Or.inl (by positivity)) (Or.inl (by simp)), one_mul]
    exact_mod_cast maxBlocks_lt_two_pow L hL

/-- `gcmOneTimeAEAD_security_of_axu` at `ε := maxBlocks L / 2¹²⁸`: `maxBlocks L` bounds the
degree of the GHASH polynomial and `2¹²⁸` is the size of the tag field. `haxu` is discharged by
`ghash_isAXU` (`Security/GhashAXU.lean`). The exponent is spelled `2 ^ (128 : ℕ)` so that the
`ℝ≥0∞` numeral matches `ghashAXU_eps_lower`. -/
theorem gcmOneTimeAEAD_security_maxBlocks (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96)
    (L : ℕ) (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d)
    (haxu : GhashIsAXU L ((maxBlocks L : ℝ≥0∞) / 2 ^ (128 : ℕ))) :
    AEADScheme.distAdvantage (gcmOneTimeAEAD prp iv L hL) adv ≤
      PRFScheme.prfAdvantage prp.toPRFScheme (prfReduction iv L adv) +
      (q_d : ℝ) * ((maxBlocks L : ℝ) / 2 ^ (128 : ℕ)) := by
  have h := gcmOneTimeAEAD_security_of_axu prp iv L hL adv q_d hq
    (ε := (maxBlocks L : ℝ≥0∞) / 2 ^ (128 : ℕ))
    (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)) haxu
  rwa [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat] at h

/-! ## The concrete bound, up to irreducibility -/

/-- `gcmOneTimeAEAD_security_maxBlocks` with its AXU hypothesis discharged by `ghash_isAXU`
(`Security/GhashAXU.lean`), which is where irreducibility of `nistPoly` enters. -/
theorem gcmOneTimeAEAD_security_maxBlocks_of_irreducible (prp : PRPScheme K (BitVec 128))
    (iv : BitVec 96) (L : ℕ) (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d)
    (hirr : Irreducible nistPoly) :
    AEADScheme.distAdvantage (gcmOneTimeAEAD prp iv L hL) adv ≤
      PRFScheme.prfAdvantage prp.toPRFScheme (prfReduction iv L adv) +
      (q_d : ℝ) * ((maxBlocks L : ℝ) / 2 ^ (128 : ℕ)) :=
  gcmOneTimeAEAD_security_maxBlocks prp iv L hL adv q_d hq (ghash_isAXU L hirr)

/-! ## The PRF-stated bound -/

/-- The PRF-stated bound with no hypothesis: `gcmOneTimeAEAD_security_maxBlocks_of_irreducible` at
`nistPoly_irreducible` (`Security/NistIrreducible.lean`). -/
-- ANCHOR: gcmOneTimeAEAD_security_prf
theorem gcmOneTimeAEAD_security_prf (prp : PRPScheme K (BitVec 128))
    (iv : BitVec 96) (L : ℕ) (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d) :
    AEADScheme.distAdvantage (gcmOneTimeAEAD prp iv L hL) adv ≤
      PRFScheme.prfAdvantage prp.toPRFScheme (prfReduction iv L adv) +
      (q_d : ℝ) * ((maxBlocks L : ℝ) / 2 ^ (128 : ℕ))
-- ANCHOR_END: gcmOneTimeAEAD_security_prf
  :=
  gcmOneTimeAEAD_security_maxBlocks prp iv L hL adv q_d hq (ghash_isAXU_unconditional L)

/-! ## The PRP-stated bound -/

/-- The main result: one-time IND-CCA security of GCM from the PRP security of the block cipher.
The PRF summand of `gcmOneTimeAEAD_security_prf` is traded for the PRP advantage of the same
reduction plus the switching term `(n + 2)(n + 1) / 2¹²⁹`, `n = ⌈L/128⌉`
(`prfAdvantage_le_prpAdvantage_switching`, `Security/PrpSwitch.lean`). -/
-- ANCHOR: gcmOneTimeAEAD_security
theorem gcmOneTimeAEAD_security (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d) :
    AEADScheme.distAdvantage (gcmOneTimeAEAD prp iv L hL) adv ≤
      PRPScheme.prpAdvantage prp (prfReduction iv L adv) +
      ((((L + 127) / 128 : ℕ) : ℝ) + 2) * ((((L + 127) / 128 : ℕ) : ℝ) + 1)
        / 2 ^ (129 : ℕ) +
      (q_d : ℝ) * ((maxBlocks L : ℝ) / 2 ^ (128 : ℕ))
-- ANCHOR_END: gcmOneTimeAEAD_security
  := by
  refine le_trans (gcmOneTimeAEAD_security_prf prp iv L hL adv q_d hq) ?_
  have h := prfAdvantage_le_prpAdvantage_switching prp iv L hL adv
  linarith

end GCM
