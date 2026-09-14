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

Entry point for the security of the one-time GCM AEAD `gcmOneTimeAEAD prp L hL`
(`AEAD/FromGCM/Construction.lean`): NIST SP 800-38D GCM-AE at the all-zero 96-bit IV, one message
per key, with the block cipher abstracted as a `PRPScheme K (BitVec 128)`.

## Main result

`gcmOneTimeAEAD_security`, with `n = ⌈L/128⌉` and the PRP security of the block cipher as its
only assumption:

  `Adv^{ot-cca-ror}(A) ≤ Adv^{prp}(B) + (n + 2)(n + 1) / 2¹²⁹ + q_d · maxBlocks L / 2¹²⁸`

* `B = prfReduction L A` (`Security/PrfHop.lean`) is the explicit reduction. It queries its
  function oracle on the fixed list `0 :: 1 :: counterChain 2 n` (the GHASH key, the tag mask,
  one keystream block per message block), independently of how many queries `A` makes.
* `(n + 2)(n + 1) / 2¹²⁹` is the PRP/PRF switching term, a birthday bound in the `n + 2`
  block-cipher calls of one encryption (`Security/PrpSwitch.lean`).
* `q_d · maxBlocks L / 2¹²⁸` charges one almost-XOR-universality term per decryption query of
  `A`, whose number `q_d` bounds (`AEADScheme.decryptQueryBound`); `maxBlocks L` bounds the
  degree of the GHASH polynomial and `2¹²⁸` is the size of the tag field
  (`Security/GhashAXU.lean`).

The only algebraic input is irreducibility of the GCM field polynomial `x¹²⁸ + x⁷ + x² + x + 1`
(`nistPoly_irreducible`, `Security/NistIrreducible.lean`), used by the GHASH bound and nowhere
else.

## Game chain

`Adv^{ot-cca-ror}(A) = |Pr[game4 = 1] − Pr[game0 = 1]|` for five games `game0 … game4`
(`Security/Games.lean`), `game0` real and `game4` ideal. The PRF hop `game0 → game1` costs
`Adv^{prf}(B)` and the Wegman–Carter authenticity hop `game2 → game3` costs `q_d · ε`; lazy
sampling of the cipher outputs (`game1 → game2`) and the one-time-pad privacy hop
(`game3 → game4`) are exact distribution equalities. `gcmOneTimeAEAD_security_of_axu` below
assembles the chain.

## The reduction

One explicit reduction witnesses the bound: `prfReduction L A` (`Security/PrfHop.lean`), used for
the `game0 → game1` hop, where it charges `Adv^{prf}`. It is an instantiation of the shared game
skeleton at the PRF oracle spec. It fetches its function oracle eagerly, at exactly the cipher
inputs of one-time GCM at the all-zero IV, and then runs `A` against the resulting closed tuple
game, so its query list is the fixed list `0 :: 1 :: counterChain 2 ⌈L/128⌉`, of length
`⌈L/128⌉ + 2`, whatever `A` does. That constant is what the PRP/PRF switching lemma consumes.

## Game hops

The proof walks a sequence of five games `game0 … game4` (`Security/Games.lean`). `game0` is the
real one-time IND-CCA experiment and `game4` is the ideal one, so
`Adv^{ot-cca-ror}(A) = |Pr[game4 = 1] − Pr[game0 = 1]|`. Each hop changes exactly one component:

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

Two of the four hops are exact `evalDist` equalities, costing `0`, so after the triangle
inequality only two `|·|` summands survive, one for the PRF hop and one for the authenticity hop.
`probOutput_game3_eq_game4` (`Security/PrivacyHop.lean`) is stated at `Pr[= true | ·]`, matching
the level of `game0_eq_real` and `game4_eq_rand`, so the assembly below needs a single adapter:
one `ToVCVio.probOutput_eq_of_evalDist_eq` for `game1_eq_game2`, which is stated at `evalDist`.

Decryption dies at the `game2 → game3` hop (`game2_game3_le_auth`, `Security/AuthHop.lean`),
which is where the whole authenticity argument is charged. The price is `q_d · ε`: one AXU term
per decryption query, and nothing else. In particular there is no separate `2⁻¹²⁸` tag-guessing
term. A blind pre-challenge guess succeeds with probability exactly `2⁻¹²⁸`, and
`ghashAXU_eps_lower` (`Security/Axu.lean`) shows `2⁻¹²⁸ ≤ ε` for every witnessing `ε`, so the
guessing case is already inside the AXU bound.

## How the proof is organised

Facts about the proof, each with its justification. They are not restrictions on the result; for
those see `## Scope` below.

1. Hop order is load-bearing. The privacy hop's state relation `gcmPrivacyRel`
   (`Security/PrivacyHop.lean`) forgets the cached tuple value, which is sound only because
   decryption is already dead in `game3`. Against `gcmTupleImpl`'s live decrypt, which returns
   `e.1 ^^^ ks` and so leaks the keystream pad, the same forgetting is unsound. So the privacy
   hop is available only after the authenticity hop has suppressed decryption; the order
   `game2 → game3 → game4` is forced, not stylistic.

2. Adversaries are failure-free by type, and this costs nothing.
   `OneTimeCCAAdversary AD M C` is `OracleComp (aeadOneTimeCCASpec AD M C) Bool`
   (`AEAD/Defs.lean`), and `OracleComp` is a `PFunctor.FreeM`, with only `pure` and `queryBind`;
   failure lives one level up, in `OptionT (OracleComp spec)`. This restriction is vacuous:
   `distAdvantage` is `|Pr[= true | · true] − Pr[= true | · false]|`, and aborting mass lands on
   neither `true`, so replacing every `failure` by `pure false` leaves both probabilities
   unchanged and the advantage exactly equal. An aborting adversary is therefore dominated by a
   total one. `securityExpFixedBit` takes the same type, so the notion and the adversary class
   agree by construction.

3. The lazy-sampling cache is internal. After the PRF hop the block cipher is a lazily sampled
   random oracle, and `game2`/`game3` carry a one-slot `consumeLazy`/`greedyLazy` cache in their
   state. Both are artifacts of the proof, not part of the ACD19 game: the adversary `A` still
   only ever sees the encrypt and decrypt oracles.

## Statements, from the general reduction to the final bound

Each row supplies one hypothesis of the row above; the last also trades the PRF advantage of
the block cipher for its PRP advantage.

| Theorem | Hypotheses beyond `Adv^{prf}` / `Adv^{prp}` |
|---|---|
| `gcmOneTimeAEAD_security_of_axu` | `GhashIsAXU L ε`, `ε ≠ ⊤` |
| `gcmOneTimeAEAD_security_maxBlocks` | `GhashIsAXU L (maxBlocks L / 2¹²⁸)` |
| `gcmOneTimeAEAD_security_prf` | none (PRF-stated) |
| `gcmOneTimeAEAD_security` | none (PRP-stated) |

The first two are the general reduction, valid for any almost-XOR-universal hash, and keep their
AXU hypothesis by design.

## Notation

| Symbol | Meaning |
|---|---|
| `prp` | the underlying block cipher, a `PRPScheme K (BitVec 128)` (AES in practice) |
| `L` / `hL` | the fixed message length in bits, and `ValidMsgLength L` (`AEAD/GCM.lean`) |
| `n` | `⌈L/128⌉ = (L + 127) / 128`, the number of message blocks |
| `A` (`adv`) | the one-time IND-CCA adversary, an `OneTimeCCAAdversary` |
| `q_d` | upper bound on `A`'s number of decryption queries (`decryptQueryBound`) |
| `ε` | the almost-XOR-universality parameter of GHASH (`GhashIsAXU L ε`) |
| `H` | the GHASH subkey, `perm k 0` (`Security/CipherProfile.lean`) |
| `mask` | the tag mask, `perm k 1` = `perm k J₀` at the all-zero 96-bit IV |
| `ks` | the GCTR keystream, `perm k` over `counterChain 2 ⌈L/128⌉`, packed to `BitVec L` |
| `maxBlocks L` | `2⁵⁷ + n + 1`, the GHASH degree bound (`Security/Encoding.lean`) |
| `Adv^{ot-cca-ror}` | one-time IND-CCA (real-or-random) advantage, `AEADScheme.distAdvantage` |
| `Adv^{prf}` / `Adv^{prp}` | `PRFScheme.prfAdvantage` / `PRPScheme.prpAdvantage` |

## Scope

The restrictions a citer must check:

- The IV is the all-zero 96-bit IV. Its width is fixed by the type (`BitVec 96`), so the
  non-96-bit GHASH-the-IV path of SP 800-38D is out of scope, and its value is fixed to `0`.
- The message length `L` is fixed and must satisfy `ValidMsgLength L` (`L ≤ 2³⁹ − 256` bits and
  `8 ∣ L`), which is what keeps the GCTR counter from wrapping.
- The tag is the full 128 bits. Truncated tags are not covered.
- One encryption per key. This is the one-time notion; key non-reuse across invocations is the
  caller's responsibility, outside the game.
- The challenge guard is ciphertext-only. ACD19's decrypt oracle rejects every query repeating
  the challenge ciphertext `(C*, T*)` under *any* associated data, so AAD-substitution resistance
  for the challenge ciphertext is not claimed here.
- The AXU constant is uniform in the AAD length. `maxBlocks L` charges the maximal AAD block
  count `2⁵⁷` to every decryption query, so the authenticity term is looser than a per-query
  `(ℓ_A + ℓ_C + 1) / 2¹²⁸` bound. It is correct, not tight.

## Paper references

- **NIST SP 800-38D**: the specification of GCM; `gcmOneTimeAEAD` is its §7 GCM-AE at a 96-bit
  IV, and `GhashIsAXU` is the universality of its §6.4 GHASH.
- **ACD19** (Alwen–Coretti–Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization*): the notion targeted here, formalised in `AEAD/Defs.lean`.
- **McGrew–Viega**, *The Security and Performance of the Galois/Counter Mode of Operation*: the
  original GCM security proof, whose shape the game chain follows.
- **Iwata–Ohashi–Minematsu**, *Breaking and Repairing GCM Security Proofs*: their attack concerns
  the non-96-bit-IV path of the mode term, where the IV itself is GHASHed. This development fixes
  the all-zero 96-bit IV, the clean regime their repair leaves intact.
- **Bellare–Rogaway**, *Code-Based Game-Playing Proofs and the Security of Triple Encryption*:
  the PRP/PRF switching lemma.

## NIST SP 800-38D / ACD19 correspondence

| Lean definition | Reference |
|---|---|
| `gcmOneTimeAEAD` | SP 800-38D §7 GCM-AE, at a 96-bit IV, one message per key |
| `GhashIsAXU` | §6.4 GHASH, as an almost-XOR-universal hash on `gcmEncode` outputs |
| `gcmEncode` | §6.4's padded input `A \|\| 0^v \|\| C \|\| 0^u \|\| [len(A)] \|\| [len(C)]` |
| `nistPoly` | §6.3's field polynomial `x¹²⁸ + x⁷ + x² + x + 1` |
| `maxBlocks` | the §5.2.1.1 length limits, as a block count |
| `AEADScheme.distAdvantage` | ACD19 Def. 2 / Fig. 1, one-time real-or-random AEAD advantage |
| `decryptQueryBound` / `q_d` | ACD19's decryption-query counter (`IsQueryBoundP` on decrypt) |

## Structure

Games and reductions are instantiations of one OracleSpec-polymorphic game skeleton
(`gcmGameSkeleton`, `Security/Games.lean`), which returns a `QueryImpl` rather than a baked-in
`simulateQ … |>.run'` so that the lazy-sampling lemmas compose with it directly. The five `game*`
instantiate it at `spec = unifSpec` (= `ProbComp`); `prfReduction` instantiates the same skeleton
at the PRF spec, forwarding the adversary's uniform-sampling queries through the `SubSpec` lift.
So a reduction is itself a game, just over a richer oracle spec.

The intermediate games are not `AEADScheme` instances: the hops change internal components (real
permutation → uniform tuple → lazily sampled tuple) while keeping fixed the encrypt/decrypt
oracle interface the adversary sees.

This file holds the assembled reduction and the hypothesis-free statements. The games, the
reduction and the per-hop lemmas live in `Games.lean`, `PrfHop.lean`, `AuthHop.lean` and
`PrivacyHop.lean`, with the supporting `Encoding.lean`, `Axu.lean`, `Counter.lean`,
`CipherProfile.lean` and `OneTimePad.lean`.

## Reading order

1. This file: the assembled reduction and the hypothesis-free statements.
2. `Security/Games.lean`, `Security/PrfHop.lean`, `Security/AuthHop.lean` and
   `Security/PrivacyHop.lean`: the games and the three hops (supporting: `Encoding`, `Axu`,
   `Counter`, `CipherProfile`, `OneTimePad`).
3. `Security/Polynomial.lean`, `Security/GhashAXU.lean`, `Security/NistIrreducible.lean`: the
   GHASH almost-XOR-universality bound and the irreducibility of `nistPoly`.
4. `Security/PrpSwitch.lean`: the PRP/PRF switching inequality at `prfReduction`.

Generic, scheme-independent lemmas live under `ToVCVio/`.
-/

namespace GCM

open OracleSpec OracleComp ENNReal AEADScheme ToVCVio

variable {K : Type}

/-! ## The general reduction -/

/-- **GCM one-time IND-CCA security**: the advantage is bounded by the PRF advantage of the
explicit distinguisher `B = prfReduction L adv` (`Security/PrfHop.lean`) plus one
almost-XOR-universality term per decryption query,

  `Adv^{ot-cca-ror}_{GCM}(A) ≤ Adv^{prf}(B) + q_d · ε`

with `hq : AEADScheme.decryptQueryBound adv q_d` unfolding to
`adv.IsQueryBoundP (· matches Sum.inr _) q_d`, a query bound on the decrypt-oracle index of
`aeadOneTimeCCASpec` (`AEAD/Defs.lean`).

`ε` is any parameter witnessing `GhashIsAXU L ε`, the almost-XOR-universality of
`fun H p => ghash H (gcmEncode p.1 p.2)`. No upper bound on it is assumed: this is a reduction,
and `ε` is instantiated downstream (`gcmOneTimeAEAD_security_maxBlocks` at `maxBlocks L / 2¹²⁸`,
proved in `Security/GhashAXU.lean`).

The side condition `hε : ε ≠ ⊤` is necessary, not cosmetic. The bound is stated in `ℝ` via
`ε.toReal` (this is where `game2_game3_le_auth` leaves `ℝ≥0∞` for `ℝ`) and
`(⊤ : ℝ≥0∞).toReal = 0`, so at `ε = ⊤` the conclusion would read
`distAdvantage ≤ prfAdvantage + q_d * 0`, which is false in general; `GhashIsAXU L ⊤` holds
trivially, so nothing else excludes that instance. It is not an upper bound on `ε` in disguise:
every finite `ε`, arbitrarily large, is admitted, and the single excluded point carries no
information, a `⊤` witness yielding a vacuous bound anyway.

Losslessness of `prp.keygen` (`Pr[⊥ | prp.keygen] = 0`, the `NeverFail` instance) is used by
`game4_eq_rand` (`Security/Games.lean`), where the ideal endpoint's keygen is dead and eliminating
a dead sample needs losslessness. It is not a hypothesis of this statement: every `ProbComp` is
lossless on this VCVio, so the instance is inferred. -/
-- ANCHOR: gcmOneTimeAEAD_security_of_axu
theorem gcmOneTimeAEAD_security_of_axu (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d)
    {ε : ℝ≥0∞} (hε : ε ≠ ⊤) (haxu : GhashIsAXU L ε) :
    AEADScheme.distAdvantage (gcmOneTimeAEAD prp L hL) adv ≤
      PRFScheme.prfAdvantage prp.toPRFScheme (prfReduction L adv) +
      (q_d : ℝ) * ε.toReal
-- ANCHOR_END: gcmOneTimeAEAD_security_of_axu
  := by
  have hg12 : Pr[= true | game1 prp L hL adv] = Pr[= true | game2 prp L hL adv] :=
    probOutput_eq_of_evalDist_eq (game1_eq_game2 prp L hL adv) true
  unfold AEADScheme.distAdvantage
  rw [← game4_eq_rand prp L hL adv, ← game0_eq_real prp L hL adv,
    ← probOutput_game3_eq_game4 prp L hL adv]
  calc |(Pr[= true | game3 prp L hL adv]).toReal -
        (Pr[= true | game0 prp L hL adv]).toReal|
    _ ≤ |(Pr[= true | game1 prp L hL adv]).toReal -
         (Pr[= true | game0 prp L hL adv]).toReal| +
        |(Pr[= true | game3 prp L hL adv]).toReal -
         (Pr[= true | game2 prp L hL adv]).toReal| := by
          rw [hg12]
          set g0 := (Pr[= true | game0 prp L hL adv]).toReal
          set g2 := (Pr[= true | game2 prp L hL adv]).toReal
          set g3 := (Pr[= true | game3 prp L hL adv]).toReal
          linarith [abs_sub_le g3 g2 g0]
    _ ≤ PRFScheme.prfAdvantage prp.toPRFScheme (prfReduction L adv) +
        (q_d : ℝ) * ε.toReal :=
      add_le_add (game0_game1_le_prf prp L hL adv)
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
degree of the GHASH polynomial and `2¹²⁸` is the size of the tag field. The exponent is spelled
`2 ^ (128 : ℕ)` so that `haxu` is syntactically the conclusion of `ghash_isAXU`
(`Security/GhashAXU.lean`), which `gcmOneTimeAEAD_security_prf` below feeds in. -/
theorem gcmOneTimeAEAD_security_maxBlocks (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d)
    (haxu : GhashIsAXU L ((maxBlocks L : ℝ≥0∞) / 2 ^ (128 : ℕ))) :
    AEADScheme.distAdvantage (gcmOneTimeAEAD prp L hL) adv ≤
      PRFScheme.prfAdvantage prp.toPRFScheme (prfReduction L adv) +
      (q_d : ℝ) * ((maxBlocks L : ℝ) / 2 ^ (128 : ℕ)) := by
  have h := gcmOneTimeAEAD_security_of_axu prp L hL adv q_d hq
    (ε := (maxBlocks L : ℝ≥0∞) / 2 ^ (128 : ℕ))
    (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)) haxu
  rwa [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat] at h

/-! ## The PRF-stated bound -/

/-- The PRF-stated bound with no hypothesis: `gcmOneTimeAEAD_security_maxBlocks` with `haxu`
supplied by `ghash_isAXU_unconditional`, which is `ghash_isAXU` at `nistPoly_irreducible`
(`Security/NistIrreducible.lean`). -/
-- ANCHOR: gcmOneTimeAEAD_security_prf
theorem gcmOneTimeAEAD_security_prf (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d) :
    AEADScheme.distAdvantage (gcmOneTimeAEAD prp L hL) adv ≤
      PRFScheme.prfAdvantage prp.toPRFScheme (prfReduction L adv) +
      (q_d : ℝ) * ((maxBlocks L : ℝ) / 2 ^ (128 : ℕ))
-- ANCHOR_END: gcmOneTimeAEAD_security_prf
  :=
  gcmOneTimeAEAD_security_maxBlocks prp L hL adv q_d hq (ghash_isAXU_unconditional L)

/-! ## The PRP-stated bound -/

/-- One-time IND-CCA security of GCM with the PRP security of the block cipher as its only
assumption, the main result of this file.

The PRF summand of `gcmOneTimeAEAD_security_prf` is replaced through
`prfAdvantage_le_prpAdvantage_switching` (`Security/PrpSwitch.lean`) by the PRP advantage of the
same reduction plus the switching term `(n + 2)(n + 1) / 2¹²⁹`, `n = ⌈L/128⌉`. `hL` is used both
to build the scheme and, in the switching proof, for the distinctness of the reduction's `n + 2`
query points.

The blueprint atom `aead_gcm_security` points here; the `-- ANCHOR:` markers delimit the
statement Verso extracts byte-for-byte. -/
-- ANCHOR: gcmOneTimeAEAD_security
theorem gcmOneTimeAEAD_security (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d) :
    AEADScheme.distAdvantage (gcmOneTimeAEAD prp L hL) adv ≤
      PRPScheme.prpAdvantage prp (prfReduction L adv) +
      ((((L + 127) / 128 : ℕ) : ℝ) + 2) * ((((L + 127) / 128 : ℕ) : ℝ) + 1)
        / 2 ^ (129 : ℕ) +
      (q_d : ℝ) * ((maxBlocks L : ℝ) / 2 ^ (128 : ℕ))
-- ANCHOR_END: gcmOneTimeAEAD_security
  := by
  refine le_trans (gcmOneTimeAEAD_security_prf prp L hL adv q_d hq) ?_
  have h := prfAdvantage_le_prpAdvantage_switching prp L hL adv
  linarith

end GCM
