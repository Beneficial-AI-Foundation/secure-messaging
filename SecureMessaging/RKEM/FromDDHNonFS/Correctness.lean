/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SecureMessaging.RKEM.FromDDHNonFS.Construction

/-!
# RKEM from DDH (non-forward-secure) — Correctness

This file proves that the non-forward-secure Diffie-Hellman RKEM of
`SecureMessaging.RKEM.FromDDHNonFS.Construction` is perfectly correct, i.e. `(0, 0)`-correct in
the sense of [TripleRatchet, Def. 5.3], as claimed by [TripleRatchet, Thm. A.3].

Both halves of Def. 5.3 hold with error exactly zero, unconditionally:

- **Shared keys agree.** With `(ekA, dkA) = (x • gen, x)` and `(êkB, d̂kB) = (y • gen, y)`,
  `REnc-A` outputs `K = x • (y • gen)` and `RDec-B` outputs `K' = y • (x • gen)`; both equal
  `(x * y) • gen`, the paper's `g^{xy}` (`probOutput_correctExpA_eq_one`).
- **Updated keys are distributed as fresh ones.** The scheme is not forward secure: the updated
  pair `(êkA, d̂kA)` produced by a round is `A`'s fresh pair itself, and fresh and updated key
  generation coincide (`evalDist_ratchetRoundOutputA_eq_evalDist_rkeygen`).

The algorithms are the same for `A` and `B`, so the `B`-side experiments are definitionally the
`A`-side ones.

[REFERENCES]

- [TripleRatchet] Dodis, Jost, Katsumata, Prest, Schmidt.
  *Triple Ratchet: A Bandwidth Efficient Hybrid-Secure Signal Protocol.*
  EUROCRYPT 2025, https://eprint.iacr.org/2025/078.pdf
-/

open OracleSpec OracleComp ENNReal RKEMScheme

namespace ddhRKEM

variable {F : Type} [Field F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G]

/-- In one round of the DH RKEM from `A` towards `B`, the two parties always agree on the shared
key: `x • (y • gen) = y • (x • gen)`, the paper's `g^{xy} = g^{yx}`. -/
theorem probOutput_correctExpA_eq_one [DecidableEq G] (gen : G) :
    Pr[= true | RKEMScheme.correctExpA (scheme (F := F) gen)] = 1 := by
  unfold RKEMScheme.correctExpA
  simp [scheme, rkeygen, renc, rdec, smul_smul, mul_comm]

/-- `ratchetRoundOutputA` at the DH RKEM has exactly the distribution of fresh key generation: the
updated pair it returns is `A`'s fresh pair itself, and `B`'s key pair is discarded. -/
theorem evalDist_ratchetRoundOutputA_eq_evalDist_rkeygen (gen : G) :
    ProbCompRuntime.probComp.evalDist (RKEMScheme.ratchetRoundOutputA (scheme (F := F) gen)) =
      ProbCompRuntime.probComp.evalDist (rkeygen (F := F) gen ()) := by
  change (𝒟[RKEMScheme.ratchetRoundOutputA (scheme (F := F) gen)] : SPMF (G × F)) =
    𝒟[rkeygen (F := F) gen ()]
  unfold RKEMScheme.ratchetRoundOutputA
  simp only [scheme, renc, rdec, pure_bind]
  refine evalDist_ext fun y => ?_
  rw [probOutput_bind_bind_swap]
  simp

/-- **Perfect correctness** (Def. 5.3, [TripleRatchet, Thm. A.3]) of the non-forward-secure DH
RKEM: both the shared-key error and the update-key-distribution error are exactly zero. -/
-- ANCHOR: deltaCorrect
theorem deltaCorrect [DecidableEq G] (gen : G) :
    RKEMScheme.deltaCorrect (scheme (F := F) gen) ProbCompRuntime.probComp 0 0
-- ANCHOR_END: deltaCorrect
    := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · unfold RKEMScheme.correctnessErrorA
    change 1 - Pr[= true | RKEMScheme.correctExpA (scheme (F := F) gen)] ≤ 0
    simp [probOutput_correctExpA_eq_one]
  · unfold RKEMScheme.correctnessErrorB
    change 1 - Pr[= true | RKEMScheme.correctExpB (scheme (F := F) gen)] ≤ 0
    rw [show (scheme (F := F) gen).correctExpB = (scheme gen).correctExpA by rfl]
    simp [probOutput_correctExpA_eq_one]
  · unfold RKEMScheme.updateKeyDistErrorA
    rw [show (scheme (F := F) gen).rsetup >>= (scheme gen).rkeygenAUpdated = rkeygen gen () by
      simp [scheme],
      evalDist_ratchetRoundOutputA_eq_evalDist_rkeygen, SPMF.tvDist_self]
    simp
  · unfold RKEMScheme.updateKeyDistErrorB
    rw [show (scheme (F := F) gen).ratchetRoundOutputB = (scheme gen).ratchetRoundOutputA by rfl,
      show (scheme (F := F) gen).rsetup >>= (scheme gen).rkeygenBUpdated = rkeygen gen () by
      simp [scheme],
      evalDist_ratchetRoundOutputA_eq_evalDist_rkeygen, SPMF.tvDist_self]
    simp

end ddhRKEM
