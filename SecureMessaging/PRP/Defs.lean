/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.SimSemantics.Append

/-!
# Pseudorandom permutations (PRPs)

A pseudorandom permutation (PRP) is the abstract model of a block cipher: a keyed,
invertible map on a block space `X` that no efficient adversary can distinguish
from a uniformly random permutation of `X`.

Modes of operation (CTR, GCM, ...) consume only the forward direction `perm`; the
inverse `invPerm` merely witnesses that the primitive is a permutation. Security
proofs for such modes replace `perm` by a random function, justified by the
PRP/PRF switching lemma applied to the PRF view `PRPScheme.toPRFScheme`; see
`SecureMessaging.AES.Defs` for the AES-specific specialization.

## References

- [BR] Bellare, Rogaway. *Code-Based Game-Playing Proofs and the Security of
  Triple Encryption.* EUROCRYPT 2006, https://eprint.iacr.org/2004/331.pdf —
  the PRP/PRF switching lemma and its `q²/2ⁿ⁺¹` bound.
-/

open OracleSpec OracleComp

/-- A pseudorandom permutation scheme: key space `K`, domain `X`. -/
structure PRPScheme (K X : Type) where
  /-- Randomized key generation. -/
  keygen : ProbComp K
  /-- The keyed permutation on `X`. -/
  perm : K → X → X
  /-- The inverse of the keyed permutation. -/
  invPerm : K → X → X

namespace PRPScheme

variable {K X : Type}

/-- Correctness: `invPerm k` and `perm k` are mutually inverse for every key `k`. -/
def Correct (prp : PRPScheme K X) : Prop :=
  ∀ k x, prp.invPerm k (prp.perm k x) = x ∧ prp.perm k (prp.invPerm k x) = x

/-- View a PRP as a `PRFScheme` by forgetting invertibility and keeping only the
forward permutation (`eval := perm`). Modes like CTR/GCM consume a block cipher
this way.

This is only the structural coercion, not the switching lemma itself: PRP
security transfers to PRF security via that lemma (for a 128-bit block, loss
`~ q² / 2¹²⁹` in `q` distinct queries), whose statement and proof are future
work. -/
def toPRFScheme (prp : PRPScheme K X) : PRFScheme K X X :=
  { keygen := prp.keygen, eval := prp.perm }

/-- Oracle spec for the PRP game: uniform randomness plus a permutation oracle. -/
def PRPOracleSpec (X : Type) := unifSpec + (X →ₒ X)

/-- A PRP adversary: a computation with access to the PRP oracles, outputting a
guess bit. -/
abbrev PRPAdversary (X : Type) := OracleComp (PRPOracleSpec X) Bool

/-- Uniform-randomness oracle for the PRP game. -/
def oracleUnif : QueryImpl unifSpec ProbComp :=
  HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)

/-- Permutation oracle answering each query `x` with `g x`. -/
def oraclePerm (g : X → X) : QueryImpl (X →ₒ X) ProbComp :=
  fun x => pure (g x)

/-- Combined oracle implementation for the PRP game using permutation `g`. -/
def prpQueryImpl (g : X → X) : QueryImpl (PRPOracleSpec X) ProbComp :=
  oracleUnif + oraclePerm g

/-- Real experiment: runs the adversary against the keyed permutation. -/
def prpRealExp (prp : PRPScheme K X) (adversary : PRPAdversary X) :
    ProbComp Bool :=
    sorry

/-- Ideal experiment: runs the adversary against a uniformly random permutation. -/
def prpIdealExp [SampleableType (Equiv.Perm X)] (adversary : PRPAdversary X) :
    ProbComp Bool := do
  let π ← $ᵗ (Equiv.Perm X)
  simulateQ (prpQueryImpl fun x => π x) adversary

/-- The PRP advantage: the gap between the adversary's success probabilities in
the real and ideal experiments. -/
noncomputable def prpAdvantage [SampleableType (Equiv.Perm X)]
    (prp : PRPScheme K X) (adversary : PRPAdversary X) : ℝ :=
    sorry

end PRPScheme
