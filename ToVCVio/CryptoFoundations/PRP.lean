/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.Constructions.SampleableType
import ToVCVio.CryptoFoundations.PRF

/-!
# Pseudorandom permutations (PRPs)

A pseudorandom permutation (PRP) is the abstract model of a block cipher: a keyed,
invertible map on a block space `X` that no efficient adversary can distinguish
from a uniformly random permutation of `X`.

`PRPScheme` mirrors VCVio's `PRFScheme` field for field, and the real experiment
`prpRealExp` is *defined* as the PRF real experiment of `toPRFScheme`. The PRP and PRF games
therefore share their real side and differ only in the ideal one, which is what the PRP/PRF
switching lemma [BR] compares. Candidate for upstream VCVio.

## References

- [BR] Bellare, Rogaway. *Code-Based Game-Playing Proofs and the Security of
  Triple Encryption.* EUROCRYPT 2006, https://eprint.iacr.org/2004/331.pdf
-/

open OracleSpec OracleComp

/-- A block cipher (NIST SP 800-38D §5.1): a keyed permutation on `X`, given as
forward/inverse functions that are mutually inverse for every key (`correct`). -/
-- ANCHOR: BlockCipher
structure BlockCipher (K X : Type) where
  /-- The forward cipher function `CIPHₖ` (§5.1). -/
  perm : K → X → X
  /-- The inverse cipher function `CIPHₖ⁻¹`. -/
  invPerm : K → X → X
  /-- `perm k` and `invPerm k` are mutually inverse for every key `k`. -/
  correct : ∀ k x, invPerm k (perm k x) = x ∧ perm k (invPerm k x) = x
-- ANCHOR_END: BlockCipher

/-- A pseudorandom permutation scheme: a `BlockCipher` plus randomized key
generation (`keygen`). -/
-- ANCHOR: PRPScheme
structure PRPScheme (K X : Type) extends BlockCipher K X where
  /-- Randomized key generation. -/
  keygen : ProbComp K
-- ANCHOR_END: PRPScheme

namespace PRPScheme

variable {K X : Type}

/-- A PRP viewed as a PRF: keep the forward permutation, forget the inverse. -/
def toPRFScheme (prp : PRPScheme K X) : PRFScheme K X X :=
  { keygen := prp.keygen, eval := prp.perm }

/-- Oracle spec for the PRP game: uniform randomness plus a permutation oracle. -/
abbrev PRPOracleSpec (X : Type) := unifSpec + (X →ₒ X)

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

/-- Real experiment: the adversary against the keyed permutation. Defined as the PRF real
experiment of `toPRFScheme`, so the PRP and PRF games share their real side. -/
noncomputable def prpRealExp (prp : PRPScheme K X) (adversary : PRPAdversary X) :
    ProbComp Bool :=
  PRFScheme.prfRealExp prp.toPRFScheme adversary

theorem prpRealExp_eq (prp : PRPScheme K X) (adversary : PRPAdversary X) :
    prpRealExp prp adversary =
      (do let k ← prp.keygen; simulateQ (prpQueryImpl (prp.perm k)) adversary) :=
  rfl

/-- Ideal experiment: the adversary against a uniformly random permutation. -/
def prpIdealExp [SampleableType (Equiv.Perm X)] (adversary : PRPAdversary X) :
    ProbComp Bool := do
  let π ← $ᵗ (Equiv.Perm X)
  simulateQ (prpQueryImpl fun x => π x) adversary

/-- The PRP advantage: how much better than chance the adversary tells the two experiments
apart. -/
-- ANCHOR: prpAdvantage
noncomputable def prpAdvantage [SampleableType (Equiv.Perm X)]
    (prp : PRPScheme K X) (adversary : PRPAdversary X) : ℝ :=
  |(Pr[= true | prpRealExp prp adversary]).toReal -
    (Pr[= true | prpIdealExp adversary]).toReal|
-- ANCHOR_END: prpAdvantage

/-- `prpQueryImpl g` as a PRF scheme with a trivial key, to reuse the PRF forwarding lemmas. -/
private def asPRF (g : X → X) : PRFScheme Unit X X :=
  { keygen := pure (), eval := fun _ x => g x }

theorem simulateQ_prpQueryImpl_inr (g : X → X) (d : X) :
    simulateQ (prpQueryImpl g)
      ((liftM (OracleSpec.query (Sum.inr d) :
        OracleQuery (PRFScheme.PRFOracleSpec X X) X)) : OracleComp (PRPOracleSpec X) X)
      = pure (g d) :=
  PRFScheme.simulateQ_prfRealQueryImpl_inr (asPRF g) () d

theorem simulateQ_prpQueryImpl_mapM_inr (g : X → X) (pts : List X) :
    simulateQ (prpQueryImpl g)
      (pts.mapM (fun t => liftM (OracleSpec.query (Sum.inr t) :
        OracleQuery (PRFScheme.PRFOracleSpec X X) X)))
      = pure (pts.map g) :=
  PRFScheme.simulateQ_prfRealQueryImpl_mapM_inr (asPRF g) () pts

/-- A computation that only samples uniformly is unchanged by `prpQueryImpl g`. -/
theorem simulateQ_prpQueryImpl_liftComp {β : Type} (g : X → X)
    (ob : OracleComp unifSpec β) :
    simulateQ (prpQueryImpl g)
      (OracleComp.liftComp ob (PRFScheme.PRFOracleSpec X X)) = ob :=
  PRFScheme.simulateQ_prfRealQueryImpl_liftComp (asPRF g) () ob

end PRPScheme
