/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Pseudorandom permutations (PRPs)

A pseudorandom permutation (PRP) is the abstract model of a block cipher: a keyed,
invertible map on a block space `X` that no efficient adversary can distinguish
from a uniformly random permutation of `X`.

## Main definitions

- `PRPScheme.prpRealExp` is *defined* to be `PRFScheme.prfRealExp prp.toPRFScheme`, so the PRP
  and the PRF game share one and the same real experiment and differ only on their ideal sides.
  That is the premise the PRP/PRF switching inequality rests on: the two advantages are
  `|R - I_prp|` and `|R - I_prf|` over a common real term `R`. `PRPScheme.prpRealExp_eq` records
  that this body is definitionally the experiment built from `oracleUnif` and `oraclePerm` via
  `prpQueryImpl`, so choosing it discards nothing.
- `PRPScheme.prpIdealExp` draws its permutation wholesale with `$ᵗ (Equiv.Perm X)`, the
  canonical ideal experiment.
- Its tractable companion (a without-replacement sampler over a *fixed list* of query points,
  together with the distributional equivalence relating the two) is generic, so it lives in
  `ToVCVio/CryptoFoundations/PRPSwitching.lean` rather than here.

## References

- [BR] Bellare, Rogaway. *Code-Based Game-Playing Proofs and the Security of
  Triple Encryption.* EUROCRYPT 2006, https://eprint.iacr.org/2004/331.pdf —
  the PRP/PRF switching lemma and its `q²/2ⁿ⁺¹` bound.
-/

open OracleSpec OracleComp

/-- A block cipher (NIST SP 800-38D §5.1): a keyed permutation on `X`, given as
forward/inverse functions that are mutually inverse for every key (`correct`). -/
structure BlockCipher (K X : Type) where
  /-- The forward cipher function `CIPHₖ`. -/
  perm : K → X → X
  /-- The inverse cipher function `CIPHₖ⁻¹`. -/
  invPerm : K → X → X
  /-- `perm k` and `invPerm k` are mutually inverse for every key `k`. -/
  correct : ∀ k x, invPerm k (perm k x) = x ∧ perm k (invPerm k x) = x

/-- A pseudorandom permutation scheme: a `BlockCipher` plus randomized key
generation (`keygen`). -/
structure PRPScheme (K X : Type) extends BlockCipher K X where
  /-- Randomized key generation. -/
  keygen : ProbComp K

namespace PRPScheme

variable {K X : Type}

/-- View a PRP as a `PRFScheme` by forgetting invertibility and keeping only the
forward permutation (`eval := perm`). The PRP/PRF switching lemma transfers PRP
security to this PRF view. -/
def toPRFScheme (prp : PRPScheme K X) : PRFScheme K X X :=
  { keygen := prp.keygen, eval := prp.perm }

/-- Oracle spec for the PRP game: uniform randomness plus a permutation oracle. Reducibly equal to
`PRFScheme.PRFOracleSpec X X`, which is what lets the PRF forwarding lemmas below apply. -/
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

/-- Real experiment: runs the adversary against the keyed permutation. -/
noncomputable def prpRealExp (prp : PRPScheme K X) (adversary : PRPAdversary X) :
    ProbComp Bool :=
  PRFScheme.prfRealExp prp.toPRFScheme adversary

/-- The real experiment, unfolded. -/
theorem prpRealExp_eq (prp : PRPScheme K X) (adversary : PRPAdversary X) :
    prpRealExp prp adversary =
      (do let k ← prp.keygen; simulateQ (prpQueryImpl (prp.perm k)) adversary) :=
  rfl

/-- Ideal experiment: runs the adversary against a uniformly random permutation. -/
def prpIdealExp [SampleableType (Equiv.Perm X)] (adversary : PRPAdversary X) :
    ProbComp Bool := do
  let π ← $ᵗ (Equiv.Perm X)
  simulateQ (prpQueryImpl fun x => π x) adversary

/-- The PRP advantage: the gap between the adversary's success probabilities in
the real and ideal experiments. -/
noncomputable def prpAdvantage [SampleableType (Equiv.Perm X)]
    (prp : PRPScheme K X) (adversary : PRPAdversary X) : ℝ :=
  |(Pr[= true | prpRealExp prp adversary]).toReal -
    (Pr[= true | prpIdealExp adversary]).toReal|

/-- `prpQueryImpl g` viewed as a PRF scheme with a trivial key. -/
private def asPRF (g : X → X) : PRFScheme Unit X X :=
  { keygen := pure (), eval := fun _ x => g x }

/-- A single permutation-oracle (`Sum.inr`) query under `prpQueryImpl g` returns `g d`. -/
theorem simulateQ_prpQueryImpl_inr (g : X → X) (d : X) :
    simulateQ (prpQueryImpl g)
      ((liftM (OracleSpec.query (Sum.inr d) :
        OracleQuery (PRFScheme.PRFOracleSpec X X) X)) : OracleComp (PRPOracleSpec X) X)
      = pure (g d) :=
  PRFScheme.simulateQ_prfRealQueryImpl_inr (asPRF g) () d

/-- A fixed list of permutation-oracle queries under `prpQueryImpl g` collapses to `pure` of
the list of images: the eager fetch loop of a non-adaptive distinguisher carries no
probabilistic content on the real side. -/
theorem simulateQ_prpQueryImpl_mapM_inr (g : X → X) (pts : List X) :
    simulateQ (prpQueryImpl g)
      (pts.mapM (fun t => liftM (OracleSpec.query (Sum.inr t) :
        OracleQuery (PRFScheme.PRFOracleSpec X X) X)))
      = pure (pts.map g) := by
  simp only [simulateQ_list_mapM, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, prpQueryImpl, QueryImpl.add_apply_inr, oraclePerm, map_pure, id_eq,
    List.mapM_pure]

/-- A computation using only the uniform-sampling oracles is unchanged by `prpQueryImpl g`. -/
theorem simulateQ_prpQueryImpl_liftComp {β : Type} (g : X → X)
    (ob : OracleComp unifSpec β) :
    simulateQ (prpQueryImpl g)
      (OracleComp.liftComp ob (PRFScheme.PRFOracleSpec X X)) = ob :=
  PRFScheme.simulateQ_prfRealQueryImpl_liftComp (asPRF g) () ob

end PRPScheme
