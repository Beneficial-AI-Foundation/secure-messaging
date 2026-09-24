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

The PRP game is set up exactly like VCVio's PRF game: same oracle spec, same adversary type,
real/ideal experiments and an absolute-difference advantage. The real experiment `prpRealExp`
is *defined* as the PRF real experiment of `toPRFScheme`, so the two games share their real
side and differ only in the ideal one, which is what the PRP/PRF switching lemma [BR]
compares. Candidate for upstream VCVio.

## References

- [BR] Bellare, Rogaway. *The Security of Triple Encryption and a Framework for Code-Based
  Game-Playing Proofs.* EUROCRYPT 2006, https://eprint.iacr.org/2004/331.pdf
-/

open OracleSpec OracleComp

/-- A block cipher (NIST SP 800-38D §5.1): a keyed permutation on `X`, given as
forward/inverse functions that are mutually inverse for every key (`correct`). -/
-- ANCHOR: BlockCipher
structure BlockCipher (K X : Type) where
  /-- The forward cipher function `CIPHₖ`. -/
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

/-- Oracle spec for the PRP game: uniform randomness plus a permutation oracle. Reducibly equal to
`PRFScheme.PRFOracleSpec X X`, which is what lets the PRF simulation lemmas below apply. -/
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

/-- Real experiment: sample a key `k` and run the adversary against the permutation `perm k`.
It is by definition the PRF real experiment of `toPRFScheme`. -/
def prpRealExp (prp : PRPScheme K X) (adversary : PRPAdversary X) :
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

/-- The PRP advantage of an adversary: the absolute difference between the probabilities that
it outputs `true` in the real and in the ideal experiment. -/
-- ANCHOR: prpAdvantage
noncomputable def prpAdvantage [SampleableType (Equiv.Perm X)]
    (prp : PRPScheme K X) (adversary : PRPAdversary X) : ℝ :=
  |(Pr[= true | prpRealExp prp adversary]).toReal -
    (Pr[= true | prpIdealExp adversary]).toReal|
-- ANCHOR_END: prpAdvantage

/-- `asPRF g` is the fixed function `g` viewed as a PRF scheme with a trivial key, so that the
PRF simulation lemmas apply to `prpQueryImpl g`. -/
private def asPRF (g : X → X) : PRFScheme Unit X X :=
  { keygen := pure (), eval := fun _ x => g x }

/-- For a fixed function `g : X → X`, a query at `d` always returns `g d`. -/
theorem simulateQ_prpQueryImpl_inr (g : X → X) (d : X) :
    simulateQ (prpQueryImpl g)
      ((liftM (OracleSpec.query (Sum.inr d) :
        OracleQuery (PRFScheme.PRFOracleSpec X X) X)) : OracleComp (PRPOracleSpec X) X)
      = pure (g d) :=
  PRFScheme.simulateQ_prfRealQueryImpl_inr (asPRF g) () d

/-- For a fixed function `g : X → X`, queries at `d₁, …, dₙ` always return
`g d₁, …, g dₙ`. -/
theorem simulateQ_prpQueryImpl_mapM_inr (g : X → X) (pts : List X) :
    simulateQ (prpQueryImpl g)
      (pts.mapM (fun t => liftM (OracleSpec.query (Sum.inr t) :
        OracleQuery (PRFScheme.PRFOracleSpec X X) X)))
      = pure (pts.map g) := by
  simp only [simulateQ_list_mapM, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, prpQueryImpl, QueryImpl.add_apply_inr, oraclePerm, map_pure, id_eq,
    List.mapM_pure]

/-- A computation that makes no queries to `g` is unchanged by giving it access to `g`. -/
theorem simulateQ_prpQueryImpl_liftComp {β : Type} (g : X → X)
    (ob : OracleComp unifSpec β) :
    simulateQ (prpQueryImpl g)
      (OracleComp.liftComp ob (PRFScheme.PRFOracleSpec X X)) = ob :=
  PRFScheme.simulateQ_prfRealQueryImpl_liftComp (asPRF g) () ob

end PRPScheme
