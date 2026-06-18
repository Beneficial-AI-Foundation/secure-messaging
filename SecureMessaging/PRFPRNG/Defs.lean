import VCVio.CryptoFoundations.SecExp
import VCVio.CryptoFoundations.PRG
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.SimSemantics.Append

open OracleSpec OracleComp ENNReal

universe u

/-- A PRF-PRNG scheme: key space `K`, state space `Sigma`, input space `I`,
output space `R`. -/
structure PRFPRNGScheme (K Sigma I R : Type) where
  /-- Initialize the scheme state from a key. -/
  init : K → Sigma
  /-- Update the state on an input, producing a new state and an output. -/
  up : Sigma → I → Sigma × R

namespace PRFPRNGScheme

section Game

variable {K Sigma I R : Type}

/-- State of the PRF-PRNG security game. -/
structure GameState (Sigma I R : Type) where
  /-- Current scheme state. -/
  σ : Sigma
  /-- Whether the state has been corrupted. -/
  corr : Bool
  /-- Whether the PRF challenge has been issued. -/
  prf : Bool
  /-- Whether the PRNG challenge has been issued. -/
  prng : Bool

/-- Oracle spec for the PRF-PRNG security game: uniform randomness, a process
oracle, PRF and PRNG challenge oracles, and a corruption oracle. -/
def pppSecuritySpec (Sigma I R : Type) :=
  unifSpec + (Option I →ₒ R) + (I →ₒ Option (Sigma × R))
    + (Option I →ₒ Option R) + (Unit →ₒ Option Sigma)

namespace pppSecuritySpec

variable {Sigma I R : Type}

/-- Domain index selecting the uniform-randomness oracle. -/
@[match_pattern] abbrev OUnif (n : ℕ) : (pppSecuritySpec Sigma I R).Domain :=
  .inl (.inl (.inl (.inl n)))
/-- Domain index selecting the process oracle. -/
@[match_pattern] abbrev OProcess (i : Option I) : (pppSecuritySpec Sigma I R).Domain :=
  .inl (.inl (.inl (.inr i)))
/-- Domain index selecting the PRF challenge oracle. -/
@[match_pattern] abbrev OChallPrf (i : I) : (pppSecuritySpec Sigma I R).Domain :=
  .inl (.inl (.inr i))
/-- Domain index selecting the PRNG challenge oracle. -/
@[match_pattern] abbrev OChallPrng (i : Option I) : (pppSecuritySpec Sigma I R).Domain :=
  .inl (.inr i)
/-- Domain index selecting the corruption oracle. -/
@[match_pattern] abbrev OCorr : (pppSecuritySpec Sigma I R).Domain :=
  .inr ()

end pppSecuritySpec

/-- A PRF-PRNG adversary: a computation with access to the game oracles,
outputting a guess bit. -/
abbrev PPPAdversary (Sigma I R : Type) := OracleComp (pppSecuritySpec Sigma I R) Bool

/-- Sample a fresh input when none is provided; return the given input otherwise. -/
def sampleIfNecessary [SampleableType I] (i : Option I) :
    StateT (GameState Sigma I R) ProbComp I :=
  sorry

/-- Process oracle: advances the scheme state and returns the produced output. -/
def oracleProcess [SampleableType I] (ppp : PRFPRNGScheme K Sigma I R) :
    QueryImpl (Option I →ₒ R) (StateT (GameState Sigma I R) ProbComp) :=
  sorry

/-- PRF challenge oracle: real response at `b = false`, random at `b = true`. -/
def oracleChallPrf (b : Bool) (F : I → R)
    (ppp : PRFPRNGScheme K Sigma I R) :
    QueryImpl (I →ₒ Option (Sigma × R)) (StateT (GameState Sigma I R) ProbComp) :=
  sorry

/-- PRNG challenge oracle: real output at `b = false`, random at `b = true`. -/
def oracleChallPrng [SampleableType I] [SampleableType R] (b : Bool)
    (ppp : PRFPRNGScheme K Sigma I R) :
    QueryImpl (Option I →ₒ Option R) (StateT (GameState Sigma I R) ProbComp) :=
  sorry

/-- Corruption oracle: exposes the current scheme state. -/
def oracleCorr (Sigma I R : Type) :
    QueryImpl (Unit →ₒ Option Sigma) (StateT (GameState Sigma I R) ProbComp) :=
  sorry

/-- Uniform-randomness oracle lifted to the game-state monad. -/
def oracleUnif (Sigma I R : Type) :
    QueryImpl unifSpec (StateT (GameState Sigma I R) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (GameState Sigma I R) ProbComp)

/-- Combined oracle implementation for the PRF-PRNG game. -/
def pppSecurityImpl [SampleableType I] [SampleableType R]
    (b : Bool) (F : I → R) (ppp : PRFPRNGScheme K Sigma I R) :
    QueryImpl (pppSecuritySpec Sigma I R) (StateT (GameState Sigma I R) ProbComp) :=
  oracleUnif Sigma I R
    + oracleProcess ppp
    + oracleChallPrf b F ppp
    + oracleChallPrng b ppp
    + oracleCorr Sigma I R

/-- Build the initial game state from a starting scheme state (all flags unset). -/
def initGameState (σ : Sigma) : GameState Sigma I R :=
  { σ := σ, corr := false, prf := false, prng := false }

/-- Real experiment: runs the adversary against the real (`b = false`) oracles. -/
def pppRealExp [SampleableType K] [SampleableType I] [SampleableType R]
    [SampleableType (I → R)]
    (ppp : PRFPRNGScheme K Sigma I R) (adversary : PPPAdversary Sigma I R) :
    ProbComp Bool := do
  let k ← $ᵗ K
  let F ← $ᵗ (I → R)
  let (b', _) ← (simulateQ (pppSecurityImpl false F ppp) adversary).run
                  (initGameState (ppp.init k))
  return b'

/-- Ideal experiment: runs the adversary against the ideal (`b = true`) oracles. -/
def pppIdealExp [SampleableType K] [SampleableType I] [SampleableType R]
    [SampleableType (I → R)]
    (ppp : PRFPRNGScheme K Sigma I R) (adversary : PPPAdversary Sigma I R) :
    ProbComp Bool :=
    sorry

/-- The PRF-PRNG advantage: the gap between the adversary's success probabilities
in the real and ideal experiments. -/
noncomputable def pppAdvantage [SampleableType K] [SampleableType I] [SampleableType R]
    [SampleableType (I → R)]
    (ppp : PRFPRNGScheme K Sigma I R) (adversary : PPPAdversary Sigma I R) : ℝ :=
  |(Pr[= true | pppRealExp ppp adversary]).toReal -
    (Pr[= true | pppIdealExp ppp adversary]).toReal|

end Game

end PRFPRNGScheme

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

namespace PRFPRNGScheme

variable {S X R : Type}

/-- Construction of a PRF-PRNG scheme from a PRP and a PRG. -/
def PRFPRNG (prp : PRPScheme S X) (prg : PRGScheme X (S × R)) :
    PRFPRNGScheme S S X R where
  init := sorry
  up := sorry

theorem security
    [SampleableType S] [SampleableType X] [SampleableType R]
    [SampleableType (X → R)] [SampleableType (S × R)] [SampleableType (Equiv.Perm X)]
    (prp : PRPScheme S X) (prg : PRGScheme X (S × R))
    (adversary : PPPAdversary S X R) (q : ℕ) :
    (sorry : Prop) :=
  sorry

end PRFPRNGScheme
