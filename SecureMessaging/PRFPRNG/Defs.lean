import VCVio.CryptoFoundations.SecExp
import VCVio.CryptoFoundations.PRG
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.SimSemantics.Append

open OracleSpec OracleComp ENNReal

universe u

structure PRFPRNGScheme (K Sigma I R : Type) where
  init : K → Sigma
  up : Sigma → I → Sigma × R

namespace PRFPRNGScheme

section Game

variable {K Sigma I R : Type}

structure GameState (Sigma I R : Type) where
  σ : Sigma
  corr : Bool
  prf : Bool
  prng : Bool

def pppSecuritySpec (Sigma I R : Type) :=
  unifSpec + (Option I →ₒ R) + (I →ₒ Option (Sigma × R))
    + (Option I →ₒ Option R) + (Unit →ₒ Option Sigma)

namespace pppSecuritySpec

variable {Sigma I R : Type}

@[match_pattern] abbrev OUnif (n : ℕ) : (pppSecuritySpec Sigma I R).Domain :=
  .inl (.inl (.inl (.inl n)))
@[match_pattern] abbrev OProcess (i : Option I) : (pppSecuritySpec Sigma I R).Domain :=
  .inl (.inl (.inl (.inr i)))
@[match_pattern] abbrev OChallPrf (i : I) : (pppSecuritySpec Sigma I R).Domain :=
  .inl (.inl (.inr i))
@[match_pattern] abbrev OChallPrng (i : Option I) : (pppSecuritySpec Sigma I R).Domain :=
  .inl (.inr i)
@[match_pattern] abbrev OCorr : (pppSecuritySpec Sigma I R).Domain :=
  .inr ()

end pppSecuritySpec

abbrev PPPAdversary (Sigma I R : Type) := OracleComp (pppSecuritySpec Sigma I R) Bool

def sampleIfNecessary [SampleableType I] (i : Option I) :
    StateT (GameState Sigma I R) ProbComp I :=
  sorry

def oracleProcess [SampleableType I] (ppp : PRFPRNGScheme K Sigma I R) :
    QueryImpl (Option I →ₒ R) (StateT (GameState Sigma I R) ProbComp) :=
  sorry

def oracleChallPrf (b : Bool) (F : I → R)
    (ppp : PRFPRNGScheme K Sigma I R) :
    QueryImpl (I →ₒ Option (Sigma × R)) (StateT (GameState Sigma I R) ProbComp) :=
  sorry

def oracleChallPrng [SampleableType I] [SampleableType R] (b : Bool)
    (ppp : PRFPRNGScheme K Sigma I R) :
    QueryImpl (Option I →ₒ Option R) (StateT (GameState Sigma I R) ProbComp) :=
  sorry

def oracleCorr (Sigma I R : Type) :
    QueryImpl (Unit →ₒ Option Sigma) (StateT (GameState Sigma I R) ProbComp) :=
  sorry

def oracleUnif (Sigma I R : Type) :
    QueryImpl unifSpec (StateT (GameState Sigma I R) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (GameState Sigma I R) ProbComp)

def pppSecurityImpl [SampleableType I] [SampleableType R]
    (b : Bool) (F : I → R) (ppp : PRFPRNGScheme K Sigma I R) :
    QueryImpl (pppSecuritySpec Sigma I R) (StateT (GameState Sigma I R) ProbComp) :=
  oracleUnif Sigma I R
    + oracleProcess ppp
    + oracleChallPrf b F ppp
    + oracleChallPrng b ppp
    + oracleCorr Sigma I R

def initGameState (σ : Sigma) : GameState Sigma I R :=
  { σ := σ, corr := false, prf := false, prng := false }

def pppRealExp [SampleableType K] [SampleableType I] [SampleableType R]
    [SampleableType (I → R)]
    (ppp : PRFPRNGScheme K Sigma I R) (adversary : PPPAdversary Sigma I R) :
    ProbComp Bool := do
  let k ← $ᵗ K
  let F ← $ᵗ (I → R)
  let (b', _) ← (simulateQ (pppSecurityImpl false F ppp) adversary).run
                  (initGameState (ppp.init k))
  return b'

def pppIdealExp [SampleableType K] [SampleableType I] [SampleableType R]
    [SampleableType (I → R)]
    (ppp : PRFPRNGScheme K Sigma I R) (adversary : PPPAdversary Sigma I R) :
    ProbComp Bool :=
    sorry

noncomputable def pppAdvantage [SampleableType K] [SampleableType I] [SampleableType R]
    [SampleableType (I → R)]
    (ppp : PRFPRNGScheme K Sigma I R) (adversary : PPPAdversary Sigma I R) : ℝ :=
  |(Pr[= true | pppRealExp ppp adversary]).toReal -
    (Pr[= true | pppIdealExp ppp adversary]).toReal|

end Game

end PRFPRNGScheme

structure PRPScheme (K X : Type) where
  keygen : ProbComp K
  perm : K → X → X
  invPerm : K → X → X

namespace PRPScheme

variable {K X : Type}

def Correct (prp : PRPScheme K X) : Prop :=
  ∀ k x, prp.invPerm k (prp.perm k x) = x ∧ prp.perm k (prp.invPerm k x) = x

def PRPOracleSpec (X : Type) := unifSpec + (X →ₒ X)

abbrev PRPAdversary (X : Type) := OracleComp (PRPOracleSpec X) Bool

def oracleUnif : QueryImpl unifSpec ProbComp :=
  HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)

def oraclePerm (g : X → X) : QueryImpl (X →ₒ X) ProbComp :=
  fun x => pure (g x)

def prpQueryImpl (g : X → X) : QueryImpl (PRPOracleSpec X) ProbComp :=
  oracleUnif + oraclePerm g

def prpRealExp (prp : PRPScheme K X) (adversary : PRPAdversary X) :
    ProbComp Bool :=
    sorry

def prpIdealExp [SampleableType (Equiv.Perm X)] (adversary : PRPAdversary X) :
    ProbComp Bool := do
  let π ← $ᵗ (Equiv.Perm X)
  simulateQ (prpQueryImpl fun x => π x) adversary

noncomputable def prpAdvantage [SampleableType (Equiv.Perm X)]
    (prp : PRPScheme K X) (adversary : PRPAdversary X) : ℝ :=
    sorry


end PRPScheme

namespace PRFPRNGScheme

variable {S X R : Type}

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
