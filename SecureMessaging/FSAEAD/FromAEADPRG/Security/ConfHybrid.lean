/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.FromAEADPRG.Security.ConfTransfer
public import ToVCVio.EvalDist.BoolDist
public import ToVCVio.EvalDist.Monad.Basic

/-!
# FS-AEAD from AEAD and PRG — the confidentiality hybrids and the PRG reductions

The hybrid `G_{v,u}^s` (`confHyb`) is `G_conf^s` for the chain with uniform steps `1, …, v` and
uniform challenge ciphertexts at the positions `1, …, u` (`randUpTo u`). It outputs the bit `b`,
the guess `b'` and the history. The hybrid `G_v` of the proof is `G_{v,v}^0`.

For an event `E` of the history, the confidentiality gap is
```text
confGap(Γ, E) = Pr_Γ[b = b' ∧ E] - Pr_Γ[E] / 2
```
A reduction for step `j` outputs `b = b'` if no corruption revealed a position below `j`, and a
fair coin otherwise (`coinOut`). It outputs `1` with probability
`confGap(Γ, no reveal below j) + 1/2` (`prEvent_coinOut_toReal`).

The PRG reduction `P'_{n+1}` (`confPrgRed`) takes `y` as step `n + 1` of the chain and plays
`G_{n+1, n}^{n+1}`. In the ideal world it plays `G_{n+1,n}`, and in the real world `G_{n,n} = G_n`
(`confGap_le_prgAdvantage`).

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the
  Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf
  — Theorem 5.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

namespace FSAEADScheme

namespace FromAEADPRG

variable {W Kae Cae AD M : Type}

/-- `LowExpo s h` is decidable. -/
instance (s : ℕ) (h : ConfHist) : Decidable (LowExpo s h) :=
  match he : h.expo with
  | none => isFalse fun ⟨r, hr, _⟩ => by rw [he] at hr; exact nomatch hr
  | some r =>
    if hrs : r < s then isTrue ⟨r, he, hrs⟩
    else isFalse fun ⟨r', hr', h'⟩ => by
      rw [he, Option.some.injEq] at hr'
      exact hrs (hr' ▸ h')

/-- Challenge modes with uniform ciphertexts at the positions `1, …, u` and real ones above. -/
def randUpTo (u : ℕ) : ℕ → ChalMode Kae := fun p => if p ≤ u then .rand else .real

/-- The confidentiality gap `Pr_Γ[b = b' ∧ E] - Pr_Γ[E] / 2` of a game `Γ` that outputs the bit
`b`, the guess `b'` and the history. -/
noncomputable def confGap (mx : ProbComp (Bool × Bool × ConfHist)) (E : ConfHist → Prop) : ℝ :=
  (Pr{let r ← mx}[r.1 = r.2.1 ∧ E r.2.2]).toReal - (Pr{let r ← mx}[E r.2.2]).toReal / 2

/-- The output of a reduction for step `j`: `b = b'` on runs without `LowExpo j`, and a fair coin
otherwise. -/
def coinOut (j : ℕ) (mx : ProbComp (Bool × Bool × ConfHist)) : ProbComp Bool := do
  let r ← mx
  let c ← $ᵗ Bool
  pure (if ¬LowExpo j r.2.2 then r.1 == r.2.1 else c)

/-- A reduction for step `j` outputs `1` with probability `confGap(Γ, no reveal below j) + 1/2`. -/
theorem prEvent_coinOut_toReal (j : ℕ) (mx : ProbComp (Bool × Bool × ConfHist)) :
    (Pr{let x ← coinOut j mx}[x = true]).toReal =
      confGap mx (fun h => ¬LowExpo j h) + 1 / 2 := by
  rw [coinOut, ToVCVio.prEvent_ite_uniformBool_toReal, confGap, OracleComp.prEvent_not_eq_one_sub,
    ENNReal.toReal_sub_of_le (prEvent_le_one _) ENNReal.one_ne_top, ENNReal.toReal_one]
  have h : Pr{let a ← mx}[¬LowExpo j a.2.2 ∧ (a.1 == a.2.1) = true] =
      Pr{let r ← mx}[r.1 = r.2.1 ∧ ¬LowExpo j r.2.2] :=
    prEvent_congr mx _ _ fun r => by simp only [beq_iff_eq, and_comm]
  rw [h]
  ring

variable [DecidableEq AD] [DecidableEq Cae] [LenSampleable Cae]

/-- **The hybrid `G_{v,u}^s`.** Uniform chain steps `1, …, v`, uniform challenge ciphertexts at
the positions `1, …, u`, and stop position `s`. It outputs `(b, b', history)`. -/
def confHyb [SampleableType W] [SampleableType Kae] (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (prg : PRGScheme W (W × Kae)) (len : M → ℕ) (clen : ℕ → ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (s v u : ℕ) :
    ProbComp (Bool × Bool × ConfHist) := do
  let U ← sampleTab v
  let k ← $ᵗ W
  let b ← $ᵗ Bool
  let z ← confRun ae (hybGen prg U) len clen (randUpTo u) (fun _ => false) s b adversary k
  pure (b, z.1, z.2.2)

/-- In every hybrid, `G_{v,u}^0` and `G_{v,u}^s` give the same probability to an event that implies
that no corruption revealed a position below `s`. -/
theorem prEvent_confHyb_eq_low [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (clen : ℕ → ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (s v u : ℕ) (X : Bool × Bool × ConfHist → Prop) (hX : ∀ r, X r → ¬LowExpo s r.2.2) :
    Pr{let r ← confHyb ae prg len clen adversary 0 v u}[X r] =
      Pr{let r ← confHyb ae prg len clen adversary s v u}[X r] := by
  refine prEvent_bind_congr _ _ _ _ _ fun U => prEvent_bind_congr _ _ _ _ _ fun k =>
    prEvent_bind_congr _ _ _ _ _ fun b => ?_
  simp only [bind_pure_comp, prEvent_map]
  exact prEvent_confRun_eq_low ae _ len clen _ _ b s adversary k _ fun z hz => hX _ hz

/-- In every hybrid, `G_{v,u}^0` and `G_{v,u}^s` have the same gap on runs where no corruption
revealed a position below `s`. -/
theorem confGap_confHyb_eq_low [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (clen : ℕ → ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (s v u : ℕ) :
    confGap (confHyb ae prg len clen adversary 0 v u) (fun h => ¬LowExpo s h) =
      confGap (confHyb ae prg len clen adversary s v u) (fun h => ¬LowExpo s h) := by
  rw [confGap, confGap, prEvent_confHyb_eq_low ae prg len clen adversary s v u _ fun r h => h.2,
    prEvent_confHyb_eq_low ae prg len clen adversary s v u _ fun r h => h]

/-! ## The PRG reductions -/

/-- **The PRG reduction `P'_{n+1}`.** On input `y`, it samples the steps `1, …, n`, takes `y` as
step `n + 1`, and plays `G_conf^{n+1}` with uniform challenge ciphertexts at the positions
`1, …, n`. It outputs `b = b'` if no corruption revealed a position below `n + 1`, and a fair coin
otherwise. It never needs the seed `w_n`: `O-Corr-A^{n+1}` and `O-Corr-B^{n+1}` reveal no seed
below `n + 1`. -/
def confPrgRed [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (clen : ℕ → ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (n : ℕ) : PRGScheme.PRGAdversary (W × Kae) := fun y =>
  coinOut (n + 1) (do
    let U ← sampleTab n
    let k ← $ᵗ W
    let b ← $ᵗ Bool
    let z ← confRun ae (hybGen prg (Function.update U (n + 1) (some y))) len clen (randUpTo n)
      (fun _ => false) (n + 1) b adversary k
    pure (b, z.1, z.2.2))

/-- **The ideal world of `P'_{n+1}`** is the hybrid `G_{n+1,n}^{n+1}`. -/
theorem prgIdeal_confPrgRed [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (clen : ℕ → ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (n : ℕ) :
    Pr{let x ← PRGScheme.prgIdealExperiment (confPrgRed ae prg len clen adversary n)}[x = true] =
      Pr{let x ← coinOut (n + 1) (confHyb ae prg len clen adversary (n + 1) (n + 1) n)}[
        x = true] := by
  refine EvalDistEq.prEvent_eq ?_ _
  simp only [PRGScheme.prgIdealExperiment, confPrgRed, coinOut, confHyb, sampleTab, bind_assoc,
    pure_bind]
  exact EvalDistEq.bind_bind_swap (spec := unifSpec) _ _ _

/-- The runs of `G_conf^s` with the same challenge modes on two chains with the same keys, and the
same seeds from `s` on, give the same bit, guess and history. -/
theorem map_confRun_eq_of_chain (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G₁ G₂ : ℕ → W → W × Kae) (k₁ k₂ : W) (len : M → ℕ) (clen : ℕ → ℕ) (u : ℕ) (s : ℕ)
    (b : Bool) (hkey : ∀ q, 1 ≤ q → chainKey G₁ k₁ q = chainKey G₂ k₂ q)
    (hseed : ∀ q, s ≤ q → chainState G₁ k₁ q = chainState G₂ k₂ q)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :
    (fun z => (b, z.1, z.2.2)) <$> confRun ae G₁ len clen (randUpTo u) (fun _ => false) s b
        adversary k₁ =
      (fun z => (b, z.1, z.2.2)) <$> confRun ae G₂ len clen (randUpTo u) (fun _ => false) s b
        adversary k₂ := by
  rw [← confRun_map_normSt ae G₁ G₂ k₁ k₂ len clen (randUpTo u) (randUpTo u) _ s b
    (fun _ => False) (fun q hq _ => hkey q hq) hseed ?_ (fun _ h => h.elim) adversary,
    Functor.map_map]
  · rfl
  · intro p
    unfold randUpTo
    split_ifs with hp
    · rfl
    · simp only [ChalMode.eff, hkey p (by omega)]

/-- **The real world of `P'_{n+1}`** is the hybrid `G_{n,n}^{n+1}`. -/
theorem prgReal_confPrgRed [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (clen : ℕ → ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (n : ℕ) :
    Pr{let x ← PRGScheme.prgRealExperiment prg (confPrgRed ae prg len clen adversary n)}[
        x = true] =
      Pr{let x ← coinOut (n + 1) (confHyb ae prg len clen adversary (n + 1) n n)}[x = true] := by
  refine EvalDistEq.prEvent_eq ?_ _
  let R : (ℕ → W → W × Kae) → W → ProbComp (Bool × Bool × ConfHist) := fun G k => do
    let b ← $ᵗ Bool
    (fun z => (b, z.1, z.2.2)) <$> confRun ae G len clen (randUpTo n) (fun _ => false) (n + 1) b
      adversary k
  let g : Bool × Bool × ConfHist → ProbComp Bool := fun r => coinOut (n + 1) (pure r)
  have h := hybGen_prgReal_evalDistEq prg n R fun G₁ G₂ k₁ k₂ hk hs => by
    simp only [R, map_confRun_eq_of_chain ae G₁ G₂ k₁ k₂ len clen n (n + 1) _ hk hs adversary]
  have e₁ : PRGScheme.prgRealExperiment prg (confPrgRed ae prg len clen adversary n) =
      (do
        let s ← $ᵗ W
        let U ← sampleTab n
        let k ← $ᵗ W
        R (hybGen prg (Function.update U (n + 1) (some (prg.gen s)))) k) >>= g := by
    simp only [PRGScheme.prgRealExperiment, confPrgRed, coinOut, R, g, bind_assoc, bind_pure_comp,
      pure_bind]
  have e₂ : coinOut (n + 1) (confHyb ae prg len clen adversary (n + 1) n n) =
      (do
        let U ← sampleTab n
        let k ← $ᵗ W
        R (hybGen prg U) k) >>= g := by
    simp only [coinOut, confHyb, R, g, bind_assoc, bind_pure_comp, pure_bind]
  rw [e₁, e₂]
  exact h.bind_left g

/-- **The PRG step.** The gap between `G_n` and `G_{n+1,n}` on runs where no corruption revealed
a position below `n + 1` is at most the advantage of `P'_{n+1}`. -/
theorem confGap_le_prgAdvantage [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (clen : ℕ → ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (n : ℕ) :
    |confGap (confHyb ae prg len clen adversary 0 n n) (fun h => ¬LowExpo (n + 1) h) -
        confGap (confHyb ae prg len clen adversary 0 (n + 1) n) (fun h => ¬LowExpo (n + 1) h)| ≤
      (prg.prgAdvantage (confPrgRed ae prg len clen adversary n)).toReal := by
  rw [confGap_confHyb_eq_low, confGap_confHyb_eq_low, PRGScheme.prgAdvantage,
    ToVCVio.toReal_boolDist_evalDist, prgReal_confPrgRed, prgIdeal_confPrgRed,
    prEvent_coinOut_toReal, prEvent_coinOut_toReal]
  exact le_of_eq (by ring_nf)

end FromAEADPRG

end FSAEADScheme
