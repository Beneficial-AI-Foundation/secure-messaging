/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.FromAEADPRG.Security.Authenticity.Transfer
public import SecureMessaging.FSAEAD.FromAEADPRG.Security.Chain.Hybrid

/-!
# FS-AEAD from AEAD and PRG — the hybrid games

Let `prg` be the PRG `G : W → W × Kae`. The hybrid `H_j` is `G_auth^0` for the chain whose steps
`1, …, j` are independent uniform pairs `(w_q, K_q)`, sampled before the game, and whose later
steps apply `G` to the previous seed. A table `U : ℕ → Option (W × Kae)` holds the uniform steps,
and `hybGen prg U q w = U q` if it is defined, and `G(w)` otherwise. The sender, the receiver and
every retry read the same table.

`H_0` is `G_auth^0` for the construction `fromAEADPRG ae prg` (`hybExp_zero`).

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

/-! ## Hybrid games and the PRG reductions -/

/-- `winIn lo hi h`: the first win of the history `h` is at an index `p` with `lo ≤ p ≤ hi`. -/
def winIn (lo hi : ℕ) (h : AuthHist) : Bool :=
  match h.firstWin with
  | some p => decide (lo ≤ p ∧ p ≤ hi)
  | none => false

/-- A first win in `[lo, hi]` is a first win at an index `p ≥ lo`. -/
theorem exists_of_winIn {lo hi : ℕ} {h : AuthHist} (hw : winIn lo hi h = true) :
    ∃ p, h.firstWin = some p ∧ lo ≤ p := by
  unfold winIn at hw
  split at hw
  · rename_i p hp
    exact ⟨p, hp, (of_decide_eq_true hw).1⟩
  · exact absurd hw Bool.false_ne_true

variable [DecidableEq AD] [DecidableEq Cae]

/-- The hybrid `H_j` with `O-Corr-A^s`: `G_auth^s` for the chain with uniform steps `1, …, j`. -/
def hybExp [SampleableType W] [SampleableType Kae] (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (prg : PRGScheme W (W × Kae)) (len : M → ℕ) (s : ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (j : ℕ) :
    ProbComp (Bool × (CState W Kae AD M Cae × AuthHist)) := do
  let U ← sampleTab j
  authExp ae (hybGen prg U) len s adversary

/-- `H_0` with cutoff `s` is `G_auth^s` for the construction `fromAEADPRG ae prg`, whose chain
applies the PRG at every step. -/
theorem hybExp_zero [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (s : ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :
    hybExp ae prg len s adversary 0 = authExp ae (fun _ => prg.gen) len s adversary := by
  simp only [hybExp, sampleTab, pure_bind]
  rfl

/-- **The PRG reduction `P_{n+1}`.** On input `y`, it samples the steps `1, …, n`, takes `y` as
step `n + 1`, and runs `G_auth^{n+1}`. It outputs whether the first win is at an index in
`[n + 1, L]`. It never needs the seed `w_n`: `O-Corr-A^{n+1}` reveals no seed below `n + 1`, and
`O-Corr-B^⊥` reveals none. -/
def prgRed [SampleableType W] [SampleableType Kae] (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (prg : PRGScheme W (W × Kae)) (len : M → ℕ) (L : ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (n : ℕ) :
    PRGScheme.PRGAdversary (W × Kae) := fun y => do
  let U ← sampleTab n
  let z ← authExp ae (hybGen prg (Function.update U (n + 1) (some y))) len (n + 1) adversary
  pure (winIn (n + 1) L z.2.2)

/-- In every hybrid `H_i`, the cutoffs `j` and `0` give a first win in `[j, L]` the same
probability: a corruption of A below `j` excludes such a win. -/
theorem prEvent_hybExp_eq_low [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (j i L : ℕ) :
    Pr{let z ← hybExp ae prg len j adversary i}[winIn j L z.2.2 = true] =
      Pr{let z ← hybExp ae prg len 0 adversary i}[winIn j L z.2.2 = true] := by
  refine prEvent_bind_congr _ _ _ _ _ fun U => prEvent_bind_congr _ _ _ _ _ fun k =>
    prEvent_bind_congr _ _ _ _ _ fun b => ?_
  exact (prEvent_authRun_eq_low ae _ len b j adversary k _ fun h hw => exists_of_winIn hw).symm

/-- **The ideal world of `P_{n+1}`** is the hybrid `H_{n+1}`. -/
theorem prgIdeal_prgRed [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (L : ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (n : ℕ) :
    Pr{let x ← PRGScheme.prgIdealExperiment (prgRed ae prg len L adversary n)}[x = true] =
      Pr{let z ← hybExp ae prg len 0 adversary (n + 1)}[winIn (n + 1) L z.2.2 = true] := by
  rw [← prEvent_hybExp_eq_low, ← prEvent_map (hybExp ae prg len (n + 1) adversary (n + 1))
    (fun z => winIn (n + 1) L z.2.2) (· = true)]
  refine EvalDistEq.prEvent_eq ?_ _
  simp only [PRGScheme.prgIdealExperiment, prgRed, hybExp, sampleTab, bind_assoc, map_bind,
    bind_pure_comp, bind_map_left]
  exact EvalDistEq.bind_bind_swap (spec := unifSpec) _ _ _

/-- **The real world of `P_{n+1}`** is `H_n` on a first win in `[n + 1, L]`. The real world takes
step `n + 1` from an independent seed `s` instead of `w_n`. `G_auth^{n+1}` reveals no seed below
`n + 1`, so both chains give the history the same distribution (`authRun_map_normSt`), and
`w_n` is uniform like `s` (`hybGen_prgReal_evalDistEq`). -/
theorem prgReal_prgRed [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (L : ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (n : ℕ) :
    Pr{let x ← PRGScheme.prgRealExperiment prg (prgRed ae prg len L adversary n)}[x = true] =
      Pr{let z ← hybExp ae prg len 0 adversary n}[winIn (n + 1) L z.2.2 = true] := by
  rw [← prEvent_hybExp_eq_low, ← prEvent_map (hybExp ae prg len (n + 1) adversary n)
    (fun z => winIn (n + 1) L z.2.2) (· = true)]
  refine EvalDistEq.prEvent_eq ?_ _
  simp only [PRGScheme.prgRealExperiment, prgRed, hybExp, authExp, map_bind, bind_pure_comp]
  exact hybGen_prgReal_evalDistEq prg n (fun G k => do
      let b ← $ᵗ Bool
      (fun z => winIn (n + 1) L z.2.2) <$> authRun ae G len b (n + 1) adversary k)
    fun G₁ G₂ k₁ k₂ hk hs => by
      congr 1
      funext b
      rw [← authRun_map_normSt ae G₁ G₂ k₁ k₂ len b (n + 1) hk hs adversary, Functor.map_map]
      rfl

end FromAEADPRG

end FSAEADScheme
