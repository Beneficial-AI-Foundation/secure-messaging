/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.FromAEADPRG.Security.Transfer
public import ToVCVio.OracleComp.Constructions.SampleableType

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

/-! ## Hybrid chains -/

/-- The chain that takes step `q` from the table `U` if `U q` is defined, and applies the PRG to
the previous seed otherwise. -/
def hybGen (prg : PRGScheme W (W × Kae)) (U : ℕ → Option (W × Kae)) : ℕ → W → W × Kae :=
  fun q w => (U q).getD (prg.gen w)

/-- `U` with the steps `1, …, j` sampled uniformly and no other steps. -/
def sampleTab [SampleableType W] [SampleableType Kae] : ℕ → ProbComp (ℕ → Option (W × Kae))
  | 0 => pure fun _ => none
  | n + 1 => do
    let U ← sampleTab n
    let u ← $ᵗ (W × Kae)
    pure (Function.update U (n + 1) (some u))

/-- Let two chains take the same step at position `j ≥ 1` and agree at every later position. Then
from position `j` on they have the same seeds and the same keys. -/
theorem chain_eq_of_ge (G₁ G₂ : ℕ → W → W × Kae) (k₁ k₂ : W) (j : ℕ) (hj : 1 ≤ j)
    (hstep : G₁ j (chainState G₁ k₁ (j - 1)) = G₂ j (chainState G₂ k₂ (j - 1)))
    (hgt : ∀ q, j < q → G₁ q = G₂ q) (q : ℕ) (hq : j ≤ q) :
    chainState G₁ k₁ q = chainState G₂ k₂ q ∧ chainKey G₁ k₁ q = chainKey G₂ k₂ q := by
  induction q, hq using Nat.le_induction with
  | base =>
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact ⟨congrArg Prod.fst hstep, congrArg Prod.snd hstep⟩
  | succ q hq ih =>
    have h : G₁ (q + 1) (chainState G₁ k₁ q) = G₂ (q + 1) (chainState G₂ k₂ q) := by
      rw [hgt (q + 1) (by omega), ih.1]
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- A step from the table: if `U q = (w, K)` with `q ≥ 1`, the chain has seed `w` and key `K` at
`q`. -/
theorem chain_hybGen_of_some (prg : PRGScheme W (W × Kae)) (U : ℕ → Option (W × Kae)) (k : W)
    {q : ℕ} (hq : 1 ≤ q) {u : W × Kae} (hU : U q = some u) :
    chainState (hybGen prg U) k q = u.1 ∧ chainKey (hybGen prg U) k q = u.2 := by
  obtain ⟨i, rfl⟩ : ∃ i, q = i + 1 := ⟨q - 1, by omega⟩
  simp only [chainState, chainKey, hybGen, hU, Option.getD_some, Nat.add_sub_cancel, and_self]

/-- Let two chains agree at every position up to `m`. Then up to `m` they have the same seeds and
the same keys. -/
theorem chain_eq_of_le (G₁ G₂ : ℕ → W → W × Kae) (k : W) (m : ℕ)
    (hle : ∀ q, q ≤ m → G₁ q = G₂ q) (q : ℕ) (hq : q ≤ m) :
    chainState G₁ k q = chainState G₂ k q ∧ chainKey G₁ k q = chainKey G₂ k q := by
  induction q with
  | zero => exact ⟨rfl, by simp only [chainKey, Nat.zero_sub, chainState_zero, hle 0 hq]⟩
  | succ q ih =>
    have h := ih (by omega)
    have h' : G₁ (q + 1) (chainState G₁ k q) = G₂ (q + 1) (chainState G₂ k q) := by
      rw [hle (q + 1) hq, h.1]
    exact ⟨congrArg Prod.fst h', by simp only [chainKey, Nat.add_sub_cancel, h']⟩

/-- The chains with step `(w, κ)` and `(w, K)` at position `j` have the same seeds. -/
theorem chainState_update_key (prg : PRGScheme W (W × Kae)) (U : ℕ → Option (W × Kae)) (j : ℕ)
    (w : W) (κ K : Kae) (k : W) (q : ℕ) :
    chainState (hybGen prg (Function.update U j (some (w, κ)))) k q =
      chainState (hybGen prg (Function.update U j (some (w, K)))) k q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [chainState, ih, hybGen]
    by_cases hq : q + 1 = j
    · subst hq
      simp only [Function.update_self, Option.getD_some]
    · simp only [Function.update_of_ne hq]

/-- The chains with step `(w, κ)` and `(w, K)` at position `j` have the same keys at every other
position. -/
theorem chainKey_update_key (prg : PRGScheme W (W × Kae)) (U : ℕ → Option (W × Kae)) (j : ℕ)
    (w : W) (κ K : Kae) (k : W) {q : ℕ} (hq : q ≠ j) :
    chainKey (hybGen prg (Function.update U j (some (w, κ)))) k q =
      chainKey (hybGen prg (Function.update U j (some (w, K)))) k q := by
  simp only [chainKey, chainState_update_key prg U j w κ K k, hybGen, Function.update_of_ne hq]

/-- A sampled table has no step above `n`. -/
theorem sampleTab_none [SampleableType W] [SampleableType Kae] (n : ℕ) :
    ∀ U ∈ support (sampleTab (W := W) (Kae := Kae) n), ∀ q, n < q → U q = none := by
  induction n with
  | zero =>
    intro U hU q _
    simp only [sampleTab, support_pure, Set.mem_singleton_iff] at hU
    subst hU
    rfl
  | succ n ih =>
    intro U hU q hq
    simp only [sampleTab, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hU
    obtain ⟨U', hU', u, -, rfl⟩ := hU
    rw [Function.update_of_ne (by omega)]
    exact ih U' hU' q (by omega)

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

/-- **The real world of a PRG step on the hybrid chain.** Let `R G k` depend on the chain `G` from
`k` only through the keys `K_q` for `q ≥ 1` and the seeds `w_q` for `q ≥ n + 1`. Then the chain
with uniform steps `1, …, n` and step `n + 1` equal to `G(s)` for a uniform seed `s` gives the
distribution of the chain with uniform steps `1, …, n`: the seed `w_n` of the second chain is
uniform like `s`. -/
theorem hybGen_prgReal_evalDistEq [SampleableType W] [SampleableType Kae]
    (prg : PRGScheme W (W × Kae)) (n : ℕ) {α : Type}
    (R : (ℕ → W → W × Kae) → W → ProbComp α)
    (hR : ∀ G₁ G₂ k₁ k₂, (∀ q, 1 ≤ q → chainKey G₁ k₁ q = chainKey G₂ k₂ q) →
      (∀ q, n + 1 ≤ q → chainState G₁ k₁ q = chainState G₂ k₂ q) → R G₁ k₁ = R G₂ k₂) :
    (do
      let s ← $ᵗ W
      let U ← sampleTab n
      let k ← $ᵗ W
      R (hybGen prg (Function.update U (n + 1) (some (prg.gen s)))) k) =ᵈ
    (do
      let U ← sampleTab n
      let k ← $ᵗ W
      R (hybGen prg U) k) := by
  cases n with
  | zero =>
    have hX (s k : W) :
        R (hybGen prg (Function.update (fun _ => none) 1 (some (prg.gen s)))) k =
          R (hybGen prg fun _ => none) s := by
      have h := chain_eq_of_ge (hybGen prg (Function.update (fun _ => none) 1
        (some (prg.gen s)))) (hybGen prg fun _ => none) k s 1 le_rfl
        (by simp only [hybGen, Function.update_self, Option.getD_some, Option.getD_none,
          Nat.sub_self, chainState_zero])
        (fun q hq => by
          funext w
          simp only [hybGen, Function.update_of_ne (Nat.ne_of_gt hq)])
      exact hR _ _ k s (fun q hq => (h q hq).2) (fun q hq => (h q hq).1)
    simp only [sampleTab, pure_bind, hX]
    exact EvalDistEq.bind_right _ fun s => EvalDistEq.bind_const (spec := unifSpec) _ _
  | succ m =>
    simp only [sampleTab, bind_assoc, pure_bind]
    refine (EvalDistEq.bind_bind_swap (spec := unifSpec) _ _ _).trans
      (EvalDistEq.bind_congr_of_support _ fun U' hU' => ?_)
    have hnone : U' (m + 2) = none := sampleTab_none m U' hU' (m + 2) (by omega)
    have hX (s : W) (u : W × Kae) (k : W) :
        R (hybGen prg (Function.update (Function.update U' (m + 1) (some u)) (m + 1 + 1)
          (some (prg.gen s)))) k =
        R (hybGen prg (Function.update U' (m + 1) (some (s, u.2)))) k := by
      set G₁ := hybGen prg (Function.update (Function.update U' (m + 1) (some u)) (m + 1 + 1)
        (some (prg.gen s)))
      set G₂ := hybGen prg (Function.update U' (m + 1) (some (s, u.2)))
      have h₁ := chain_hybGen_of_some prg (Function.update (Function.update U' (m + 1) (some u))
        (m + 1 + 1) (some (prg.gen s))) k (q := m + 1) (by omega) (u := u)
        (by rw [Function.update_of_ne (by omega), Function.update_self])
      have h₂ := chain_hybGen_of_some prg (Function.update U' (m + 1) (some (s, u.2))) k
        (q := m + 1) (by omega) (u := (s, u.2)) (Function.update_self _ _ _)
      have hlo := chain_eq_of_le G₁ G₂ k m fun q hq => by
        funext w
        simp only [G₁, G₂, hybGen, Function.update_of_ne (show q ≠ m + 1 by omega),
          Function.update_of_ne (show q ≠ m + 1 + 1 by omega)]
      have hhi := chain_eq_of_ge G₁ G₂ k k (m + 1 + 1) (by omega)
        (by
          simp only [Nat.add_sub_cancel, h₂.1, G₁, G₂, hybGen, Function.update_self,
            Option.getD_some, Function.update_of_ne (show m + 1 + 1 ≠ m + 1 by omega), hnone,
            Option.getD_none])
        (fun q hq => by
          funext w
          simp only [G₁, G₂, hybGen, Function.update_of_ne (show q ≠ m + 1 by omega),
            Function.update_of_ne (show q ≠ m + 1 + 1 by omega)])
      refine hR G₁ G₂ k k (fun q hq => ?_) (fun q hq => (hhi q hq).1)
      rcases Nat.lt_or_ge q (m + 1) with hq' | hq'
      · exact (hlo q (by omega)).2
      rcases Nat.lt_or_ge q (m + 1 + 1) with hq'' | hq''
      · obtain rfl : q = m + 1 := by omega
        rw [h₁.2, h₂.2]
      · exact (hhi q hq'').2
    simp only [hX]
    exact ToVCVio.uniformSample_prod_replace_fst fun v => do
      let k ← $ᵗ W
      R (hybGen prg (Function.update U' (m + 1) (some v))) k

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
