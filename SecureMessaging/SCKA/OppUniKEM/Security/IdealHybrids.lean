/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.OppUniKEM.Security.Endpoints
public import SecureMessaging.SCKA.Security.Hybrids
public import VCVio.ProgramLogic.Relational.SimulateQ.Coupling

/-!
# Ideal hybrids

Let `scka` be Opp-UniKEM (`scheme`) over a KEM `kem` with deterministic decapsulation and correct
erasure codes, and let `adv` be an SCKA adversary.

A *challenge mode* `μ : ℕ → Bool` decides which epochs' challenges get random keys: an eligible
challenge at `t` returns a uniform key if `μ t` and the real (recorded) key otherwise. The *ideal
game* `I_μ` (`idealSecurityExp … μ adv`, `Endpoints`) is the SCKA security game under `μ` without
decapsulation failures: A uses B's recorded key instead of decapsulating. The constant modes give
`I_false` (all keys real) and `I_true` (all keys uniform).

The *ideal hybrids* `H_i` (`idealEpochHybridExp … adv i`) switch from real to uniform keys one
epoch at a time. For `e > 0`, the *stopped hybrids* `S_e^real` and `S_e^random` are the adjacent
hybrids at `e`, returning `false` at the first exposure of `e`:

```text
H_i        := I_{μ_i},  μ_i(t) := (0 < t ≤ i)    -- uniform keys at epochs 1, …, i
S_e^real   := H_{e-1} stopped at e               -- real key at e
S_e^random := H_e     stopped at e               -- uniform key at e
```

The modes `μ_i` (`hybridMode i`), the endpoint identities for `H_0` and `H_q`, and the stopping
identity are generic (`SCKA.Security.Hybrids`). They apply because, for every challenge mode `μ`,
the ideal security oracles under `μ` are `SCKAScheme.modeImpl … μ`, the state-dependent security
oracles for the assignment that maps each game state `s` to the *ideal instance*: Opp-UniKEM in
which A's receive replaces decapsulation by B's recorded key `s.keyB s.stA.t` for A's current epoch.

Let `AdvGuess_SCKA(scka, adv) := |Pr[b' = b] - 1/2|` be the advantage of `adv` in guessing the
challenge bit `b` of the SCKA security game, and `ε` the KEM correctness error
(`kem.correctnessError`): the probability that an honest encapsulation does not decapsulate to its
key.

**Results.**

- If `adv` makes at most `q` ordinary or leaking sends of A and B together, on every response path
  (`SCKAScheme.SecuritySendQueryBound adv q`), then (`security_guess_le_hybrid_gap`)
  `AdvGuess_SCKA(scka, adv) ≤ |Pr[H_0 = true] - Pr[H_q = true]| / 2 + q · ε`.
- Stopping at the first exposure of `e` preserves the difference between adjacent hybrids
  (`idealEpochHybrid_signed_gap_stop_eq`, stated for `e = i + 1`):
  `Pr[S_e^random = true] - Pr[S_e^real = true] = Pr[H_e = true] - Pr[H_{e-1} = true]`.
-/

@[expose] public section

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security

variable {K PK SK C Sym : Type}
variable (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
  (hDet : kem.DeterministicDecaps)
variable (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
variable (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
variable (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
variable (leak : kem.OnOffRandLeak onoff)

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-! ### Send and epoch accounting -/

omit [SampleableType K] in
/-- Ideal correctness queries preserve `sendEpochInv`: A's epoch is at most its send count plus
one, and at most its send count when A holds a secret key. -/
private theorem idealCorrectnessImpl_preserves_sendEpochInv :
    QueryImpl.PreservesInv (idealCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak)
      sendEpochInv := by
  intro t s hs res hres
  rcases t with ((((n | u) | u) | n) | n)
  · rw [SCKAScheme.mem_support_oracleUnif_run n s res hres]; exact hs
  · exact oracleSendA_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak u s hs res hres
  · exact oracleSendB_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak u s hs res hres
  · exact oracleRecvAIdeal_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1
      leak n s hs res hres
  · exact oracleRecvB_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak n s hs res hres

/-- Every query of `idealSecurityImpl` preserves `sendEpochInv`. -/
private theorem idealSecurityImpl_preserves_sendEpochInv
    (mode : ℕ → Bool) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      sendEpochInv :=
  SCKAScheme.securityImplOf_preservesInv_of_book _ _ _ _ _ sendEpochInv (fun _ _ _ h => h)
    (sendArleak_forget kem onoff ecEk leak) (sendBrleak_forget kem onoff ecCt0 ecCt1 leak)
    (SCKAScheme.challOf_recordsChallenges _)
    (idealCorrectnessImpl_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (oracleSendA_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (oracleSendB_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak)

include hEk hCt0 hCt1 in
/-- Assuming correct erasure codes, every ideal security query preserves consistency with a
protocol transcript (`reachableInv`). -/
private theorem idealSecurityImpl_preserves_reachableInv (mode : ℕ → Bool) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      (reachableInv kem onoff ecEk ecCt0 ecCt1) :=
  SCKAScheme.securityImplOf_preservesInv_of_book _ _ _ _ _ _
    (fun _ E C h => reachableInv_with_security_bookkeeping h E C)
    (sendArleak_forget kem onoff ecEk leak) (sendBrleak_forget kem onoff ecCt0 ecCt1 leak)
    (SCKAScheme.challOf_recordsChallenges _)
    (idealCorrectnessImpl_preserves_reachableInv kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak)
    (oracleSendA_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1 leak ecEk.ec.nchunk_pos)
    (oracleSendB_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt0.ec.nchunk_pos
      ecCt1 ecCt1.ec.nchunk_pos leak)

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] in
/-- In a transcript-consistent state (`reachableInv`) satisfying `sendEpochInv`, every epoch `t`
with a recorded key satisfies `0 < t ≤ nA + nB`. -/
private theorem recorded_epoch_pos_le (s : GameState onoff Sym)
    (hr : reachableInv kem onoff ecEk ecCt0 ecCt1 s) (he : sendEpochInv s) (t : ℕ)
    (hk : (s.keyA t).isSome ∨ (s.keyB t).isSome) : 0 < t ∧ t ≤ s.nA + s.nB := by
  have htq := recorded_epoch_le_sends hr he t hk
  obtain ⟨T, hT⟩ := hr
  have hzeroA : s.keyA 0 = none := by simp [hT.keyA]
  have htpos : 0 < t := Nat.pos_of_ne_zero fun ht => by
    simp [ht, hzeroA, hT.keyB_zero] at hk
  exact ⟨htpos, by omega⟩

/-! ### Hybrids -/

include hDet in
/-- The ideal instance at the game state `s`: Opp-UniKEM in which A's receive outputs B's recorded
key `s.keyB s.stA.t` for A's current epoch instead of decapsulating. -/
private abbrev idealSchemeOf (s : GameState onoff Sym) :=
  schemeWithDecaps kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ _ => s.keyB s.stA.t)

/-- The ideal security oracles under `mode` are the state-dependent security oracles over the
ideal instance: `idealSecurityImpl mode = modeImpl idealSchemeOf (exposureA …) (exposureB …) mode`
(`SCKA.Security.Hybrids`). -/
private theorem idealSecurityImpl_eq_modeImpl (mode : ℕ → Bool) :
    idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode =
      SCKAScheme.modeImpl (idealSchemeOf kem onoff hDet ecEk ecCt0 ecCt1 leak)
        (exposureA kem onoff leak) (exposureB kem onoff leak) mode := by
  funext t
  apply StateT.ext
  intro s
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n) <;> rfl
  all_goals rfl

include hDet in
/-- Oracles of the ideal hybrid `H_i`: the ideal security oracles answering eligible
challenges at epochs `1, …, i` with uniform keys and later ones with recorded keys, that is,
`idealSecurityImpl` under the challenge mode `hybridMode i`. -/
abbrev idealEpochHybridImpl (i : ℕ) :=
  idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (SCKAScheme.hybridMode i)

include hDet in
/-- The ideal hybrid `H_i`: `adv` run from the initial game state against the ideal security
oracles that answer eligible challenges at epochs `1, …, i` with uniform keys and later ones with
recorded keys (`idealEpochHybridImpl … i`). -/
def idealEpochHybridExp
    (adv : SecurityAdversary leak Sym) (i : ℕ) : ProbComp Bool :=
  idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1 leak (SCKAScheme.hybridMode i) adv

include hDet in
/-- Run the ideal hybrid `H_i` from the initial state, returning `false` at exposure of `e`. -/
def stoppedHybridExp (adv : SecurityAdversary leak Sym) (i e : ℕ) : ProbComp Bool :=
  stoppedRun (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak i)
    (fun s => decide (e ∈ s.exposed)) adv (Reduction.Internal.initialGame kem onoff)

/-- The initial hybrid `idealEpochHybridExp … 0` (`H_0`) coincides with the real-key ideal game
`idealSecurityExp … (fun _ => false) adv` (`I_false`) as a probabilistic computation. -/
theorem idealEpochHybridExp_zero
    (adv : SecurityAdversary leak Sym) :
    idealEpochHybridExp kem onoff hDet ecEk ecCt0 ecCt1 leak adv 0 =
      idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => false) adv := by
  simp only [idealEpochHybridExp, SCKAScheme.hybridMode_zero]

include hEk hCt0 hCt1 in
/-- Assuming the erasure codes are correct and `SCKAScheme.SecuritySendQueryBound adv q`, the final
hybrid `idealEpochHybridExp … q` (`H_q`) has the same acceptance probability as the random-key
ideal game `idealSecurityExp … (fun _ => true) adv` (`I_true`):
`Pr[H_q = true] = Pr[I_true = true]`. -/
theorem idealEpochHybridExp_last
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SCKAScheme.SecuritySendQueryBound adv q) :
    Pr{let x ← idealEpochHybridExp kem onoff hDet ecEk ecCt0 ecCt1 leak adv q}[x = true] =
      Pr{let x ← (idealSecurityExp
          kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => true) adv)}[x = true] := by
  simp only [idealEpochHybridExp, idealSecurityExp, idealSecurityImpl_eq_modeImpl]
  refine SCKAScheme.prEvent_hybridImpl_last_eq _ _ _
    (fun s => reachableInv kem onoff ecEk ecCt0 ecCt1 s ∧ sendEpochInv s) (fun mode => ?_)
    (fun s hs t hk => recorded_epoch_pos_le kem onoff ecEk ecCt0 ecCt1 s hs.1 hs.2 t hk)
    adv q hq (Reduction.Internal.initialGame kem onoff)
    ⟨reachableInv_initialGame kem onoff ecEk ecCt0 ecCt1, sendEpochInv_init kem onoff⟩
    (by simp [Reduction.Internal.initialGame, SCKAScheme.initGameState])
  rw [← idealSecurityImpl_eq_modeImpl]
  exact fun t s hs res hres =>
    ⟨idealSecurityImpl_preserves_reachableInv kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak
      mode t s hs.1 res hres,
    idealSecurityImpl_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak mode t s hs.2
      res hres⟩

include hEk hCt0 hCt1 in
/-- Assuming the erasure codes are correct and `SCKAScheme.SecuritySendQueryBound adv q`, the SCKA
guessing advantage of `adv` is bounded by half the distance between the endpoint ideal hybrids
`H_0 := idealEpochHybridExp … 0` and `H_q := idealEpochHybridExp … q`, plus `q` times the KEM
correctness error `ε`:
`AdvGuess_SCKA(scka, adv) ≤ |Pr[H_0 = true] - Pr[H_q = true]| / 2 + q · ε`. -/
theorem security_guess_le_hybrid_gap
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SCKAScheme.SecuritySendQueryBound adv q) :
    SCKAScheme.sckaGuessAdvantage (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)
      adv (exposureA kem onoff leak) (exposureB kem onoff leak) ≤
    |(Pr{let x ← idealEpochHybridExp kem onoff hDet ecEk ecCt0 ecCt1 leak adv 0}[x = true]).toReal -
      (Pr{let x ← (idealEpochHybridExp
          kem onoff hDet ecEk ecCt0 ecCt1 leak adv q)}[x = true]).toReal| / 2 +
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal := by
  rw [idealEpochHybridExp_zero,
    idealEpochHybridExp_last kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak adv q hq,
    abs_sub_comm]
  exact SCKAScheme.sckaGuessAdvantage_le_of_abs_sub_le _ adv _ _
    (fun b => (Pr{let x ← (idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1
      leak (fun _ => b) adv)}[x = true]).toReal) _
    fun b => security_correctness_endpoint_le kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak b adv q hq

/-! ### Stopping at exposure -/

/-- From any state `s` satisfying `Disjoint s.exposed s.challenged`, stopping at the first exposure
of epoch `i + 1` preserves the difference in acceptance probability between the adjacent ideal
hybrids `idealEpochHybridImpl … (i + 1)` (`H_{i+1}`) and `idealEpochHybridImpl … i` (`H_i`). -/
theorem idealEpochHybrid_signed_gap_stop_eq
    (i : ℕ) (adv : SecurityAdversary leak Sym)
    (s : GameState onoff Sym)
    (hs : Disjoint s.exposed s.challenged) :
    (Pr{let x ← ((simulateQ
      (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (i + 1)) adv).run'
        s)}[x = true]).toReal -
    (Pr{let x ← ((simulateQ
      (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak i) adv).run'
        s)}[x = true]).toReal =
    (Pr{let x ← (stoppedRun
      (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (i + 1))
      (fun u => decide (i + 1 ∈ u.exposed)) adv s)}[x = true]).toReal -
    (Pr{let x ← (stoppedRun
      (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak i)
      (fun u => decide (i + 1 ∈ u.exposed)) adv s)}[x = true]).toReal := by
  simp only [idealEpochHybridImpl, idealSecurityImpl_eq_modeImpl]
  exact SCKAScheme.hybridImpl_signed_gap_stop_eq _ _ _ i adv s hs

end oppUniKemCKA.Security
