/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.Quantitative.SendStep
import SecureMessaging.SCKA.OppBiKEM.Correctness.MainInvariant.SendTotal

/-!
# Opp-BiKEM-CKA — Reduction to KEM correctness

Let:

* `Π := scheme kem hDet ecEk ecCt leak` be the Opp-BiKEM-CKA SCKA scheme;
* `G(Adv) := SCKAScheme.correctnessExp Π Adv` be the outcome of its correctness experiment
  for an adversary `Adv`;
* `ε := kem.correctnessError` be the KEM's correctness error;
* `φ(pk, sk) := keypairFailure kem hDet pk sk` (`KEM.CorrectnessError`) be the correctness
  error after fixing the key pair `(pk, sk)`, over the remaining encapsulation to `pk`;
* `E_X[f] := Pr[X = ⊥] + Σ x, Pr[X = x] · f x` be the expected payoff of `f` under a
  computation `X` (`expectedPayoff`).

  In our context, the payoff `f x` is a failure probability, so `E_X[f]` is the probability
  that `X` fails directly (charged `1`) or returns an `x` that fails later (probability `f x`).

## Main results

Assume that `kem` has deterministic decapsulation and that `ecEk` and `ecCt` are correct. If
the adversary `Adv` makes at most `q` send queries (`SendQueryBound Adv q`), then

* `correctness_failure_le`: `Pr[G(Adv) = false] ≤ q · ε`;
* `correctness_true_ge`: `Pr[G(Adv) = true] ≥ 1 - q · ε`;
* `correctness_of_perfectKEM'`: `Pr[G(Adv) = true] = 1` if `kem` is perfectly correct.

Moreover, `sends_never_rejected_of_noFailure`: on every reachable tracked state whose failure
flag is clear, neither party's send is rejected.

The proof has four parts.

## Tracked game and tracked invariant (`SCKA.Correctness.Tracked`, `Quantitative.Core`)

The tracked execution augments each ordinary game state with a failure flag. Its states are
pairs `(s, b)`, where `s` is a correctness-game state and `b` records whether a KEM instance
has completed inconsistently so far.

The tracked execution uses:

* `bad s := kemFailure hDet s` — a Boolean predicate on correctness-game states. It is `true`
  iff, for one of the two parties `P` with peer `P'`, the KEM instance of the peer's current
  responder epoch `e` is complete and inconsistent:

  ```text
  P.req.dk.lookup e   = some sk      (e := P'.res.resEpoch)
  P'.res.ct           = some c
  keyP' e             = some k       (keyP' the game key table of P')
  decaps sk c         ≠ some k
  ```

* `Ô := trackedBiKem kem hDet ecEk ecCt leak` — the tracked query handler: it runs the
  ordinary query and sets the flag if the resulting state is bad:

  ```text
  Run o s := ((SCKAScheme.sckaCorrectnessImpl Π) o).run s

  Ô o (s, b) := do
    (r, s') ← Run o s
    return (r, (s', b ∨ bad s'))
  ```

* `J := trackedInv (GameInv kem ecEk ecCt) (kemFailure hDet)` — the tracked invariant: either
  the flag is set, or `s` satisfies the main invariant and is not bad:

  ```text
  J (s, b) := b = true ∨ (GameInv s ∧ bad s = false)
  ```

`J` holds initially (`trackedInv_init`) and is preserved by `Ô` (`trackedBiKem_preservesInv`):
on a state that is not bad, every transcript consistent with it is decapsulation-ready
(`decapsReady_of_noFailure`), which is the only KEM fact the receive step of the main
invariant uses.

## Failure potential (`Quantitative.Core`)

On invariant states a party retains at most one secret key (`PartyInv.dk_shape`), and the
public key `pk` of its epoch is available, as the peer's decoded copy or as the party's own
retained copy (`pendingKey_available`). For a game state `s` and a flag `b`, define:

* `V(s) := failurePotential hDet s`, the conditional probability that a KEM instance in
  progress completes inconsistently, summed over both parties `P` and over the secret keys
  `(e, sk)` that `P` retains:

  ```text
  V s := Σ_P Σ_{(e, sk) ∈ P.req.dk} pendingTerm (e, sk)

  pendingTerm (e, sk) := φ (pk, sk)   while the peer's key table has no entry at e
                         0            once it has (the peer has encapsulated to e)
  ```

* `S(s, b) := trackedScore hDet (s, b)`, equal to `1` when `b = true` and to `V(s)`
  otherwise:

  ```text
  S (s, b) := if b then 1 else V s
  ```

The initial tracked state has score `0` (`trackedScore_init`).

## One step (`Quantitative.SendStep`, `Quantitative.RecvStep`, `Quantitative.SendDist`)

For every oracle `o` and every tracked state `(s, b)` satisfying `J (s, b)`
(`tracked_step_score_le`):

```text
E_{Ô o (s, b)}[S] ≤ S (s, b) + ε      if o ∈ {SendA, SendB}
E_{Ô o (s, b)}[S] ≤ S (s, b)          otherwise.
```

A send samples only in two cases (`Quantitative.SendDist`). An *advance* draws a key pair
`(pk, sk)` and adds `φ(pk, sk)` to `V`; averaged over key generation this is at most `ε`. An
*encapsulation* to `pk` completes the pending instance: with probability at most `φ(pk, sk)`
the flag is set, otherwise the term `φ(pk, sk)` leaves `V`. Every other send, every receive,
and the uniform oracle change neither `V` nor `bad`.

## Composition (`SCKA.Correctness.Tracked`)

`tracked_bad_le` aggregates the one-query bounds over an adaptive adversary, whose later
queries may depend on earlier responses, by induction over its oracle-computation tree
(`SCKAScheme.tracked_bad_le_of_score_step`). For the final tracked state `(s_f, b_f)`:

```text
Pr[b_f = true] ≤ E[S (s_f, b_f)] ≤ S (initState, false) + q · ε = q · ε.
```

Since `J` holds on every reachable tracked state and `GameInv s` contains `s.correct = true`,
a final state with `correct = false` has `b_f = true`. Forgetting the flag recovers the
ordinary run (`SCKAScheme.correctness_failure_le_of_tracked_bad`), so
`Pr[G(Adv) = false] ≤ q · ε`.
-/

open OracleComp KEMScheme ENNReal

namespace oppBiKemCKA

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
  (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)

/-- The initial state of the Opp-BiKEM-CKA correctness game, built from both parties' initial
states. -/
abbrev initState : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) :=
  SCKAScheme.initGameState (initialState .A) (initialState .B)

omit [DecidableEq Sym] in
/-- The initial state is not bad: no party retains a secret key. -/
theorem kemFailure_init : kemFailure hDet (initState (PK := PK) (SK := SK) (C := C) (Sym := Sym)
    (K := K)) = false := by
  rw [kemFailure, Bool.or_eq_false_iff]
  constructor <;> exact kemFailureAt_eq_false_of hDet (Or.inl rfl)

omit [DecidableEq Sym] in
/-- The initial tracked state `(initState, false)` has score `0`: no party retains a secret
key. -/
theorem trackedScore_init :
    trackedScore hDet (initState (PK := PK) (SK := SK) (C := C) (Sym := Sym) (K := K), false)
      = 0 := by
  rw [trackedScore_false, failurePotential, pendingPotential_nil hDet rfl,
    pendingPotential_nil hDet rfl, add_zero]

include hEk hCt in
/-- The tracked handler `Ô` preserves the tracked invariant `J`: either the flag is set, or the
main invariant holds and the state is not bad. -/
theorem trackedBiKem_preservesInv :
    QueryImpl.PreservesInv (trackedBiKem kem hDet ecEk ecCt leak)
      (trackedInv (GameInv kem ecEk ecCt) (kemFailure hDet)) :=
  trackedImpl_preserves _ _ _ (gameInv_step_of_noFailure kem hDet ecEk ecCt hEk hCt leak)

omit [DecidableEq Sym] in
/-- The initial tracked state `(initState, false)` satisfies the tracked invariant `J`. -/
theorem trackedInv_init :
    trackedInv (GameInv kem ecEk ecCt) (kemFailure hDet)
      (initState (PK := PK) (SK := SK) (C := C) (Sym := Sym) (K := K), false) :=
  Or.inr ⟨gameInv_init kem ecEk ecCt _ _ (by simp [initA, init, initialState])
    (by simp [initB, init, initialState]), kemFailure_init kem hDet⟩

include hEk hCt in
/-- Against an adversary making at most `q` send queries, the tracked game run from
`(initState, false)` ends with the flag set with probability at most `q · ε`. -/
theorem tracked_bad_le (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    Pr[ fun z => z.2.2 = true |
        (simulateQ (trackedBiKem kem hDet ecEk ecCt leak) adv).run (initState, false)] ≤
      (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp :=
  SCKAScheme.tracked_bad_le_of_score_step (scheme kem hDet ecEk ecCt leak) (kemFailure hDet)
    (GameInv kem ecEk ecCt) (fun z => trackedScore hDet z)
    (kem.correctnessError ProbCompRuntime.probComp)
    (fun p hp => one_le_trackedScore_of_flag hDet p hp)
    (trackedBiKem_preservesInv kem hDet ecEk ecCt hEk hCt leak)
    (tracked_step_score_le kem hDet ecEk ecCt leak hEk hCt)
    adv q hq _ (trackedInv_init kem hDet ecEk ecCt) (trackedScore_init kem hDet)

include hEk hCt in
/-- Assume:

* `kem` has deterministic decapsulation;
* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` `SendA` and `SendB` queries combined.

Then the Opp-BiKEM-CKA correctness game fails with probability at most
`q · kem.correctnessError`. -/
theorem correctness_failure_le (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    Pr[= false | SCKAScheme.correctnessExp (scheme kem hDet ecEk ecCt leak) adv] ≤
      (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp :=
  SCKAScheme.correctness_failure_le_of_tracked_bad (scheme kem hDet ecEk ecCt leak)
    (kemFailure hDet) (GameInv kem ecEk ecCt) (fun _ hs => hs.1)
    (trackedBiKem_preservesInv kem hDet ecEk ecCt hEk hCt leak) adv _
    (trackedInv_init kem hDet ecEk ecCt) (correctnessExp_eq_map kem hDet ecEk ecCt leak adv) _
    (tracked_bad_le kem hDet ecEk ecCt hEk hCt leak adv q hq)

include hEk hCt in
/-- Assume:

* `kem` has deterministic decapsulation;
* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` `SendA` and `SendB` queries combined.

Then the Opp-BiKEM-CKA correctness game succeeds with probability at least
`1 - q · kem.correctnessError`. -/
theorem correctness_true_ge (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    Pr[= true | SCKAScheme.correctnessExp (scheme kem hDet ecEk ecCt leak) adv] ≥
      1 - (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp := by
  have h := correctness_failure_le kem hDet ecEk ecCt hEk hCt leak adv q hq
  rw [probOutput_false_eq_sub, probFailure_eq_zero, tsub_zero, tsub_le_iff_right] at h
  rw [ge_iff_le, tsub_le_iff_right]
  rwa [add_comm]

include hEk hCt in
/-- Assume:

* `kem` has deterministic decapsulation and is perfectly correct;
* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` `SendA` and `SendB` queries combined.

Then the Opp-BiKEM-CKA correctness game succeeds with probability one. This is the `ε = 0`
instance of `correctness_true_ge`; `correctness_of_perfectKEM` proves the same without a query
bound. -/
theorem correctness_of_perfectKEM' (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    Pr[= true | SCKAScheme.correctnessExp (scheme kem hDet ecEk ecCt leak) adv] = 1 := by
  have h := correctness_true_ge kem hDet ecEk ecCt hEk hCt leak adv q hq
  rw [(KEMScheme.correctnessError_eq_zero_iff_perfectlyCorrect kem ProbCompRuntime.probComp).mpr
    hkem, mul_zero, tsub_zero] at h
  exact le_antisymm probOutput_le_one h

include hEk hCt in
/-- Assume:

* `kem` has deterministic decapsulation;
* `ecEk` and `ecCt` are correct erasure codes;
* `z` is a reachable outcome of the tracked game run against `adv` from `(initState, false)`,
  with the failure flag clear.

Then neither `sendA` nor `sendB` can return `none` from the parties' states in `z`. With
`tracked_bad_le`, the final states admit a rejected send with probability at most `q · ε` when
`adv` makes at most `q` send queries. -/
theorem sends_never_rejected_of_noFailure
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (z : Bool × (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) × Bool))
    (hz : z ∈ support ((simulateQ (trackedBiKem kem hDet ecEk ecCt leak) adv).run
      (initState, false)))
    (hflag : z.2.2 = false) :
    none ∉ support (sendA kem ecEk ecCt z.2.1.stA) ∧
      none ∉ support (sendB kem ecEk ecCt z.2.1.stB) := by
  have hinv := simulateQ_run_preservesInv _ _
    (trackedBiKem_preservesInv kem hDet ecEk ecCt hEk hCt leak) adv _
    (trackedInv_init kem hDet ecEk ecCt) z hz
  rcases hinv with h | ⟨hs, -⟩
  · rw [hflag] at h; cases h
  · exact ⟨sendA_ne_none kem ecEk ecCt _ hs, sendB_ne_none kem ecEk ecCt _ hs⟩

end oppBiKemCKA
