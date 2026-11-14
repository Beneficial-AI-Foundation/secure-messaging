/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.Security.Hybrids
public import SecureMessaging.SCKA.SPQR.Security.Invariant
public import SecureMessaging.SCKA.SPQR.Correctness
public import ToVCVio.OracleComp.EvalDist
public import ToVCVio.OracleComp.SimSemantics.StateT.BadFlag

/-!
# The ideal game of SPQR and its correctness-error endpoints

Let `scka := scheme P auth sampleInitKey` be the SPQR scheme over parameters `P` whose four stream
decoders are sound for their erasure codes, `V := vuln P AuthState` the exposure policy of both
parties, and `adv` an SCKA adversary.
Every game below except the stopped hybrid, which takes `ik` as an argument, draws an initial key
`ik ← sampleInitKey`, runs `adv` from the initial game state `initState auth ik`, and returns its
output bit.

- For a challenge bit `b`, the *real game* `G_b` is the security game of `scka` with its
  challenge bit fixed to `b`: uniform keys for `true`, recorded keys for `false`
  (`securityExpFixedBit scka adv b V V`, oracles `realImpl b`).
- A *challenge mode* `μ : ℕ → Bool` decides which epochs' challenges get random keys: an eligible
  challenge at `t` returns a uniform key if `μ t` and the real (recorded) key otherwise. The
  *ideal game* `I_μ` (`idealExp μ adv`) is the security game under `μ` without decapsulation
  failures: the generator of an epoch outputs the key recorded by the encapsulator instead of the
  decapsulated key (`idealSchemeOf`, `idealImpl μ`). The constant modes give `I_false` (all keys
  real) and `I_true` (all keys uniform).
- The *ideal hybrids* `H_i := I_{μ_i}`, with `μ_i(t) := (0 < t ≤ i)` (`hybridMode i`), switch from
  real to uniform keys one epoch at a time; `H_0 = I_false`.
- For an initial key `ik` and an epoch `e`, the *stopped hybrid* `stoppedHybridExp adv i e ik` runs
  `adv` from `initState auth ik` against the oracles of `H_i` and returns `false` at the first
  query that exposes `e`. The hybrids adjacent at `e`, stopped at `e`, are
  `S_e^real := stoppedHybridExp adv (e - 1) e ik` and `S_e^random := stoppedHybridExp adv e e ik`
  (`Reduction.HybridGame`).

Let `AdvGuess_SCKA(scka, adv) := |Pr[b' = b] - 1/2|` be the advantage of `adv` in guessing the
challenge bit `b` of the SCKA security game, and `ε` the KEM correctness error
(`P.det.toKEM.correctnessError`): the probability that an honest encapsulation does not
decapsulate to its key.

**Results.** Assume that `adv` makes at most `q` ordinary and leaking sends on every response path
(`SecuritySendQueryBound adv q`).

- The real and ideal games differ in acceptance probability by at most the KEM correctness error
  accumulated over `q` sends: `|Pr[G_b = true] - Pr[I_b = true]| ≤ q · ε`
  (`security_correctness_endpoint_le`).
- The last hybrid accepts as often as the uniform-key game: `Pr[H_q = true] = Pr[I_true = true]`
  (`prEvent_idealExp_hybrid_last`).
- Hence `AdvGuess_SCKA(scka, adv) ≤ |Pr[H_0 = true] - Pr[H_q = true]| / 2 + q · ε`
  (`security_guess_le_hybrid_gap`).
- For either fixed challenge bit `b` and every initial key `ik`, the run of `adv` against the
  oracles of `G_b` from `initState auth ik` ends with a false correctness flag with probability at
  most `q · ε` (`correctness_failure_le_security`).

Every query of the ideal game preserves consistency with a protocol transcript (`Inv auth`,
`idealImpl_preservesInv`). In particular, no reachable state performs the authenticator update of
epoch `0`, so for every `U` the ideal game over `authAt auth 0 U` accepts as often as over `auth`,
for every stopping predicate (`prEvent_stoppedRun_idealImpl_authAt_zero`).
-/

@[expose] public section

open OracleSpec OracleComp ENNReal
open OracleComp.ProgramLogic

namespace SPQR

open Chunked

variable {P : SPQR.Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac) (sampleInitKey : ProbComp InitKey)
  (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
  (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2)

/-- The initial game state for the initial key `ik`. -/
def initState (ik : InitKey) : GameState P AuthState :=
  SCKAScheme.initGameState (initA P auth ik) (initB P auth ik)

/-- The invariant of the SPQR correctness proof (`SPQR.Correctness`): `Braid.CorrectnessInv` of
the translated state, and `Ct1AckInv`. -/
def CorrectnessInv (ik : InitKey) (s : GameState P AuthState) : Prop :=
  Braid.CorrectnessInv (P := P.toBraid) auth ik s.toBraid ∧ Ct1AckInv s

/-! ### The failure flag and score

The bound `|Pr[G_b = true] - Pr[I_b = true]| ≤ q · ε` tracks the failure potential of
`SPQR.Correctness` with a flag set once the potential reaches `1`.
-/

section Potential

variable [DecidableEq P.K] [DecidableEq P.EpochKey]

/-- The failure potential of the SPQR correctness proof: `Braid.failurePotential` of the
translated state. -/
noncomputable def failurePotential (s : GameState P AuthState) : ℝ≥0∞ :=
  Braid.failurePotential s.toBraid

open scoped Classical in
/-- The failure flag: `failurePotential s = 1`. -/
noncomputable def badPotential (s : GameState P AuthState) : Bool :=
  decide (failurePotential s = 1)

/-- The flag is unset exactly when the failure potential is not `1`. -/
private theorem badPotential_eq_false_iff (s : GameState P AuthState) :
    badPotential s = false ↔ failurePotential s ≠ 1 := by
  simp [badPotential]

/-- A state with the flag unset has a true correctness flag. -/
private theorem correct_of_badPotential_eq_false {s : GameState P AuthState}
    (h : badPotential s = false) : s.correct = true := by
  rw [badPotential_eq_false_iff] at h
  by_contra hc
  exact h (by simp [failurePotential, Braid.failurePotential, hc])

/-- The score of a tracked state: `1` once the flag is set, the failure potential otherwise. -/
noncomputable def trackedScore (p : GameState P AuthState × Bool) : ℝ≥0∞ :=
  if p.2 then 1 else failurePotential p.1

/-- The score is at most `1`. -/
private theorem trackedScore_le_one (p : GameState P AuthState × Bool) : trackedScore p ≤ 1 := by
  unfold trackedScore
  split_ifs
  · exact le_rfl
  · exact Braid.failurePotential_le_one _

/-- A state with its own flag scores its failure potential. -/
private theorem trackedScore_bad (s : GameState P AuthState) :
    trackedScore (s, badPotential s) = failurePotential s := by
  unfold trackedScore badPotential
  by_cases h : failurePotential s = 1 <;> simp [h]

/-- The failure potential ignores the exposed set. -/
private theorem failurePotential_exposed (s : GameState P AuthState) (exposed : Finset ℕ) :
    failurePotential { s with exposed := exposed } = failurePotential s := by
  cases s
  rfl

/-- The failure potential ignores the challenged set. -/
private theorem failurePotential_challenged (s : GameState P AuthState) (challenged : Finset ℕ) :
    failurePotential { s with challenged := challenged } = failurePotential s := by
  cases s
  rfl

/-- The failure potential of the initial game state is `0`. -/
private theorem failurePotential_initState (ik : InitKey) :
    failurePotential (initState auth ik) = 0 := by
  simp only [failurePotential, initState, toBraid_initGameState]
  simp [Braid.failurePotential, Braid.currentEpochFailure, Braid.pairFailure,
    SCKAScheme.initGameState, Braid.initA, Braid.initB,
    Braid.State.controlPosition, Braid.State.epoch]

/-- The flag is unset at the initial game state. -/
private theorem badPotential_initState (ik : InitKey) : badPotential
    (initState auth ik) = false := by
  rw [badPotential_eq_false_iff, failurePotential_initState]
  exact zero_ne_one

/-- The tracked invariant holds at the initial tracked state. -/
private theorem tracked_initState_inv (ik : InitKey) :
    trackedInv (CorrectnessInv auth ik) badPotential (initState auth ik, false) :=
  Or.inr ⟨⟨Or.inr ⟨_, Braid.transcriptConsistent_initGameState (P := P.toBraid) auth ik⟩,
    ct1AckInv_initGameState auth ik⟩, badPotential_initState auth ik⟩

end Potential

/-! ### Replacing an update that no reachable state performs -/

section UpdateAt

/-- From a state of another epoch than `t`, the leaking send over `authAt auth t U` is that over
`auth`: a send updates the authenticator only at the epoch of its state. -/
theorem sendRleakWith_authAt_of_ne (t : ℕ) (U : AuthState → AuthState)
    (ops : Ops P) {st : PartyState P AuthState} (h : st.epoch ≠ t) :
    sendRleakWith (authAt auth t U) ops st = sendRleakWith auth ops st := by
  cases st
  case headerReceived core dec =>
    simp only [PartyState.epoch] at h
    simp [sendRleakWith, authAt_update_of_ne auth t U _ h]
  all_goals rfl

/-- From a state of another epoch than `t`, the receive over `authAt auth t U` is that over
`auth`: a receive updates the authenticator only at the epoch of its state. -/
theorem recvWith_authAt_of_ne (t : ℕ) (U : AuthState → AuthState)
    (ops : Ops P) {st : PartyState P AuthState} (h : st.epoch ≠ t)
    (msg : Message P.Sym) :
    recvWith (authAt auth t U) ops st msg = recvWith auth ops st msg := by
  cases st
  case ekSentCt1Received core dec =>
    simp only [PartyState.epoch] at h
    obtain ⟨me, payload⟩ := msg
    cases payload
    case ct2 chunk =>
      by_cases hme : me = core.ep
      · subst hme
        simp [recvWith, recvCt2With, authAt_update_of_ne auth t U _ h]
      · simp only [recvWith, hme, ↓reduceIte]
        rcases Nat.lt_or_gt_of_ne hme with hlt | hgt
        · simp [recv, PartyState.epoch, hlt]
        · simp [recv, PartyState.epoch, hgt, not_lt.mpr hgt.le]
    all_goals rfl
  all_goals
    obtain ⟨me, payload⟩ := msg
    cases payload <;> rfl

/-- Under `Inv auth s`, both parties have positive epochs. -/
theorem Inv.epoch_pos {s : GameState P AuthState} (h : Inv auth s) (party : Bool) :
    0 < (s.stateAt party).epoch := by
  obtain ⟨⟨ik, T, hT⟩, -⟩ := h
  have := (Braid.TranscriptInv.pairBounds (P := P.toBraid) auth hT party).2.2.1
  simpa [PartyState.toBraid_epoch] using this

end UpdateAt

/-! ### The games -/

section Games

/-- The ideal instance at the game state `s`: the samplers of `scheme P auth sampleInitKey`,
with the second-stage receive at epoch `t` outputting the key recorded for the peer at `t`. -/
abbrev idealSchemeOf (s : GameState P AuthState) :=
  schemeWith auth (idealOps (Ops.real P) s) sampleInitKey

variable [DecidableEq P.EpochKey] [SampleableType P.EpochKey]

/-- The oracles of `G_b`: the state-dependent family with the constant instance
`scheme P auth sampleInitKey` and the challenge mode `fun _ => b`. -/
abbrev realImpl (b : Bool) :=
  SCKAScheme.modeImpl (fun _ : GameState P AuthState => scheme P auth sampleInitKey)
    (vuln P AuthState) (vuln P AuthState) (fun _ => b)

/-- The oracles of the ideal game with challenge mode `mode`. -/
abbrev idealImpl (mode : ℕ → Bool) :=
  SCKAScheme.modeImpl (idealSchemeOf auth sampleInitKey) (vuln P AuthState)
    (vuln P AuthState) mode

/-- The ideal game: `ik ← sampleInitKey`, then `adv` against `idealImpl mode` from
`initState auth ik`. -/
def idealExp (mode : ℕ → Bool) (adv : SecurityAdversary P AuthState) : ProbComp Bool := do
  let ik ← sampleInitKey
  (simulateQ (idealImpl auth sampleInitKey mode) adv).run' (initState auth ik)

/-- The stopped hybrid: `adv` run from `initState auth ik` against the oracles
`idealImpl (hybridMode i)` of the ideal hybrid `H_i`, returning `false` at the first query that
exposes `e`. -/
def stoppedHybridExp (adv : SecurityAdversary P AuthState) (i e : ℕ) (ik : InitKey) :
    ProbComp Bool :=
  stoppedRun (idealImpl auth sampleInitKey (SCKAScheme.hybridMode i))
    (fun s => decide (e ∈ s.exposed)) adv (initState auth ik)

/-- The security oracles of `G_b` are `realImpl b`. -/
private theorem sckaSecurityImpl_eq_realImpl (b : Bool) :
    SCKAScheme.sckaSecurityImpl b (vuln P AuthState) (vuln P AuthState)
      (scheme P auth sampleInitKey) = realImpl auth sampleInitKey b := by
  funext t s
  rw [SCKAScheme.sckaSecurityImpl_eq_securityImplOf]
  exact (SCKAScheme.securityImplAt_run (fun _ => scheme P auth sampleInitKey)
    (SCKAScheme.challOf fun _ => b) (vuln P AuthState) (vuln P AuthState) t s).symm

/-- `G_b` samples `ik ← sampleInitKey` and runs `adv` against `realImpl b` from
`initState auth ik`. -/
private theorem securityExpFixedBit_eq (b : Bool) (adv : SecurityAdversary P AuthState) :
    SCKAScheme.securityExpFixedBit (scheme P auth sampleInitKey) adv b
        (vuln P AuthState) (vuln P AuthState) =
      (do
        let ik ← sampleInitKey
        (simulateQ (realImpl auth sampleInitKey b) adv).run' (initState auth ik)) := by
  unfold SCKAScheme.securityExpFixedBit
  rw [sckaSecurityImpl_eq_realImpl]
  refine bind_congr fun ik => ?_
  rw [show (scheme P auth sampleInitKey).initA ik = pure (initA P auth ik) from rfl,
    show (scheme P auth sampleInitKey).initB ik = pure (initB P auth ik) from rfl,
    pure_bind, pure_bind, StateT.run'_eq, map_eq_bind_pure_comp]
  exact bind_congr fun res => rfl

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- Assuming sound stream decoders, every query of `realImpl b` preserves
`CorrectnessInv auth ik`. -/
private theorem realImpl_preserves_correctnessInv (ik : InitKey) (b : Bool) :
    QueryImpl.PreservesInv (realImpl auth sampleInitKey b) (CorrectnessInv auth ik) :=
  SCKAScheme.securityImplAt_preservesInv _ _ _ _ (CorrectnessInv auth ik)
    (fun _ X Y hs => ⟨hs.1.imp_right fun ⟨T, hT⟩ => ⟨T, hT.setFlags X Y⟩, hs.2⟩)
    (fun _ st => scheme_sendArleak_forget auth sampleInitKey st)
    (fun _ st => scheme_sendArleak_forget auth sampleInitKey st)
    (SCKAScheme.challOf_recordsChallenges _)
    (fun s hs t res hres => correctnessImpl_preserves_correctnessInv auth sampleInitKey
      hHdrSound hEkSound hCt1Sound hCt2Sound ik t s hs res hres)

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- Assuming sound stream decoders, every ideal security query preserves consistency with a
protocol transcript and the bound of the epochs by the send counters (`Inv auth`). -/
theorem idealImpl_preservesInv (mode : ℕ → Bool) :
    QueryImpl.PreservesInv (idealImpl auth sampleInitKey mode) (Inv auth) :=
  SCKAScheme.securityImplAt_preservesInv _ _ _ _ (Inv auth)
    (fun _ X Y hs => hs.with_bookkeeping auth X Y)
    (fun _ st => schemeWith_sendArleak_forget auth _ sampleInitKey st)
    (fun _ st => schemeWith_sendArleak_forget auth _ sampleInitKey st)
    (SCKAScheme.challOf_recordsChallenges _)
    (fun s hs t res hres => idealCorrectness_preserves_at auth sampleInitKey hHdrSound hEkSound
      hCt1Sound hCt2Sound (opsPossible_real) s hs t res hres)

/-- From a state with `Inv auth`, every ideal query over `authAt auth 0 U` is the query over
`auth`: both parties have positive epochs, so no transition updates the authenticator at `0`. -/
theorem idealImpl_authAt_zero_run_eq (U : AuthState → AuthState) (mode : ℕ → Bool)
    (q : (securitySpec P AuthState).Domain) (s : GameState P AuthState) (hs : Inv auth s) :
    (idealImpl (authAt auth 0 U) sampleInitKey mode q).run s =
      (idealImpl auth sampleInitKey mode q).run s := by
  have hA : s.stA.epoch ≠ 0 := (Inv.epoch_pos auth hs true).ne'
  have hB : s.stB.epoch ≠ 0 := (Inv.epoch_pos auth hs false).ne'
  apply SCKAScheme.securityImplAt_congr (R := fun {_} => Eq) (hrefl := fun _ => rfl)
  · exact fun _ => by
      simp only [idealSchemeOf, schemeWith, sendWith, sendRleakWith_authAt_of_ne auth 0 U _ hA]
  · exact fun _ => by
      simp only [idealSchemeOf, schemeWith, sendWith, sendRleakWith_authAt_of_ne auth 0 U _ hB]
  · intro n _ ρ tsnd _
    simp only [idealSchemeOf, schemeWith, recvSCKAWith, recvWith_authAt_of_ne auth 0 U _ hA]
  · intro n _ ρ tsnd _
    simp only [idealSchemeOf, schemeWith, recvSCKAWith, recvWith_authAt_of_ne auth 0 U _ hB]
  · exact fun _ => SCKAScheme.oracleSendArleak_run_congr _ _ _ s (by
      simp only [idealSchemeOf, schemeWith, sendRleakWith_authAt_of_ne auth 0 U _ hA])
  · exact fun _ => SCKAScheme.oracleSendBrleak_run_congr _ _ _ s (by
      simp only [idealSchemeOf, schemeWith, sendRleakWith_authAt_of_ne auth 0 U _ hB])

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- Assuming sound stream decoders, replacing the update of `auth` at epoch `0` does not change
the acceptance probability of a stopped ideal game from `initState auth ik`: no reachable state
has epoch `0`. -/
theorem prEvent_stoppedRun_idealImpl_authAt_zero (U : AuthState → AuthState) (mode : ℕ → Bool)
    (stop : GameState P AuthState → Bool) (adv : SecurityAdversary P AuthState) (ik : InitKey) :
    Pr{let x ← (stoppedRun (idealImpl (authAt auth 0 U) sampleInitKey mode) stop adv
      (initState (authAt auth 0 U) ik))}[x = true] =
    Pr{let x ← (stoppedRun (idealImpl auth sampleInitKey mode) stop adv
      (initState auth ik))}[x = true] :=
  prEvent_stoppedRun_eq_of_query_eq _ _ stop (Inv auth)
    (idealImpl_preservesInv auth sampleInitKey hHdrSound hEkSound hCt1Sound hCt2Sound mode)
    (fun q s hs => idealImpl_authAt_zero_run_eq auth sampleInitKey U mode q s hs) adv _
    (Inv_initGameState auth ik)

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- Assuming sound stream decoders and `SecuritySendQueryBound adv q`, the last ideal hybrid
`H_q := idealExp (hybridMode q) adv` has the acceptance probability of the uniform-key ideal game
`I_true := idealExp (fun _ => true) adv`. -/
theorem prEvent_idealExp_hybrid_last (adv : SecurityAdversary P AuthState) (q : ℕ)
    (hq : SCKAScheme.SecuritySendQueryBound adv q) :
    Pr{let x ← idealExp auth sampleInitKey (SCKAScheme.hybridMode q) adv}[x = true] =
      Pr{let x ← idealExp auth sampleInitKey (fun _ => true) adv}[x = true] := by
  simp only [idealExp, map_bind]
  refine OracleComp.prEvent_bind_congr_of_support _ _ _ fun ik _ => ?_
  exact SCKAScheme.prEvent_hybridImpl_last_eq _ _ _ (Inv auth)
    (idealImpl_preservesInv auth sampleInitKey hHdrSound hEkSound hCt1Sound hCt2Sound)
    (fun s hs t hk => hs.keys_le_sends auth t hk) adv q hq (initState auth ik)
    (Inv_initGameState auth ik) rfl

/-! ### The correctness-error endpoints -/

section Endpoints

variable [DecidableEq P.K]

include hCt2Sound in
/-- Let `CorrectnessInv auth ik s` hold and the failure flag be unset at `s`. Then `realImpl b` and
`idealImpl (fun _ => b)` answer every query from `s` by equal response/state computations. -/
private theorem realImpl_run_eq_ideal (ik : InitKey) (b : Bool)
    (t : (securitySpec P AuthState).Domain) (s : GameState P AuthState)
    (hs : CorrectnessInv auth ik s) (hflag : badPotential s = false) :
    (realImpl auth sampleInitKey b t).run s =
      (idealImpl auth sampleInitKey (fun _ => b) t).run s := by
  have hpot : failurePotential s ≠ 1 := (badPotential_eq_false_iff s).mp hflag
  have hcorrect := correct_of_badPotential_eq_false hflag
  obtain ⟨T, hT⟩ := hs.1.resolve_left (by simp [hcorrect])
  have hcur : Braid.currentEpochFailure s.toBraid ≠ 1 := by
    simpa [failurePotential, Braid.failurePotential, hcorrect] using hpot
  have hdec := Braid.decaps_eq_of_currentEpochFailure_ne_one (P := P.toBraid) auth hT hcur
  apply SCKAScheme.securityImplAt_congr (R := fun {_} => Eq) (hrefl := fun _ => rfl)
  · exact fun _ => by
      simp only [scheme, idealSchemeOf, schemeWith, sendWith_idealOps, sendWith_real]
  · exact fun _ => by
      simp only [scheme, idealSchemeOf, schemeWith, sendWith_idealOps, sendWith_real]
  · intro n _ ρ tsnd hentry
    exact (recvSCKAWith_eq_recvSCKA auth _ _ _
      (recvWith_idealOps_eq_recv auth hCt2Sound (Ops.real P) (fun _ => rfl)
        hT true hentry (hdec true))).symm
  · intro n _ ρ tsnd hentry
    exact (recvSCKAWith_eq_recvSCKA auth _ _ _
      (recvWith_idealOps_eq_recv auth hCt2Sound (Ops.real P) (fun _ => rfl)
        hT false hentry (hdec false))).symm
  · exact fun _ => SCKAScheme.oracleSendArleak_run_congr _ _ _ s (by
      simp only [scheme, idealSchemeOf, schemeWith, sendRleakWith_idealOps, sendRleakWith_real])
  · exact fun _ => SCKAScheme.oracleSendBrleak_run_congr _ _ _ s (by
      simp only [scheme, idealSchemeOf, schemeWith, sendRleakWith_idealOps, sendRleakWith_real])

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- The tracked `realImpl b` preserves `trackedInv (CorrectnessInv auth ik) badPotential`. -/
private theorem tracked_realImpl_preserves (ik : InitKey) (b : Bool) :
    QueryImpl.PreservesInv (trackedImpl (realImpl auth sampleInitKey b) badPotential)
      (trackedInv (CorrectnessInv auth ik) badPotential) :=
  trackedImpl_preserves _ _ _ fun t s hs _ res hres =>
    realImpl_preserves_correctnessInv auth sampleInitKey hHdrSound hEkSound hCt1Sound
      hCt2Sound ik b t s hs res hres

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- For `p` with `trackedInv (CorrectnessInv auth ik) badPotential p`, a query `t` of the tracked
`realImpl b` from `p` raises the expected score by at most `ε` if `t` is an ordinary or leaking
send, and not at all otherwise. -/
private theorem tracked_realImpl_score_step_le (ik : InitKey) (b : Bool)
    (t : (securitySpec P AuthState).Domain) (p : GameState P AuthState × Bool)
    (hp : trackedInv (CorrectnessInv auth ik) badPotential p) :
    wp ((trackedImpl (realImpl auth sampleInitKey b) badPotential t).run p)
        (fun res => trackedScore res.2) ≤
      trackedScore p + if SCKAScheme.sckaSecuritySpec.isSendQuery t then
        P.det.toKEM.correctnessError ProbCompRuntime.probComp else 0 := by
  by_cases hbad : p.2 = true
  · refine le_trans (wp_le_const_of_support _ fun res _ => trackedScore_le_one res.2) ?_
    simp [trackedScore, hbad]
  have hfalse : p.2 = false := Bool.eq_false_iff.mpr hbad
  have hs : CorrectnessInv auth ik p.1 := by
    rcases hp with hp | hp
    · exact absurd hp hbad
    · exact hp.1
  have hpEq : p = (p.1, false) := Prod.ext rfl hfalse
  rw [hpEq]
  -- On the unflagged part, the tracked score of a successor is its failure potential.
  have hrun : wp ((trackedImpl (realImpl auth sampleInitKey b) badPotential t).run
        (p.1, false)) (fun res => trackedScore res.2) =
      wp ((realImpl auth sampleInitKey b t).run p.1)
        (fun res => failurePotential res.2) := by
    change wp (do
      let y ← (realImpl auth sampleInitKey b t).run p.1
      pure (y.1, (y.2, false || badPotential y.2))) _ = _
    rw [bind_pure_comp, wp_map]
    congr 1
    funext y
    simp only [Function.comp_apply, Bool.false_or, trackedScore_bad]
  rw [hrun]
  simp only [trackedScore, Bool.false_eq_true, ↓reduceIte]
  rw [SCKAScheme.securityImplAt_run]
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rw [SCKAScheme.sckaSecuritySpec.isSendQuery_OCorrectness]
    exact wp_failurePotential_query_le auth sampleInitKey hHdrSound hEkSound
      hCt1Sound hCt2Sound ik t p.1 hs.1 hs.2
  · cases u
    simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, ↓reduceIte]
    refine SCKAScheme.oracleSendArleak_wp_le (scheme P auth sampleInitKey) _
      (scheme_sendArleak_forget auth sampleInitKey) p.1 (leakEpochs p.1.stA)
      (fun key msg epoch state coins hout =>
        scheme_sendArleak_exposure auth sampleInitKey p.1.stA key msg epoch state coins hout)
      failurePotential failurePotential_exposed _ le_self_add ?_
    simpa [failurePotential, SCKAScheme.isSendQuery, SCKAScheme.sckaCorrectnessImpl,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] using
      wp_failurePotential_query_le auth sampleInitKey hHdrSound hEkSound
        hCt1Sound hCt2Sound ik SCKAScheme.sckaCorrectnessSpec.OSendA p.1 hs.1 hs.2
  · cases u
    simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, ↓reduceIte]
    refine SCKAScheme.oracleSendBrleak_wp_le (scheme P auth sampleInitKey) _
      (scheme_sendArleak_forget auth sampleInitKey) p.1 (leakEpochs p.1.stB)
      (fun key msg epoch state coins hout =>
        scheme_sendArleak_exposure auth sampleInitKey p.1.stB key msg epoch state coins hout)
      failurePotential failurePotential_exposed _ le_self_add ?_
    simpa [failurePotential, SCKAScheme.isSendQuery, SCKAScheme.sckaCorrectnessImpl,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] using
      wp_failurePotential_query_le auth sampleInitKey hHdrSound hEkSound
        hCt1Sound hCt2Sound ik SCKAScheme.sckaCorrectnessSpec.OSendB p.1 hs.1 hs.2
  all_goals
    simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, Bool.false_eq_true, ↓reduceIte, add_zero]
    refine wp_le_const_of_support _ fun res hres => le_of_eq ?_
  · exact SCKAScheme.oracleChall_preservesInv b (fun u => failurePotential u = failurePotential p.1)
      (fun u C h => (failurePotential_challenged u C).trans h) t p.1 rfl res hres
  · exact SCKAScheme.oracleCorruptA_preservesInv (vuln P AuthState).corrupt
      (fun u => failurePotential u = failurePotential p.1)
      (fun u E h => (failurePotential_exposed u E).trans h) u p.1 rfl res hres
  · exact SCKAScheme.oracleCorruptB_preservesInv (vuln P AuthState).corrupt
      (fun u => failurePotential u = failurePotential p.1)
      (fun u E h => (failurePotential_exposed u E).trans h) u p.1 rfl res hres

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- Assuming sound stream decoders and `SecuritySendQueryBound adv q`, the tracked execution of
`realImpl b` from `(initState auth ik, false)` ends with the flag set with probability at most
`q · ε`. -/
private theorem tracked_realImpl_bad_le (ik : InitKey) (b : Bool)
    (adv : SecurityAdversary P AuthState) (q : ℕ)
    (hq : SCKAScheme.SecuritySendQueryBound adv q) :
    Pr{let res ← ((simulateQ (trackedImpl (realImpl auth sampleInitKey b) badPotential) adv).run
        (initState auth ik, false))}[res.2.2 = true] ≤
      (q : ℝ≥0∞) * P.det.toKEM.correctnessError ProbCompRuntime.probComp := by
  have h := tracked_bad_le_of_score_step (realImpl auth sampleInitKey b) badPotential
    (CorrectnessInv auth ik) trackedScore
    (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true)
    (P.det.toKEM.correctnessError ProbCompRuntime.probComp)
    (fun x hx => by simp [trackedScore, hx])
    (tracked_realImpl_preserves auth sampleInitKey hHdrSound hEkSound hCt1Sound
      hCt2Sound ik b)
    (tracked_realImpl_score_step_le auth sampleInitKey hHdrSound hEkSound hCt1Sound
      hCt2Sound ik b)
    adv q hq (initState auth ik) (tracked_initState_inv auth ik)
  rwa [show trackedScore (initState auth ik, false) = 0 by
    simp [trackedScore, failurePotential_initState], zero_add] at h

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- Correctness for the full security interface. Assume sound stream decoders and an adversary
`adv` making at most `q` ordinary or leaking sends in total (`SecuritySendQueryBound adv q`). For
either fixed challenge bit `b` and every initial key `ik`, the run of `adv` against the security
oracles of `G_b` from `initState auth ik` ends with a false correctness flag with probability at
most `q · ε`. -/
theorem correctness_failure_le_security (b : Bool) (adv : SecurityAdversary P AuthState)
    (q : ℕ) (hq : SCKAScheme.SecuritySendQueryBound adv q) (ik : InitKey) :
    Pr{let res ← (simulateQ (SCKAScheme.sckaSecurityImpl b (vuln P AuthState)
        (vuln P AuthState) (scheme P auth sampleInitKey)) adv).run
        (initState auth ik)}[res.2.correct = false] ≤
      (q : ℝ≥0∞) * P.det.toKEM.correctnessError ProbCompRuntime.probComp := by
  rw [sckaSecurityImpl_eq_realImpl]
  refine (prEvent_not_good_le_tracked_bad (realImpl auth sampleInitKey b) badPotential
    (fun s => CorrectnessInv auth ik s ∧ s.correct = true) (fun s => s.correct)
    (fun _ hs => hs.2) ?_ adv (initState auth ik) ?_).trans
    (tracked_realImpl_bad_le auth sampleInitKey hHdrSound hEkSound hCt1Sound
      hCt2Sound ik b adv q hq)
  · intro t p hp res hres
    rcases tracked_realImpl_preserves auth sampleInitKey hHdrSound hEkSound hCt1Sound
        hCt2Sound ik b t p (hp.imp_right fun h => ⟨h.1.1, h.2⟩) res hres with
      hflag | ⟨hinv, hbad⟩
    · exact Or.inl hflag
    · exact Or.inr ⟨⟨hinv, correct_of_badPotential_eq_false hbad⟩, hbad⟩
  · exact (tracked_initState_inv auth ik).imp_right fun h => ⟨⟨h.1, rfl⟩, h.2⟩

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- Assuming sound stream decoders and `SecuritySendQueryBound adv q`, for every initial key `ik`,
the acceptance probabilities of `realImpl b` and `idealImpl (fun _ => b)` from `initState auth ik`
are within `q · ε` of each other. -/
private theorem security_correctness_endpoint_le_at (b : Bool)
    (adv : SecurityAdversary P AuthState)
    (q : ℕ) (hq : SCKAScheme.SecuritySendQueryBound adv q) (ik : InitKey) :
    Pr{let x ← ((simulateQ (realImpl auth sampleInitKey b) adv).run'
        (initState auth ik))}[x = true] ≤
      Pr{let x ← ((simulateQ (idealImpl auth sampleInitKey (fun _ => b)) adv).run'
        (initState auth ik))}[x = true] +
        (q : ℝ≥0∞) * P.det.toKEM.correctnessError ProbCompRuntime.probComp ∧
    Pr{let x ← ((simulateQ (idealImpl auth sampleInitKey (fun _ => b)) adv).run'
        (initState auth ik))}[x = true] ≤
      Pr{let x ← ((simulateQ (realImpl auth sampleInitKey b) adv).run'
          (initState auth ik))}[x = true] +
        (q : ℝ≥0∞) * P.det.toKEM.correctnessError ProbCompRuntime.probComp := by
  have hbad := tracked_realImpl_bad_le auth sampleInitKey hHdrSound hEkSound hCt1Sound
    hCt2Sound ik b adv q hq
  have h := prEvent_simulateQ_run'_bounds_of_tracked (realImpl auth sampleInitKey b)
    (idealImpl auth sampleInitKey (fun _ => b)) badPotential (CorrectnessInv auth ik)
    (tracked_realImpl_preserves auth sampleInitKey hHdrSound hEkSound hCt1Sound
      hCt2Sound ik b)
    (fun t u hu hflag => realImpl_run_eq_ideal auth sampleInitKey hCt2Sound ik b t u hu hflag)
    adv (· = true) (initState auth ik) (tracked_initState_inv auth ik)
  exact ⟨h.1.trans (add_le_add le_rfl hbad), h.2.trans (add_le_add le_rfl hbad)⟩

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- Assuming sound stream decoders and `SecuritySendQueryBound adv q`, the real game
`G_b := securityExpFixedBit scka adv b V V` of the SPQR scheme `scka` under its exposure policy `V`
and the ideal game `I_b := idealExp (fun _ => b) adv` differ in acceptance probability by at most
`q` times the KEM correctness error `ε`: `|Pr[G_b = true] - Pr[I_b = true]| ≤ q · ε`. -/
theorem security_correctness_endpoint_le (b : Bool) (adv : SecurityAdversary P AuthState)
    (q : ℕ) (hq : SCKAScheme.SecuritySendQueryBound adv q) :
    |(Pr{let x ← (SCKAScheme.securityExpFixedBit (scheme P auth sampleInitKey) adv b
        (vuln P AuthState) (vuln P AuthState))}[x = true]).toReal -
      (Pr{let x ← idealExp auth sampleInitKey (fun _ => b) adv}[x = true]).toReal| ≤
      (q : ℝ) * (P.det.toKEM.correctnessError ProbCompRuntime.probComp).toReal := by
  rw [securityExpFixedBit_eq, idealExp]
  have hfin : (q : ℝ≥0∞) * P.det.toKEM.correctnessError ProbCompRuntime.probComp ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (ne_of_lt (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top))
  have h := abs_toReal_prEvent_bind_sub_le sampleInitKey _ _ (· = true) _ hfin
    (fun ik _ => (security_correctness_endpoint_le_at auth sampleInitKey hHdrSound
      hEkSound hCt1Sound hCt2Sound b adv q hq ik).1)
    (fun ik _ => (security_correctness_endpoint_le_at auth sampleInitKey hHdrSound
      hEkSound hCt1Sound hCt2Sound b adv q hq ik).2)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using h

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- Assuming sound stream decoders and `SecuritySendQueryBound adv q`, the guessing advantage of
`adv` against the SPQR scheme `scka` under its exposure policy `V` is at most half the distance
between the ideal hybrids `H_0` and `H_q` (`H_i := idealExp (hybridMode i) adv`), plus `q` times
the KEM correctness error `ε`:
`sckaGuessAdvantage scka adv V V ≤ |Pr[H_0 = true] - Pr[H_q = true]| / 2 + q · ε`. -/
theorem security_guess_le_hybrid_gap (adv : SecurityAdversary P AuthState) (q : ℕ)
    (hq : SCKAScheme.SecuritySendQueryBound adv q) :
    SCKAScheme.sckaGuessAdvantage (scheme P auth sampleInitKey) adv (vuln P AuthState)
        (vuln P AuthState) ≤
      |(Pr{let x ← (idealExp auth sampleInitKey (SCKAScheme.hybridMode 0)
          adv)}[x = true]).toReal -
        (Pr{let x ← (idealExp auth sampleInitKey (SCKAScheme.hybridMode q)
            adv)}[x = true]).toReal| / 2 +
        (q : ℝ) * (P.det.toKEM.correctnessError ProbCompRuntime.probComp).toReal := by
  rw [SCKAScheme.hybridMode_zero, prEvent_idealExp_hybrid_last auth sampleInitKey hHdrSound
    hEkSound hCt1Sound hCt2Sound adv q hq, abs_sub_comm]
  exact SCKAScheme.sckaGuessAdvantage_le_of_abs_sub_le _ adv _ _
    (fun b => (Pr{let x ← idealExp auth sampleInitKey (fun _ => b) adv}[x = true]).toReal) _
    fun b => security_correctness_endpoint_le auth sampleInitKey hHdrSound hEkSound hCt1Sound
      hCt2Sound b adv q hq

end Endpoints

end Games

end SPQR
