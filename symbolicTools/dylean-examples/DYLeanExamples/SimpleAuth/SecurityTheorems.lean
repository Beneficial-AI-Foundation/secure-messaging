/-
  SimpleAuth in DYLean: security theorem.

  LeanDY's theorem is:

    abbrev authentication (tr : 𝑇 Unit Nonce) : Prop :=
      ∀ rk a b, (.Event $ .done a b rk) ∈ tr → (.Event $ .start a b rk) ∈ tr

    theorem protocol_authentication (h: Crypto.valid_trace Γ tr) : authentication tr

  It quantifies over *valid* traces (traces satisfying the invariant),
  and concludes that the matching `start` is somewhere in the trace.

  This file states the property twice, with independent proofs.
  Both quantify over *reachable* traces
  (traces the attacker can produce by calling the protocol functions and the network).
  - `initiator_auth_literal` is LeanDY's conclusion word for word:
    if `Done` is in the trace, then `Start` is in the trace.
  - `initiator_auth` is stronger: `Start` was logged *before* `Done`
    (in the prefix of the trace up to the time of `Done`).

  Why two versions: each framework hands you the event's invariant on a different trace.
  LeanDY's `valid_trace_mem` gives the validity of `done` on the *whole* trace
  (it lifts it there by monotonicity), so membership is what naturally comes out.
  DYLean's `Trace.EventLoggedAt_imp_EventInv` gives the invariant of `Done`
  on the prefix *before* `Done` was logged, so the ordering naturally comes out.
-/

module

import DY.Meta
import DY.Meta.Utils
public import DYLeanExamples.SimpleAuth.Specification
public import DYLeanExamples.SimpleAuth.Proof
import all DYLeanExamples.SimpleAuth.Proof
public import DYLeanExamples.SimpleAuth.Instance

namespace DY.Example.SimpleAuth

/--
  LeanDY's `authentication` property, word for word:
  for every reachable trace, if `Done a b na` was logged, then `Start a b na` was logged.
  The proof follows LeanDY's `protocol_authentication`:
  retrieve the invariant of the `Done` event, and read the `Start` event off it.
-/
public
theorem initiator_auth_literal
  (a b: Participant)
  (na: Bytes)
  : ∀ tr: ExecTrace,
    tr.Reachable reachability →
    tr.EventLogged (SimpleAuthEvent.Done a b na) →
    tr.EventLogged (SimpleAuthEvent.Start a b na)
:= by
  -- Reduce the statement on reachable (execution) traces
  -- to a statement on proof traces satisfying the invariant.
  apply Trace.apply_Reachable_implies_Invariant
  intro tr h_trinv h_ev
  -- The invariant of the `Done` event holds on the trace as it was when `Done` was logged
  -- (this plays the role of LeanDY's `valid_trace_mem`)...
  obtain ⟨ i, h_inv ⟩ := Trace.EventLogged_imp_EventInv _ _ h_trinv h_ev
  -- ... it says that `Start` was logged in that earlier trace...
  simp [ProtocolEvent.EventInv.invariant] at h_inv
  -- ... hence `Start` is also logged in the full trace (logged events stay logged).
  grind

/--
info: 'DY.Example.SimpleAuth.initiator_auth_literal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms initiator_auth_literal

/--
  For every reachable trace, if the initiator `a` logged `Done a b na` at time `time`,
  then `Start a b na` was logged before `time`.
  As in LeanDY, this holds unconditionally (no compromise clause),
  because it only relies on the initiator's own session state.
-/
public
theorem initiator_auth
  (a b: Participant)
  (na: Bytes)
  (time: Nat)
  : ∀ tr: ExecTrace,
    tr.Reachable reachability →
    tr.EventLoggedAt (SimpleAuthEvent.Done a b na) time →
    (tr.prefix time).EventLogged (SimpleAuthEvent.Start a b na)
:= by
  -- Reduce the statement on reachable (execution) traces
  -- to a statement on proof traces satisfying the invariant.
  apply Trace.apply_Reachable_implies_Invariant
  intro tr h_trinv h_ev
  -- The invariant of the `Done` event holds on the trace prefix before it was logged...
  have := Trace.EventLoggedAt_imp_EventInv _ _ _ h_trinv h_ev
  -- ... and this invariant is exactly the conclusion.
  simp [ProtocolEvent.EventInv.invariant] at this
  grind

/--
info: 'DY.Example.SimpleAuth.initiator_auth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms initiator_auth

end DY.Example.SimpleAuth
