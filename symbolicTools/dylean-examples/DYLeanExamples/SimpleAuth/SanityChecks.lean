/-
  SimpleAuth in DYLean: sanity checks.

  A security theorem of the form "if Done then Start" is vacuously true
  if `Done` can never be logged.
  We therefore check that the specification has the intended behaviours,
  by *executing* the protocol code (`#guard`) and *proving* that the resulting traces are reachable.
  This is the counterpart of LeanDY's debug run
  (`symbolicTools/leandy-examples/LeanDYExamples/SimpleAuthDemo.lean`).

  1. `honestRun`: an honest execution reaches `Done`.
  2. `forgedResponseAttacker`: a response forged without the shared key is rejected.
  3. `compromisedKeyAttacker`: with a leaked key, the attacker makes Alice log `Done`
     although Bob never responded. This is allowed by `initiator_auth`,
     and illustrates that SimpleAuth's property says nothing about the responder.
-/

module

import DY.Meta
import DY.Meta.Utils
import DYLeanExamples.SimpleAuth.Specification
import DYLeanExamples.SimpleAuth.Instance
public meta import DYLeanExamples.SimpleAuth.Instance

namespace DY.Example.SimpleAuth

-- Copied from DYLean's `Examples/SignedDH/SanityChecks.lean` (it is private there).
theorem liftM_parse_preserves_reachability
  {a: Type} [Comparse.ParseableSerializeable a]
  (config: ReachabilityConfig)
  (buf: Bytes)
  : (liftM (Comparse.parse buf): Traceful a).PreservesReachability config (fun _ => True) (fun res _ => Comparse.FormatRel buf res)
:= by
  simp only [Traceful.PreservesReachability, Traceful.PreservesReachabilityFrom, liftM, monadLift, MonadLift.monadLift, Traceful.run_mk]
  grind

/-
  1. Honest run.
  Trace entries (timestamps on the right):
  key generation (0), Alice's key copy (1), Bob's key copy (2),
  nonce generation (3), `Start` (4), Alice's session state (5), first message (6),
  response (7), `Done` (8).
-/

public
def honestRun: Traceful Unit := do
  let (aliceKeyHandle, bobKeyHandle) ← SharedKey.generate "Alice" "Bob" -- 3 entries
  let (stHandle, msgHandle) ← Initiator.start "Alice" "Bob" -- 4 entries
  let respHandle ← Responder.respond "Alice" "Bob" bobKeyHandle msgHandle -- 1 entry
  Initiator.finish "Alice" aliceKeyHandle stHandle respHandle -- 1 entry

-- The run succeeds: every `guard`, `parse` and decryption succeeds.
#guard (honestRun.run Trace.nil).fst = some ()

-- Future work (upstream comment): we could design a step-like tactic to automate this proof
theorem honestRun_PreservesReachability
  : honestRun.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr h_pre
  dsimp only [honestRun]

  -- Each call to a protocol function is a reachability step.
  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (SharedKey.generate.reachability) _ ("Alice", "Bob")
  · assumption
  · simp [SharedKey.generate.reachability]
  intro ⟨ aliceKeyHandle, bobKeyHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Initiator.start.reachability) _ ("Alice", "Bob")
  · assumption
  · simp [Initiator.start.reachability]
  intro ⟨ stHandle, msgHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Responder.respond.reachability) _ ("Alice", "Bob", bobKeyHandle, msgHandle)
  · assumption
  · simp [Responder.respond.reachability]
  intro respHandle tr h_post h_tr h_le

  -- The last call is not followed by a bind: unfold `PreservesReachabilityFrom` directly.
  have := Traceful.PreservesReachability_base (Initiator.finish.reachability) reachability ("Alice", aliceKeyHandle, stHandle, respHandle)
  simp only [Traceful.PreservesReachability, Initiator.finish.reachability] at this
  grind

/--
  The honest trace is reachable, and contains `Start` followed by `Done` for the same nonce.
  `native_decide` evaluates the trace.
-/
public
theorem honestRun_properties:
  let tr := (honestRun.run (Trace.nil)).snd.val
  tr.Reachable reachability ∧
  ∃ t1 t2 na,
    t1 < t2 ∧
    tr.EventLoggedAt (SimpleAuthEvent.Start "Alice" "Bob" na) t1 ∧
    tr.EventLoggedAt (SimpleAuthEvent.Done "Alice" "Bob" na) t2
:= by
  intro tr
  refine ⟨ ?_, ?_ ⟩
  · apply Traceful.PreservesReachability_to_Reachable honestRun_PreservesReachability
    grind
  simp only [DY.Trace.EventLoggedAt_eq_getEventAt]
  -- The nonce is found by inspecting the event at timestamp 4.
  let witness :=
    match (Trace.getEventAt SimpleAuthEvent 4 tr) with
    | some (SimpleAuthEvent.Start _ _ na) => na
    | _ => Comparse.BytesLike.empty
  refine ⟨ 4, 8, witness, ?_ ⟩
  native_decide

/--
info: 'DY.Example.SimpleAuth.honestRun_properties' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 honestRun_properties._native.native_decide.ax_1_6]
-/
#guard_msgs in
#print axioms honestRun_properties

/-
  2. A forged response is rejected.
  The attacker answers Alice's first message itself,
  encrypting the expected plaintext under a key it made up.
  Alice's decryption fails, so `Initiator.finish` aborts and `Done` is never logged.
-/

public
def forgedResponseAttacker: Traceful Unit := do
  let (aliceKeyHandle, _) ← SharedKey.generate "Alice" "Bob"
  let (stHandle, msgHandle) ← Initiator.start "Alice" "Bob"

  let msgBytes ← Network.receiveMessage msgHandle
  let msg: InitMessage ← Comparse.parse msgBytes
  let fakeKey := Literal.literalToBytes "00000000000000000000000000000000".toByteArray
  let forged := SymEnc.symEnc fakeKey (Comparse.serialize ({ na := msg.na, a := msg.a }: ResponsePayload))
  let forgedHandle ← Network.sendMessage forged

  Initiator.finish "Alice" aliceKeyHandle stHandle forgedHandle

-- The run fails (at Alice's decryption).
#guard (forgedResponseAttacker.run Trace.nil).fst = none

/-
  3. With a compromised key, Alice completes without Bob.
  The attacker compromises Bob's copy of the shared key,
  then answers Alice's first message itself.
  Alice logs `Done`, although `Responder.respond` was never called.
  `initiator_auth` still holds (`Start` was logged before `Done`):
  the theorem constrains only the initiator's own history.
  Trace entries:
  key generation (0), Alice's key copy (1), Bob's key copy (2),
  compromise of Bob's copy (3), leaked state on the network (4),
  nonce generation (5), `Start` (6), Alice's session state (7), first message (8),
  forged response (9), `Done` (10).
-/

public
def compromisedKeyAttacker: Traceful Unit := do
  let (aliceKeyHandle, bobKeyHandle) ← SharedKey.generate "Alice" "Bob"
  let leakHandle ← SharedKeyState.compromise bobKeyHandle
  let leakedBytes ← Network.receiveMessage leakHandle
  let leaked: PersistentLocalState.LocalState SharedKeyState ← Comparse.parse leakedBytes
  let key := leaked.state.key

  let (stHandle, msgHandle) ← Initiator.start "Alice" "Bob"

  let msgBytes ← Network.receiveMessage msgHandle
  let msg: InitMessage ← Comparse.parse msgBytes
  let forged := SymEnc.symEnc key (Comparse.serialize ({ na := msg.na, a := msg.a }: ResponsePayload))
  let forgedHandle ← Network.sendMessage forged

  Initiator.finish "Alice" aliceKeyHandle stHandle forgedHandle

#guard (compromisedKeyAttacker.run Trace.nil).fst = some ()

-- Future work (upstream comment): we could design a step-like tactic to automate this proof
theorem compromisedKeyAttacker_PreservesReachability
  : compromisedKeyAttacker.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr h_pre
  dsimp only [compromisedKeyAttacker]

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (SharedKey.generate.reachability) _ ("Alice", "Bob")
  · assumption
  · simp [SharedKey.generate.reachability]
  intro ⟨ aliceKeyHandle, bobKeyHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (SharedKeyState.compromise.reachability)
  · assumption
  · simp [SharedKeyState.compromise.reachability]
  intro leakHandle tr h_post h_tr h_le

  -- Attacker computations do not append to the trace, but we record what the attacker knows.
  apply Traceful.PreservesReachabilityFrom_bind
  · apply Network.receiveMessage.preservesReachability
  · assumption
  · grind
  intro leakedBytes tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply liftM_parse_preserves_reachability
  · assumption
  · grind
  intro leaked tr h_post h_tr h_le

  dsimp only
  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Initiator.start.reachability) _ ("Alice", "Bob")
  · assumption
  · simp [Initiator.start.reachability]
  intro ⟨ stHandle, msgHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Network.receiveMessage.preservesReachability
  · assumption
  · grind
  intro msgBytes tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply liftM_parse_preserves_reachability
  · assumption
  · grind
  intro msg tr h_post h_tr h_le

  -- Sending the forged response: the attacker must know it
  -- (it knows the leaked key and the nonce, hence their encryption).
  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · dsimp only
    apply SymEnc.attacker_knows_symEnc
    · grind (ematch := 10)
    · simp only [Comparse.AttackerKnows_serialize, ResponsePayload.IsWellFormed_eq]
      grind
  intro forgedHandle tr h_post h_tr h_le

  have := Traceful.PreservesReachability_base (Initiator.finish.reachability) reachability ("Alice", aliceKeyHandle, stHandle, forgedHandle)
  simp only [Traceful.PreservesReachability, Initiator.finish.reachability] at this
  grind

/-- The compromise trace is reachable, and Alice logged `Done` (without any responder step). -/
public
theorem compromisedKeyAttacker_properties:
  let tr := (compromisedKeyAttacker.run (Trace.nil)).snd.val
  tr.Reachable reachability ∧
  ∃ t na,
    tr.EventLoggedAt (SimpleAuthEvent.Done "Alice" "Bob" na) t
:= by
  intro tr
  refine ⟨ ?_, ?_ ⟩
  · apply Traceful.PreservesReachability_to_Reachable compromisedKeyAttacker_PreservesReachability
    grind
  simp only [DY.Trace.EventLoggedAt_eq_getEventAt]
  let witness :=
    match (Trace.getEventAt SimpleAuthEvent 10 tr) with
    | some (SimpleAuthEvent.Done _ _ na) => na
    | _ => Comparse.BytesLike.empty
  refine ⟨ 10, witness, ?_ ⟩
  native_decide

/--
info: 'DY.Example.SimpleAuth.compromisedKeyAttacker_properties' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compromisedKeyAttacker_properties._native.native_decide.ax_1_6]
-/
#guard_msgs in
#print axioms compromisedKeyAttacker_properties

end DY.Example.SimpleAuth
