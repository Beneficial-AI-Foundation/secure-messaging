/-
  SimpleAuth in DYLean: the trace invariant and its preservation.

  The proof follows DYLean's (DY*-style) methodology:
  1. choose labels and usages for the secrets (here: the shared key),
  2. give the protocol-specific part of the cryptographic invariants (here: of encryption),
  3. give invariants for the local states and the protocol events,
  4. prove one Hoare triple per protocol step, saying that it preserves the trace invariant,
  5. combine these proofs into "every reachable trace satisfies the invariant".

  This corresponds to LeanDY's `Γ`, `CryptoPreds`, `HasValid`, `event_preds`,
  and `valid_exchange` proofs, respectively.
-/

module

import DY.Meta.Step
import DY.Meta.Utils
public import DYLeanExamples.SimpleAuth.Specification
import all DYLeanExamples.SimpleAuth.Specification

namespace DY.Example.SimpleAuth

open DY.Comparse

/-
  The proof trace is the execution trace enriched with ghost information
  (e.g. the label and usage of each random value).
  This section lists the proof-trace entry types; it mirrors `HasExecTrace`.
-/
-- Future work (upstream comment): the following section is boilerplate that could be meta-programmed
public section ProofTraceConfig

class HasProofTrace extends HasExecTrace where
  [traceProof: ProofTraceTypes]
  [traceProof0: ProofTraceTypes.Has Network.ProofEntryT]
  [traceProof1: ProofTraceTypes.Has Random.ProofEntryT]
  [traceProof2: ProofTraceTypes.Has (ProtocolEvent.ProofEntryT SimpleAuth.SimpleAuthEvent)]
  [traceProof3: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT SimpleAuth.SharedKeyState)]
  [traceProof4: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT SimpleAuth.InitiatorState)]

attribute [reducible, scoped instance] HasProofTrace.traceProof
attribute [reducible, scoped instance] HasProofTrace.traceProof0
attribute [reducible, scoped instance] HasProofTrace.traceProof1
attribute [reducible, scoped instance] HasProofTrace.traceProof2
attribute [reducible, scoped instance] HasProofTrace.traceProof3
attribute [reducible, scoped instance] HasProofTrace.traceProof4

end ProofTraceConfig

public section BytesInvariants

variable [HasProofTrace]

/--
  The label of SK(initiator, responder): it becomes public as soon as
  the initiator's or the responder's copy of the key is compromised.
  This replaces LeanDY's `Γ` (`Nonce.Sk _ _ ↦ 𝓢ec`):
  DYLean labels are not looked up in a global environment,
  they are attached to a random value when it is generated (see `SharedKey.generate.spec`).
  LeanDY's `𝓢ec` corresponds to `Label.secret`, which would forbid compromising the key.
-/
def sharedKeyLabel
  (initiator responder: Participant) (key: Bytes)
  : Label
where
  isCorrupt tr := SharedKeyCompromised initiator responder key tr

/--
  The usage of shared keys: they are symmetric-encryption keys for SimpleAuth.
  Usages say what a secret may be used for;
  the encryption invariant dispatches on the key usage to find which predicate applies.
-/
@[grind]
def sharedKeyUsage: Usage := {
  type := "SymKey",
  tag := "SimpleAuth SharedKey",
  data := none
}

/--
  What honest participants may encrypt with a SimpleAuth key:
  a well-formed `ResponsePayload` (a nonce and a participant name).
  This is the counterpart of LeanDY's `u_sym_enc_pred Γ _ m k tr := ∃ a b, m = [!(); a, b]`
  ("the plaintext is a pair").
  As in LeanDY, it says nothing about *who* encrypted or *when*,
  which is why the final theorem cannot conclude anything about the responder.
-/
instance SimpleAuthSymEncPred
  : SymEnc.SymEncPred
where
  pred keyUsg _key msg _tr :=
    keyUsg = sharedKeyUsage ∧ (
      match (parse msg: Err ResponsePayload) with
      | none => False
      | some _ => True
    )

-- The predicate does not depend on the trace, hence it is trivially stable.
instance
  [BytesInvariants]
  : SymEnc.SymEncPredProof
where
  pred_later := by
    intro _ _ _ _ _ _ _ _ _ _ _ h
    exact h

end BytesInvariants

-- Future work (upstream comment): the following section is boilerplate that could be meta-programmed
public section BytesInvariantsConfig

class HasBytesInvariants extends HasProofTrace where
  [bytesInv: BytesInvariants]
  [bytesInvProof: BytesInvariantsProofs]
  [bytesInv0: BytesInvariants.Has Random.invariants]
  [bytesInv1: BytesInvariants.Has Literal.invariants]
  [bytesInv2: BytesInvariants.Has Concat.invariants]
  [bytesInv3: BytesInvariants.Has SymEnc.invariants]

attribute [reducible, scoped instance] HasBytesInvariants.bytesInv
attribute [           scoped instance] HasBytesInvariants.bytesInvProof
attribute [           scoped instance] HasBytesInvariants.bytesInv0
attribute [           scoped instance] HasBytesInvariants.bytesInv1
attribute [           scoped instance] HasBytesInvariants.bytesInv2
attribute [           scoped instance] HasBytesInvariants.bytesInv3

end BytesInvariantsConfig

public section TraceInvariant

variable [HasBytesInvariants]

/--
  Invariant of a participant's copy of SK(initiator, responder):
  the owner is one of the two participants, and the key has the expected label and usage.
  Because the state is compromisable, we must also prove that its content
  may be known by whoever compromises it (`invariant_implies_KnowableBy`):
  this holds because compromising either copy makes the key's label corrupt.
-/
instance SharedKeyStateInv : PersistentLocalState.CompromisableLocalStateInv SharedKeyState
where
  invariant me st tr :=
    let { initiator, responder, key } := st
    (me = initiator ∨ me = responder) ∧
    key.Invariant tr ∧
    key.label tr = sharedKeyLabel initiator responder key ∧
    key.HasUsage sharedKeyUsage tr
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by
    intro h
    have: (sharedKeyLabel state.initiator state.responder state.key).canFlow (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, sharedKeyLabel, SharedKeyCompromised] at *
      grind
    grind [canFlowTrans]

/--
  Invariant of the initiator's session state, LeanDY's `HasValid` instance:
  `valid Γ (.Init a b na) tr := valid_bytes Γ na tr ∧ (.Event $ .start a b na) ∈ tr`.
  Here: the nonce is publishable, and `Start me b na` has been logged.
  The nonce is public, so the state may be leaked without breaking anything.
-/
instance InitiatorStateInv : PersistentLocalState.CompromisableLocalStateInv InitiatorState
where
  invariant me st tr :=
    let { b, na } := st
    na.Publishable tr ∧
    tr.erase.EventLogged (SimpleAuthEvent.Start me b na)
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by
    grind [canFlowTrans]

/--
  Event invariants, LeanDY's `event_preds`.
  An event invariant must hold on the trace *before* the event is logged.
  - `Start` may be logged at any time
    (LeanDY additionally requires `na ≠ fail`; DYLean has no `fail` value:
    failures are handled by the `Traceful` monad and never reach the trace).
  - `Done a b na` may only be logged if `Start a b na` was logged before.
-/
instance SimpleAuthEventInv : ProtocolEvent.EventInv SimpleAuthEvent
where
  invariant tr ev :=
    match ev with
    | SimpleAuthEvent.Start _ _ _ => True
    | SimpleAuthEvent.Done a b na => tr.erase.EventLogged (SimpleAuthEvent.Start a b na)

end TraceInvariant

-- Future work (upstream comment): the following section is boilerplate that could be meta-programmed
public section TraceInvariantConfig

class HasTraceInvariant extends HasBytesInvariants where
  [traceInv: TraceInvariant]
  [traceInv0: TraceInvariant.Has Network.ProofEntryT]
  [traceInv1: TraceInvariant.Has Random.ProofEntryT]
  [traceInv2: TraceInvariant.Has (ProtocolEvent.ProofEntryT SimpleAuth.SimpleAuthEvent)]
  [traceInv3: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT SimpleAuth.SharedKeyState)]
  [traceInv4: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT SimpleAuth.InitiatorState)]
  [attBaseThm: BaseAttackerKnowledgeTheorem]
  [attThm: AttackerKnowledgeTheorem]

attribute [reducible, scoped instance] HasTraceInvariant.traceInv
attribute [           scoped instance] HasTraceInvariant.traceInv0
attribute [           scoped instance] HasTraceInvariant.traceInv1
attribute [           scoped instance] HasTraceInvariant.traceInv2
attribute [           scoped instance] HasTraceInvariant.traceInv3
attribute [           scoped instance] HasTraceInvariant.traceInv4
attribute [           scoped instance] HasTraceInvariant.attBaseThm
attribute [           scoped instance] HasTraceInvariant.attThm

end TraceInvariantConfig

/-
  One Hoare triple per protocol step:
  starting from a trace satisfying the invariant, the step produces a trace satisfying the invariant.
  These are LeanDY's `valid_exchange` theorems.

  The `step` tactic symbolically executes one instruction of the `Traceful` program:
  it looks up the Hoare triple of that instruction,
  discharges its precondition (by `grind`, or by the tactic given with `step by ...`),
  and adds its postcondition to the context.
  `step with ⟨ g ⟩` supplies a ghost argument
  (the label and usage of a random value, the usage of an encryption key).
  Hypotheses about the previous trace are automatically transported to the new, longer trace
  ("monotonization"), using lemmas tagged `grind_later`.
-/
public section Proofs

variable [HasTraceInvariant]

attribute [local grind] ProtocolEvent.EventInv.invariant
attribute [local grind] SimpleAuthEventInv
attribute [local grind] SharedKeyStateInv
attribute [local grind] InitiatorStateInv
attribute [local grind] SymEnc.SymEncPred.pred
attribute [local grind] SimpleAuthSymEncPred
attribute [local grind] PersistentLocalState.LocalStateInv.invariant
attribute [local grind] PersistentLocalState.CompromisableLocalStateInv.toLocalStateInv

@[instance]
theorem SharedKey.generate.spec (initiator responder: Participant):
  HoareTriple
    (SharedKey.generate initiator responder)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold SharedKey.generate
  -- The key is generated with label `sharedKeyLabel initiator responder key` and usage `sharedKeyUsage`.
  step with ⟨ fun key => sharedKeyLabel initiator responder key, sharedKeyUsage ⟩
  -- Storing each copy requires the `SharedKeyStateInv` invariant.
  step by
    simp only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step by
    simp only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step
  grind

@[instance]
theorem Initiator.start.spec (a b: Participant):
  HoareTriple
    (Initiator.start a b)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold Initiator.start
  -- The nonce is public, like LeanDY's `Nonce.Nat n` (labelled `𝓟ub` by `Γ`).
  step with ⟨ fun _ => Label.pub, Usage.nothing ⟩
  -- Logging `Start`: its invariant is `True`.
  step
  -- Storing the state: the nonce is publishable and `Start a b na` was just logged.
  step by
    simp only [PersistentLocalState.LocalStateInv.invariant]
    grind
  -- Sending the message: it only contains public data.
  step
  step
  grind

@[instance]
theorem Responder.respond.spec (a b: Participant) (keyHandle msgHandle: Nat):
  HoareTriple
    (Responder.respond a b keyHandle msgHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold Responder.respond
  -- Receiving: the message is publishable (it may come from the attacker).
  step
  -- Parsing: the parsed fields relate to the received bytes.
  step
  -- Checking the identities.
  step
  -- Loading the key: we learn `SharedKeyStateInv` (label and usage of the key).
  step
  -- Checking the key's owners.
  step
  -- Encrypting: we must establish the encryption invariant in its honest case, i.e.
  -- - the key has usage `sharedKeyUsage`, of type "SymKey",
  -- - the plaintext satisfies `SimpleAuthSymEncPred` (it parses as a `ResponsePayload`),
  -- - the plaintext (public) is no more secret than the key.
  step with ⟨ sharedKeyUsage ⟩ by
    have: (serialize ({ na := msg.na, a := msg.a }: ResponsePayload)).Publishable tr := by grind
    simp_all only [PersistentLocalState.LocalStateInv.invariant]
    grind [canFlowTrans]
  -- Sending: the ciphertext is publishable.
  step
  grind

@[instance]
theorem Initiator.finish.spec (a: Participant) (keyHandle stHandle msgHandle: Nat):
  HoareTriple
    (Initiator.finish a keyHandle stHandle msgHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold Initiator.finish
  -- Loading the session state: we learn `InitiatorStateInv`, in particular that `Start a b na` was logged.
  step
  -- `let ({ b, na }: InitiatorState) ← ...` is a pattern match: open it.
  split
  -- Loading the key and checking its owners.
  step
  step
  -- Expose the facts stored in the state invariants (e.g. `key.Invariant tr`) as separate hypotheses,
  -- so that `step` can transport facts mentioning `key.label tr` to later traces.
  simp only [PersistentLocalState.LocalStateInv.invariant] at *
  -- Receiving the ciphertext.
  step
  -- Decrypting (ghost argument: the key usage).
  step with ⟨ sharedKeyUsage ⟩
  -- Parsing and checking the plaintext.
  step
  step
  -- Logging `Done a b na`: its invariant (`Start a b na` was logged) comes from the session state,
  -- *not* from the decrypted message. This is exactly LeanDY's `valid_initiator_check` proof.
  step
  grind

@[instance]
theorem SharedKeyState.compromise.spec (stHandle: Nat): HoareTriple (SharedKeyState.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold SharedKeyState.compromise; step; grind

@[instance]
theorem InitiatorState.compromise.spec (stHandle: Nat): HoareTriple (InitiatorState.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold InitiatorState.compromise; step; grind

end Proofs

/-
  Package the step proofs: every function the attacker may call preserves the invariant.
  By induction on reachability (`Trace.Reachable_implies_Invariant`),
  every reachable trace has a proof trace satisfying the invariant.
  This is the part that LeanDY leaves to the user ("induct over permitted executions").
-/
section ReachabilityImpliesInvariant

variable [HasTraceInvariant]

public instance: ReachableImpliesInvariant SharedKey.generate.reachability := .mk (fun (initiator, responder) => SharedKey.generate.spec initiator responder)
public instance: ReachableImpliesInvariant Initiator.start.reachability := .mk (fun (a, b) => Initiator.start.spec a b)
public instance: ReachableImpliesInvariant Responder.respond.reachability := .mk (fun (a, b, keyHandle, msgHandle) => Responder.respond.spec a b keyHandle msgHandle)
public instance: ReachableImpliesInvariant Initiator.finish.reachability := .mk (fun (a, keyHandle, stHandle, msgHandle) => Initiator.finish.spec a keyHandle stHandle msgHandle)
public instance: ReachableImpliesInvariant SharedKeyState.compromise.reachability := .mk (fun stHandle => SharedKeyState.compromise.spec stHandle)
public instance: ReachableImpliesInvariant InitiatorState.compromise.reachability := .mk (fun stHandle => InitiatorState.compromise.spec stHandle)

#combine into ReachabilityTheorem from
  Network,
  SharedKey.generate,
  Initiator.start,
  Responder.respond,
  Initiator.finish,
  SharedKeyState.compromise,
  InitiatorState.compromise,

end ReachabilityImpliesInvariant

end DY.Example.SimpleAuth
