/-
  SimpleAuth in DYLean: closing the world.

  `Specification.lean` and `Proof.lean` are parametrized by typeclasses
  (`HasExecBytes`, `HasExecTrace`, ..., `HasTraceInvariant`) that only say
  "the protocol's `Bytes`/trace/invariant contain at least these components".
  Here we build the concrete types by combining exactly the components SimpleAuth uses,
  and provide the instances.
  LeanDY has no counterpart of this file: its bytes, trace entries and attacker are fixed by the library.
-/

module

public import DYLeanExamples.SimpleAuth.Specification
public import DYLeanExamples.SimpleAuth.Proof

namespace DY.Example.SimpleAuth

-- Future work (upstream comment): the following section could avoid a lot of repetition
public section

-- The symbolic bytes: random values, literals, concatenation and symmetric encryption.
#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  Random,
  Literal,
  Concat,
  SymEnc,

instance: HasExecBytes where

-- The execution trace entries.
#combine +toplevel into
  ExecEntryT,
  baseAttackerKnowledge,
from
  Network,
  Random,
  ProtocolEvent SimpleAuth.SimpleAuthEvent,
  PersistentLocalState.CompromisableState SimpleAuth.SharedKeyState,
  PersistentLocalState.CompromisableState SimpleAuth.InitiatorState,

instance: HasExecTrace where

-- The proof trace entries.
#combine +toplevel into
  ProofEntryT,
from
  Network,
  Random,
  ProtocolEvent SimpleAuth.SimpleAuthEvent,
  PersistentLocalState.CompromisableState SimpleAuth.SharedKeyState,
  PersistentLocalState.CompromisableState SimpleAuth.InitiatorState,

instance: HasProofTrace where

-- The bytes invariants (this is where `SimpleAuthSymEncPred` is plugged in).
#combine +toplevel into BytesInvariants, BytesInvariantsProofs from
  Random,
  Literal,
  Concat,
  SymEnc,

instance: HasBytesInvariants where

-- The trace invariant, and the proof that the attacker only learns publishable bytes.
#combine +toplevel into
  SubTraceInvariant,
  SubBaseAttackerKnowledgeTheorem,
from
  Network,
  Random,
  ProtocolEvent SimpleAuth.SimpleAuthEvent,
  PersistentLocalState.CompromisableState SimpleAuth.SharedKeyState,
  PersistentLocalState.CompromisableState SimpleAuth.InitiatorState,

#combine +toplevel into SubAttackerKnowledgeTheorem from
  Random,
  Literal,
  Concat,
  SymEnc,

instance: HasTraceInvariant where

end

end DY.Example.SimpleAuth
