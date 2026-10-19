import LeanDYExamples.SimpleAuth

open DebugM Executable IO

private def renderSymbolicBytes : 𝔹 Unit Nonce → String
  | none => "fail"
  | some (.Xor nonces) =>
      match nonces.maybe_choose_unique with
      | some nonce => "nonce(" ++ reprStr nonce ++ ")"
      | none => "xor(...)"
  | some (.Const (.Princ principal)) => "principal(" ++ reprStr principal ++ ")"
  | some (.Const (.BitString string)) => "string(" ++ reprStr string ++ ")"
  | some (.Const (.Nat number)) => "nat(" ++ toString number ++ ")"
  | some (.Key _ _ key) => "key(" ++ renderSymbolicBytes (some key) ++ ")"
  | some (.Tuple _ left right) =>
      "tuple(" ++ renderSymbolicBytes (some left) ++ ", " ++
        renderSymbolicBytes (some right) ++ ")"
  | some (.SymEnc _ message key) =>
      "symenc(" ++ renderSymbolicBytes (some message) ++ ", " ++
        renderSymbolicBytes (some key) ++ ")"
  | some (.SymDec _ ciphertext key) =>
      "symdec(" ++ renderSymbolicBytes (some ciphertext) ++ ", " ++
        renderSymbolicBytes (some key) ++ ")"
  | some (.AEnc _ message key) =>
      "aenc(" ++ renderSymbolicBytes (some message) ++ ", " ++
        renderSymbolicBytes (some key) ++ ")"
  | some (.ADec _ ciphertext key) =>
      "adec(" ++ renderSymbolicBytes (some ciphertext) ++ ", " ++
        renderSymbolicBytes (some key) ++ ")"
  | some (.Sign _ message key) =>
      "sign(" ++ renderSymbolicBytes (some message) ++ ", " ++
        renderSymbolicBytes (some key) ++ ")"
  | some (.Verify _ signature key) =>
      "verify(" ++ renderSymbolicBytes (some signature) ++ ", " ++
        renderSymbolicBytes (some key) ++ ")"
  | some (.Hash _ value) => "hash(" ++ renderSymbolicBytes (some value) ++ ")"
  | some (.Proj_1 _ value) => "proj1(" ++ renderSymbolicBytes (some value) ++ ")"
  | some (.Proj_2 _ value) => "proj2(" ++ renderSymbolicBytes (some value) ++ ")"

instance : Repr (𝐵 Unit Nonce) where
  reprPrec message _ := renderSymbolicBytes message.γ'

instance : Repr (BytesEq.NonFail Unit Nonce) := inferInstance

instance : Repr State where
  reprPrec
    | .Init a b nonce, _ =>
        "Init(" ++ reprStr a ++ ", " ++ reprStr b ++ ", " ++
          renderSymbolicBytes nonce.val.γ' ++ ")"
    | .Null, _ => "Null"

instance : Repr (Crypto.UserPreds.u_state Unit Nonce) := inferInstanceAs (Repr State)
instance : DecidableEq (Crypto.UserPreds.u_state Unit Nonce) := inferInstanceAs (DecidableEq State)

abbrev SimpleAuthDebugM := DebugM Unit Nonce

def alice : ℙ := "alice"
def bob : ℙ := "bob"

def dbgConfig : DebugConfig Unit Nonce := {
  show_non_failed_messages := true
  default_state := none
}

/-- Run one exchange and return the state and message it produces. -/
def runStep (st : State) (msg : 𝐵 Unit Nonce) (op : exchange Unit Nonce) :
    SimpleAuthDebugM (State × 𝐵 Unit Nonce) := do
  set_next_state st
  set_next_message msg
  execute op
  return (← get_next_state, ← get_next_message)

/-- Execute the intended honest run: initiator, responder, then initiator check. -/
def runDemo : SimpleAuthDebugM Unit := do
  println "--- SIMPLE AUTH DEMO ---"
  println "1. Initiator sends (A, B, Na)."
  let (initiatorState, firstMessage) ← runStep .Null .fail (initiator alice bob 42)
  println "2. Responder sends encrypted (Na, A)."
  let (_, reply) ← runStep .Null firstMessage (responder alice bob)
  println "3. Initiator decrypts and checks the reply as (Na, A)."
  let _ ← runStep initiatorState reply initiator_check
  let trace ← get_trace
  let hasDone := trace.any fun
    | .Event event => event.tag == "done"
    | _ => false
  println ("done event emitted: " ++ toString hasDone)

def main : IO Unit := do
  let _ ← DebugM.to_IO (config := dbgConfig) runDemo
  return ()
