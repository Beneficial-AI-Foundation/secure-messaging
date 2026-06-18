/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.Defs
import ToMathlib.Control.StateT
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# Continuous Key Agreement (CKA) from Decisional Diffie-Hellman (DDH) Assumption

Construction of a CKA scheme from the DDH following [ACD19, Section 4.1].
https://eprint.iacr.org/2018/1037.pdf

We consider a module `Module F G` with scalar field `F`, additive group `G`,
scalar multiplication `a • gen`, and a fixed generator `gen : G`.

- Initial key space `IK = G × F` — a group element and its discrete log.
- Epoch key space `I = G` — DH shared secrets.
- Message space `Rho = G` — DH public values.
- State space `St = CKAState F G` — a phase-tagged state:
  `sendReady h` holds a group element `h : G` and can send next;
  `recvReady x` holds a scalar `x : F` and can receive next.

The send and receive algorithms are same for both A and B: sendA = sendB and recvA = recvB.

```text
Setup:

  initKeyGen()                                 -- x₀ ←$ F
        │
        ▼
  ik = (x₀•gen, x₀)
        │
   ┌────┴────────────┐
   ▼                 ▼
 initA(ik)         initB(ik)
   │                 │
   ▼                 ▼
 stA₀ = x₀•gen ∈ G  stB₀ = x₀ ∈ F

Alternating protocol flow (Round 1, A → B):

A                                          B
─────                                      ─────
stA = x₀•gen ∈ G                           stB = x₀ ∈ F

sendA(stA):
  x   ←$ F
  kA  := x • (x₀•gen)
  ρA  := x • gen
  stA':= x ∈ F
         ─────────── ρA ───────────▶
                                           recvB(stB, ρA):
                                             kB   := x₀ • ρA      (= x₀ • (x•gen))
                                             stB' := ρA ∈ G       (= x•gen)

[CORRECTNESS: kA = x•(x₀•gen) = x₀•(x•gen) = kB]

Round 2 (B → A):

A                                          B
─────                                      ─────
stA' = x ∈ F                               stB' = x•gen ∈ G

                                           sendB(stB'):
                                             y'   ←$ F
                                             kB'  := y' • (x•gen)
                                             ρB   := y' • gen
                                             stB'':= y' ∈ F
         ◀─────────── ρB ───────────

recvA(stA', ρB):
  kA'   := x • ρB        (= x • (y'•gen))
  stA'' := ρB ∈ G        (= y'•gen)

[CORRECTNESS: kA' = x•(y'•gen) = y'•(x•gen) = kB']
```
-/

open OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]

/-- Phase-tagged CKA state for the DDH construction.

`sendReady h` means the party holds the peer's current DH public value `h : G`
and can produce the next epoch key by sampling a scalar. `recvReady x` means
the party holds its previously sampled scalar `x : F` and can receive the next
DH public value. -/
-- ANCHOR: CKAState
inductive CKAState (F G : Type) where
  /-- Holds the peer's current DH public value and is ready to send. -/
  | sendReady : G → CKAState F G
  /-- Holds the party's sampled scalar and is ready to receive. -/
  | recvReady : F → CKAState F G
  deriving DecidableEq, Fintype, Repr
-- ANCHOR_END: CKAState

/-- `send(h : G)`: `x ← $ᵗ F`; `key := x • h`, `msg := x • gen`, `st' := x`. -/
def send (gen : G) (st : CKAState F G) : ProbComp (Option (G × G × CKAState F G)) :=
  match st with
  | .sendReady h => do
    let x ← $ᵗ F
    let key := x • h
    let msg := x • gen
    let st' : CKAState F G := .recvReady x
    return some (key, msg, st')
  | .recvReady _ => return none

/-- `send_rleak(h : G)`: as `send`, additionally leaking the sampled scalar `x`. -/
def send_rleak (gen : G) (st : CKAState F G) :
    ProbComp (Option (G × G × CKAState F G × F)) :=
  match st with
  | .sendReady h => do
    let x ← $ᵗ F
    let key := x • h
    let msg := x • gen
    let st' : CKAState F G := .recvReady x
    return some (key, msg, st', x)
  | .recvReady _ => return none

/-- `recv(x : F, ρ : G)`: `key := x • ρ`, `st' := ρ`. -/
def recv (st : CKAState F G) (ρ : G) : Option (G × CKAState F G) :=
  match st with
  | .recvReady x =>
    let key := x • ρ
    let st' : CKAState F G := .sendReady ρ
    some (key, st')
  | .sendReady _ => none

/-- CKA from DDH over a module `Module F G` with generator `gen : G`.

- `initKeyGen`: `x₀ ← $ᵗ F`; return `(x₀ • gen, x₀)`.
- `initA (h, x₀)`: store `h : G`. `initB (h, x₀)`: store `x₀ : F`.
- `sendA(h: G)` and `sendB(h: G)`: defined as `send(h: G)` above.
- `recvA(x: F, ρ: G)` and `recvB(x: F, ρ: G)` defined as `recv(x: F, ρ: G)` above.
-/
-- The `Fintype F`, `DecidableEq F`, and `SampleableType G` instances are unused
-- in the construction itself but kept to align with the security theorems about
-- `ddhCKA`, which require them.
@[nolint unusedArguments]
-- ANCHOR: ddhCKA
def ddhCKA (F G : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G] [SampleableType G]
  (gen : G) : CKAScheme ProbComp (G × F) (CKAState F G) G G F where
  initKeyGen := do
    let x ← $ᵗ F
    return (x • gen, x)
  initA := fun (h, _) => return .sendReady h
  initB := fun (_, x) => return .recvReady x
  sendA := send gen
  sendA_rleak := send_rleak gen
  sendB := send gen
  sendB_rleak := send_rleak gen
  recvA := recv
  recvB := recv
-- ANCHOR_END: ddhCKA
