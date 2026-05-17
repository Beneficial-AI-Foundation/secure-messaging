/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.Defs
import ToMathlib.Control.StateT
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# Continuous Key Agreement from Decisional Diffie-Hellman Assumption

Construction of a CKA scheme from the DDH following [ACD19, Section 4.1].
https://eprint.iacr.org/2018/1037.pdf

We consider a module `Module F G` with scalar field `F`, additive group `G`,
scalar multiplication `a • gen`, and a fixed generator `gen : G`.

- Initial key space `IK = G × F` — a group element and its discrete log.
- Epoch key space `I = G` — DH shared secrets.
- Message space `Rho = G` — DH public values.
- State space `St = F ⊕ G` — holds :
  A scalar in F after a Send action, or else group element in G after a Recv action.

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

/-- `send(h : G)`: `x ← $ᵗ F`; `key := x • h`, `msg := x • gen`, `st' := x`. -/
def ddhCKA.send (gen : G) (st : F ⊕ G) : ProbComp (Option (G × G × (F ⊕ G))) :=
  match st with
  | .inr h => do
    let x ← $ᵗ F
    let key := x • h
    let msg := x • gen
    let st' : F ⊕ G := .inl x
    return some (key, msg, st')
  | .inl _ => return none

/-- `send_rleak(h : G)`: as `send`, additionally leaking the sampled scalar `x`. -/
def ddhCKA.send_rleak (gen : G) (st : F ⊕ G) :
    ProbComp (Option (G × G × (F ⊕ G) × F)) :=
  match st with
  | .inr h => do
    let x ← $ᵗ F
    let key := x • h
    let msg := x • gen
    let st' : F ⊕ G := .inl x
    return some (key, msg, st', x)
  | .inl _ => return none

/-- `recv(x : F, ρ : G)`: `key := x • ρ`, `st' := ρ`. -/
def ddhCKA.recv (st : F ⊕ G) (ρ : G) : Option (G × (F ⊕ G)) :=
  match st with
  | .inl x =>
    let key := x • ρ
    let st' : F ⊕ G := .inr ρ
    some (key, st')
  | .inr _ => none

/-- CKA from DDH over a module `Module F G` with generator `gen : G`.

- `initKeyGen`: `x₀ ← $ᵗ F`; return `(x₀ • gen, x₀)`.
- `initA (h, x₀)`: store `h : G`. `initB (h, x₀)`: store `x₀ : F`.
- `sendA(h: G)` and `sendB(h: G)`: defined as `send(h: G)` above.
- `recvA(x: F, ρ: G)` and `recvB(x: F, ρ: G)` defined as `recv(x: F, ρ: G)` above.
-/
def ddhCKA (F G : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G] [SampleableType G]
    (gen : G) : CKAScheme ProbComp (G × F) (F ⊕ G) G G F where
  initKeyGen := do
    let x ← $ᵗ F
    return (x • gen, x)
  initA := fun (h, _) => return .inr h
  initB := fun (_, x) => return .inl x
  sendA := ddhCKA.send gen
  sendA_rleak := ddhCKA.send_rleak gen
  sendB := ddhCKA.send gen
  sendB_rleak := ddhCKA.send_rleak gen
  recvA := ddhCKA.recv
  recvB := ddhCKA.recv
