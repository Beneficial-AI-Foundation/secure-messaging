/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.OracleComp.Constructions.BitVec
import ToVCVio.OracleComp.SimSemantics.UnifLift
import VCVio.OracleComp.SimSemantics.Append

/-!
# Wegman-Carter one-time authenticity: the scheme and the game

## Scheme

A Wegman-Carter tag authenticates data under two shared secrets: a key `H` of a hash family and
a one-time mask. Here the data is a message body together with unencrypted associated data.

Let `M`, `Cb`, `A`, `K` and `D` be the plaintext, body, associated-data, key and hash-input
types. The following functions are fixed and public:

    hash   : K → D → BitVec 128
    enc    : A × Cb → D           encoding of the hash input (not encryption)
    padMsg : M → Cb               produces the body
    unpad  : Cb → M               recovers a message from a body

The secrets are drawn uniformly and independently, and `⊕` is bitwise XOR:

    H ←$ K;  mask ←$ BitVec 128
    tag(x : D) := hash(H, x) ⊕ mask

For plaintext `m` and associated data `ad`, the ciphertext is `(c, tag(enc(ad, c)))` with
`c := padMsg(m)`. Nothing here needs `c` to hide `m`, or `unpad` to invert `padMsg`.

## Game

An adversary over `wcSpec A M Cb` runs against `wcInstImpl … b` for a bit `b`, with the
secrets drawn as above:

    challenge := none; forged := false
    Enc(ad, m):
      if challenge ≠ none then return none
      c := padMsg(m); e := (c, tag(enc(ad, c)))
      challenge := some(e); return some(e)
    Dec(ad, e = (c, t)):
      if challenge = some(e) then return none
      ok := (t = tag(enc(ad, c)))
      forged := forged ∨ ok
      return if b ∧ ok then some(unpad(c)) else none

The challenge check compares ciphertexts only and ignores `ad`; verification does not.
Decryption queries may come before or after the single encryption query, which is optional.
The adversary never sees `forged`. At `b = false` every decryption returns `none`; this is the
execution the bound in `Security.lean` is about.
-/

open OracleSpec OracleComp ENNReal ToVCVio

namespace OracleComp.WegmanCarter

/-- The game's oracle spec: uniform sampling, the one-shot encryption oracle and the decryption
oracle. It equals `aeadOneTimeCCASpec` in `SecureMessaging/AEAD/Defs.lean`, restated because
`ToVCVio` does not import `SecureMessaging`. -/
abbrev wcSpec (A M Cb : Type) :=
  unifSpec + (A × M →ₒ Option (Cb × BitVec 128)) + (A × (Cb × BitVec 128) →ₒ Option M)

/-! ## The flag-instrumented handler -/

/-- `wcInstImpl hash enc H mask padMsg unpad b` is the flag-instrumented Wegman-Carter handler
with key `H` and mask `mask`. Its state is the challenge ciphertext slot and a `forged` flag.
Decryption rejects the challenge ciphertext, raises the flag whenever the tag verifies and never
lowers it, and returns the plaintext only when `b = true`; `b = false` is the always-reject
execution. -/
def wcInstImpl {K A M Cb D : Type} [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D)
    (H : K) (mask : BitVec 128)
    (padMsg : M → Cb) (unpad : Cb → M) (b : Bool) :
    QueryImpl (wcSpec A M Cb)
      (StateT (Option (Cb × BitVec 128) × Bool) ProbComp) :=
  (unifLiftStateT (Option (Cb × BitVec 128) × Bool) unifSpec)
  + ((fun (ad, m) => do
      let (challenge, forged) ← get
      match challenge with
      | some _ => pure none
      | none => do
        let c := padMsg m
        let e := (c, hash H (enc (ad, c)) ^^^ mask)
        set ((some e, forged) : Option (Cb × BitVec 128) × Bool)
        return some e) : QueryImpl (A × M →ₒ Option (Cb × BitVec 128))
      (StateT (Option (Cb × BitVec 128) × Bool) ProbComp))
  + ((fun (ad, e) => do
      let (challenge, forged) ← get
      if challenge == some e then pure none
      else do
        let ok : Bool := decide (e.2 = hash H (enc (ad, e.1)) ^^^ mask)
        set ((challenge, forged || ok) : Option (Cb × BitVec 128) × Bool)
        if ok then (if b then pure (some (unpad e.1)) else pure none) else pure none) :
    QueryImpl (A × (Cb × BitVec 128) →ₒ Option M)
      (StateT (Option (Cb × BitVec 128) × Bool) ProbComp))

end OracleComp.WegmanCarter
