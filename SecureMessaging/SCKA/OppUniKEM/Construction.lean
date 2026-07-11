/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs
import SecureMessaging.KEM.OnOffKEM.Defs
import SecureMessaging.ErasureCode.Defs
import ToVCVio.CryptoFoundations.KeyEncapMech

/-!
# Opp-UniKEM-CKA (SCKA from an offline-online KEM + erasure code)

`Opp-UniKEM-CKA` protocol from Figure 16 in [SCKA] https://eprint.iacr.org/2025/2267.pdf.


## Building blocks
- KEM Scheme `kem : KEMScheme m K PK SK C` with
  - `onoff : kem.OnOffStructure` — offline (`Enc.Off`) / online (`Enc.On`) structure,
  - `detDecaps : kem.DeterministicDecaps` — deterministic decapsulation,
  - `leak : KEMScheme.OnOffRandLeak kem onoff` — phase-specific randomness leakage
    for `KeyGen`, `Enc.Off`, and `Enc.On`.
- Erasure Codes for payloads of type
  -  `PK`: `ecEk : ErasureCodePayload PK Sym`,
  -  `onoff.C₀`: `ecCt0 : ErasureCodePayload onoff.C₀ Sym`,
  -  `onoff.C₁`: `ecCt1 : ErasureCodePayload onoff.C₁ Sym`,

## Modeling notes
The algorithms follow Figure 16 with the following differences:

- **Leaking sends.** `sendArleak`/`sendBrleak` are `sendA`/`sendB` with each
  randomized KEM call replaced by its leaking version from `OnOffRandLeak`,
  returning the coins of exactly the KEM phases run by that send.
- **Acknowledgement update.** The acknowledgement bits of a message refer to
  the payloads of its epoch `t'`, so a receive algorithm copies them into the state only
  if the state is still in epoch `t'` after other state updates.
  Figure 16 instead tests `t = t'` at entry (`Rec-A`) or not at all (`Rec-B`),
  which lets an old epoch's acknowledgement incorrectly mark the next epoch's fresh
  payload as already delivered.
- **Totality.** Figure 16 is partial on unreachable malformed states, for example
  when `Rec-A` reaches `Dec` without both `dk_A` and `ct_0`.  In Lean, the
  algorithms are total: locally undefined payload-processing branches output no
  key and perform no branch-specific state update.
-/

open OracleSpec OracleComp KEMScheme


universe u

namespace oppUniKemCKA

/-- Acknowledgement flags for an epoch: whether B has received A's
encapsulation key (`ekRec`) and whether A has received B's offline ciphertext
(`ctRec`). -/
structure Ack where
  /-- `ack.ek-rec`: peer received the encapsulation key of this epoch. -/
  ekRec : Bool
  /-- `ack.ct₀-rec`: peer received the offline ciphertext of this epoch. -/
  ctRec : Bool

/-- Payload selector `b`: bit `0` for `ct_0`, bit `1` for `ct_1`. -/
abbrev Bit : Type := Fin 2

/-- Message type `ρ = (ch, ack, t, [b])`.

- `ch?`  : erasure-code chunk `(index, symbol)` (`⊥` if none sent);
- `ack`  : acknowledgement flags;
- `t`    : the epoch of the transmitted message;
- `b?`   : when B is the sender, this records
  which payload the chunk belongs to — `0` = `ct_0`, `1` = `ct_1` -/
abbrev Message (Sym : Type) : Type :=
  Option (ℕ × Sym) × Ack × ℕ × Option Bit

/-- Randomness type returned by an Opp-UniKEM leaking send.

Depending on the role and state of the sending party, various branches of
the sending algorithm may produce different types of randomness that can be leaked. -/
inductive SendRand (KeygenRand OffRand OnRand : Type) where
  /-- No randomized primitive was run by this send. -/
  | none
  /-- Party A generated a fresh encapsulation/decapsulation key pair. -/
  | keygen (r : KeygenRand)
  /-- Party B ran the offline encapsulation phase `Enc.Off`. -/
  | off (r : OffRand)
  /-- Party B ran the online encapsulation phase `Enc.On`. -/
  | on (r : OnRand)
  /-- Party B ran both `Enc.Off` and `Enc.On` in one send. -/
  | offOn (rOff : OffRand) (rOn : OnRand)

/-- Party **A**'s state `(dk_A, ek_A, ct_0, t, i_ch, L_ch, ack)`. -/
structure StateA (SK PK Coff Sym : Type) where
  /-- `dk_A`: A's decapsulation key for the current epoch. -/
  dkA : Option SK
  /-- `ek_A`: A's encapsulation key being transmitted. -/
  ekA : Option PK
  /-- `ct_0`: the offline ciphertext recovered from B. -/
  ct0 : Option Coff
  /-- `t`: current epoch. -/
  t : ℕ
  /-- `i_ch`: chunk counter. -/
  ich : ℕ
  /-- `L_ch`: received-chunk list as `(index, symbol)` pairs. -/
  lch : Finset (ℕ × Sym)
  /-- Acknowledgement flags. -/
  ack : Ack

/-- Party **B**'s state `(ek_A, ct_0, ct_1, st_ct, t, i_ch, L_ch, ack)`. -/
structure StateB (PK Coff Con StOff Sym : Type) where
  /-- `ek_A`: A's encapsulation key recovered by B. -/
  ekA : Option PK
  /-- `ct_0`: offline ciphertext produced by `Enc.Off`, being transmitted. -/
  ct0 : Option Coff
  /-- `ct_1`: online ciphertext produced by `Enc.On`, being transmitted. -/
  ct1 : Option Con
  /-- `st_ct`: offline-KEM state from `Enc.Off`. -/
  stCt : Option StOff
  /-- `t`: current epoch. -/
  t : ℕ
  /-- `i_ch`: chunk counter. -/
  ich : ℕ
  /-- `L_ch`: received-chunk list as `(index, symbol)` pairs. -/
  lch : Finset (ℕ × Sym)
  /-- Acknowledgement flags. -/
  ack : Ack

section Construction

variable {m : Type → Type u} [Monad m] {K PK SK C Sym : Type}

/-- A's state specialised to the KEM's offline ciphertext space and the shared
chunk alphabet. -/
abbrev StA {kem : KEMScheme m K PK SK C} (onoff : kem.OnOffStructure)
    (Sym : Type) : Type :=
  StateA SK PK onoff.C₀ Sym

/-- B's state specialised to the KEM's offline/online ciphertext and offline
state spaces and the shared chunk alphabet. -/
abbrev StB {kem : KEMScheme m K PK SK C} (onoff : kem.OnOffStructure)
    (Sym : Type) : Type :=
  StateB PK onoff.C₀ onoff.C₁ onoff.St Sym

/-- `CKA-Init-KeyGen`: `I_CKA := ⊥` (there is no shared initial key). -/
-- ANCHOR: initAlgorithms
def initKeyGen : m Unit := pure ()

/-- `CKA-Init-A`: `st_A ← (⊥, ⊥, ⊥, 1, 0, ∅, (false, false))`. -/
def initA (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (_ik : Unit) : m (StA onoff Sym) :=
  pure { dkA := none, ekA := none, ct0 := none, t := 1, ich := 0, lch := ∅,
         ack := { ekRec := false, ctRec := false } }

/-- `CKA-Init-B`: `st_B ← (⊥, ⊥, ⊥, ⊥, 1, 0, ∅, (false, false))`. -/
def initB (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (_ik : Unit) : m (StB onoff Sym) :=
  pure { ekA := none, ct0 := none, ct1 := none, stCt := none, t := 1, ich := 0,
         lch := ∅, ack := { ekRec := false, ctRec := false } }
-- ANCHOR_END: initAlgorithms

/-- `CKA-Send-A`.

```text
parse (dk_A, ek_A, ct_0, t, i_ch, L_ch, ack) <- st_A
ch <- ⊥
if dk_A = ⊥ then
  (ek_A, dk_A) <- KeyGen
  i_ch <- 0
if ¬ack.ek-rec then
  i_ch <- i_ch + 1
  ch <- Encode(ek_A, i_ch)
rho <- (ch, ack, t, ⊥)
st_A <- (dk_A, ek_A, ct_0, t, i_ch, L_ch, ack)
return ((⊥, ⊥), rho, t - 1, st_A)
``` -/
-- ANCHOR: sendA
def sendA (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
  (ecEk : ErasureCodePayload PK Sym) (stA : StA onoff Sym) :
    m (Option (Option (ℕ × K) × Message Sym × ℕ × StA onoff Sym)) := do
-- ANCHOR_END: sendA
  let (dkA, ekA, ich) ←
    match stA.dkA with
    | none => do
        let (ekA, dkA) ← kem.keygen
        pure (some dkA, some ekA, 0)
    | some dkA =>
        pure (some dkA, stA.ekA, stA.ich)
  let ich := if stA.ack.ekRec then ich else ich + 1
  let ch? : Option (ℕ × Sym) :=
    if stA.ack.ekRec then
      none
    else
      match ekA with
      | none => none
      | some ekA =>
          some (ich, ecEk.encode ekA ich)
  let msg := (ch?, stA.ack, stA.t, none)
  let stA' := { stA with dkA := dkA, ekA := ekA, ich := ich }
  pure (some (none, msg, stA.t - 1, stA'))

/-- Randomness-leaking `CKA-Send-A`, also returning the send coins.

The only randomized primitive in `CKA-Send-A` is `KeyGen`, and it is used only
on the first message of an epoch. Later sends only repeat deterministic chunk
encoding, so they leak `SendRand.none`. -/
-- ANCHOR: sendArleak
def sendArleak (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
  (leak : KEMScheme.OnOffRandLeak kem onoff) (stA : StA onoff Sym) :
  m (Option (Option (ℕ × K) × Message Sym × ℕ × StA onoff Sym ×
    SendRand leak.KeygenRand leak.OffRand leak.OnRand)) := do
-- ANCHOR_END: sendArleak
    let (dkA, ekA, ich, rand) ←
      match stA.dkA with
      | none => do
        -- First epoch send: run the leaking KeyGen and remember its coins.
          let ((ekA, dkA), rKeygen) ← leak.keygenRleak
          pure (some dkA, some ekA, 0, SendRand.keygen rKeygen)
      | some dkA =>
        -- Subsequent chunk sends are deterministic, so no primitive coins leak.
          pure (some dkA, stA.ekA, stA.ich, SendRand.none)
    let ich := if stA.ack.ekRec then ich else ich + 1
    let ch? : Option (ℕ × Sym) :=
      if stA.ack.ekRec then
        none
      else
        match ekA with
        | none => none
        | some ekA =>
            some (ich, ecEk.encode ekA ich)
    let msg := (ch?, stA.ack, stA.t, none)
    let stA' := { stA with dkA := dkA, ekA := ekA, ich := ich }
    -- normal send output plus randomness-leakage
    pure (some (none, msg, stA.t - 1, stA', rand))

/-- `CKA-Rec-A`.

```text
parse (dk_A, ek_A, ct_0, t, i_ch, L_ch, ack) <- st_A
parse (ch, ack', t', b) <- rho
I_B <- ⊥, t_IB <- ⊥
  if t = t' then
  if ct_0 = ⊥ ∧ b = 0 then
    L_ch <- L_ch ∪ {ch}
    ct_0 <- Decode(L_ch)
    if ct_0 ≠ ⊥ then
      ack.ct_0-rec <- true
      L_ch <- ∅
  elseif b = 1 then
    L_ch <- L_ch ∪ {ch}
    ct_1 <- Decode(L_ch)
    if ct_1 ≠ ⊥ then
      I_B <- Dec(dk_A, (ct_0, ct_1))
      t_IB <- t
      t <- t + 1
      L_ch <- ∅
      (dk_A, ek_A, ct_0) <- (⊥, ⊥, ⊥)
      (ack.ek-rec, ack.ct_0-rec) <- (false, false)
  if ack'.ek-rec and t = t' then
    ack.ek-rec <- true
st_A <- (dk_A, ek_A, ct_0, t, i_ch, L_ch, ack)
return ((t_IB, I_B), t' - 1, st_A)
``` -/
-- ANCHOR: recvA
def recvA (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    [DecidableEq Sym]
  (hDet : kem.DeterministicDecaps)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
  (stA : StA onoff Sym) (ρ : Message Sym) :
    Option (Option (ℕ × K) × ℕ × StA onoff Sym) :=
-- ANCHOR_END: recvA
  let (ch?, ack', t', b?) := ρ
  let (key?, stA') :=
    if stA.t = t' then
      let (key?, stA') :=
        match stA.ct0, b?, ch? with
        | none, some 0, some ch =>
            -- `ct_0` not received yet
            let lch := insert ch stA.lch
            match ecCt0.decode lch with
            -- still not received enough chunks to decode `ct_0`
            | none => (none, { stA with ct0 := none, lch := lch })
            -- decoded `ct_0` successfully
            | some ct0 =>
                (none,
                  { stA with
                    ct0 := some ct0
                    lch := ∅
                    ack := { stA.ack with ctRec := true } })
        | _, some 1, some ch =>
        -- processing `ct_1` chunks; without `dk_A` or `ct_0`, output no key
        -- and leave state unchanged
            match stA.dkA, stA.ct0 with
            | some dkA, some ct0 =>
                let lch := insert ch stA.lch
                match ecCt1.decode lch with
                | none => (none, { stA with lch := lch })
                | some ct1 =>
                -- decoded `ct_1` successfully; decapsulate (ct_0, ct_1) to get an epoch key
                  match hDet.decapsDet dkA (onoff.split.symm (ct0, ct1)) with
                  | none => (none, stA)
                  | some key =>
                      (some (stA.t, key),
                        { stA with
                          dkA := none
                          ekA := none
                          ct0 := none
                          t := stA.t + 1
                          lch := ∅
                          ack := { ekRec := false, ctRec := false } })
            | _, _ => (none, stA)
        | _, _, _ => (none, stA)
      -- Incorporate B's acknowledgement only if this receive did not advance A
      -- to the next epoch; otherwise a final `ct_1` message would carry the old
      -- epoch's ack into the fresh epoch.
      let stA' :=
        if ack'.ekRec && stA'.t == t' then
          { stA' with ack := { stA'.ack with ekRec := true } }
        else
          stA'
      (key?, stA')
    else
      (none, stA)
  some (key?, t' - 1, stA')

/-- `CKA-Send-B`.

```text
parse (ek_A, ct_0, ct_1, st_ct, t, i_ch, L_ch, ack) <- st_B
I_B <- ⊥, t_IB <- ⊥, ch <- ⊥
if ct_0 = ⊥ then  -- first message of the epoch: run offline encapsulation
  (st_ct, ct_0) <- Enc.Off
  i_ch <- 0
if ¬ack.ct_0-rec then -- `ct_0` not yet acknowledged by A: send chunks of `ct_0`
  i_ch <- i_ch + 1
  ch <- Encode(ct_0, i_ch)
  b <- 0
elseif ek_A ≠ ⊥ then -- `ek_A` received: run online encapsulation and send chunks of `ct_1`
  if ct_1 = ⊥ then
    (ct_1, I_B) <- Enc.On(st_ct, ek_A)
    t_IB <- t
    i_ch <- 0
  i_ch <- i_ch + 1
  ch <- Encode(ct_1, i_ch)
  b <- 1
rho <- (ch, ack, t, b)
st_B <- (ek_A, ct_0, ct_1, st_ct, t, i_ch, L_ch, ack)
return ((t_IB, I_B), rho, t - 1, st_B)
``` -/
-- ANCHOR: sendB
def sendB (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (stB : StB onoff Sym) :
    m (Option (Option (ℕ × K) × Message Sym × ℕ × StB onoff Sym)) := do
-- ANCHOR_END: sendB
  let (stB, ct0, ich) ←
  match stB.ct0 with
  | none => do -- first message of the epoch: run offline encapsulation
    let (stCt, ct0) ← onoff.encapsOff
    pure ({ stB with stCt := some stCt, ct0 := some ct0 }, ct0, 0)
  | some ct0 =>
    pure (stB, ct0, stB.ich)
  if !stB.ack.ctRec then -- `ct_0` not yet acknowledged by A: send chunks of `ct_0`
  let ich := ich + 1
  let ch? := some (ich, ecCt0.encode ct0 ich)
  let msg := (ch?, stB.ack, stB.t, some 0)
  let stB' := { stB with ich := ich }
  pure (some (none, msg, stB.t - 1, stB'))
  else
  match stB.ekA with
  | none =>  -- `ek_A` not yet received
    let msg := (none, stB.ack, stB.t, none)
    pure (some (none, msg, stB.t - 1, stB))
  | some ekA => -- `ek_A` received
    match stB.ct1 with
    | none =>
      match stB.stCt with
      | none =>
        let msg := (none, stB.ack, stB.t, some 1)
        pure (some (none, msg, stB.t - 1, stB))
      | some stCt => do
        let (ct1, key) ← onoff.encapsOn stCt ekA
        let ich := 1
        let ch? := some (ich, ecCt1.encode ct1 ich)
        let msg := (ch?, stB.ack, stB.t, some 1)
        let stB' := { stB with ct1 := some ct1, ich := ich }
        pure (some (some (stB.t, key), msg, stB.t - 1, stB'))
    | some ct1 =>
      let ich := stB.ich + 1
      let ch? := some (ich, ecCt1.encode ct1 ich)
      let msg := (ch?, stB.ack, stB.t, some 1)
      let stB' := { stB with ich := ich }
      pure (some (none, msg, stB.t - 1, stB'))

/-- Randomness-leaking `CKA-Send-B`: follows `sendB` branch-for-branch, also
returning the coins of the encapsulation phases run by this send. -/
-- ANCHOR: sendBrleak
def sendBrleak (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff) (stB : StB onoff Sym) :
    m (Option (Option (ℕ × K) × Message Sym × ℕ × StB onoff Sym ×
      SendRand leak.KeygenRand leak.OffRand leak.OnRand)) :=
  do
-- ANCHOR_END: sendBrleak
    let (stB, ct0, ich, rOff?) ←
      match stB.ct0 with
      | none => do
        -- First `ct_0` send: run leaking offline encapsulation.
        let ((stCt, ct0), rOff) ← leak.encapsOffRleak
        pure ({ stB with stCt := some stCt, ct0 := some ct0 }, ct0, 0, some rOff)
      | some ct0 =>
        -- Re-sending existing `ct_0` is deterministic.
        pure (stB, ct0, stB.ich, none)
    let offRand :=
      match rOff? with
      | none => SendRand.none
      | some rOff => SendRand.off rOff
    if !stB.ack.ctRec then
      let ich := ich + 1
      let ch? := some (ich, ecCt0.encode ct0 ich)
      let msg := (ch?, stB.ack, stB.t, some 0)
      let stB' := { stB with ich := ich }
      pure (some (none, msg, stB.t - 1, stB', offRand))
    else
      match stB.ekA with
      | none =>
        let msg := (none, stB.ack, stB.t, none)
        pure (some (none, msg, stB.t - 1, stB, offRand))
      | some ekA =>
        match stB.ct1 with
        | none =>
          match stB.stCt with
          | none =>
            let msg := (none, stB.ack, stB.t, some 1)
            pure (some (none, msg, stB.t - 1, stB, offRand))
          | some stCt => do
            -- First `ct_1` send: run leaking online encapsulation.
            let ((ct1, key), rOn) ← leak.encapsOnRleak stCt ekA
            let rand :=
              match rOff? with
              | none => SendRand.on rOn
              | some rOff => SendRand.offOn rOff rOn
            let ich := 1
            let ch? := some (ich, ecCt1.encode ct1 ich)
            let msg := (ch?, stB.ack, stB.t, some 1)
            let stB' := { stB with ct1 := some ct1, ich := ich }
            pure (some (some (stB.t, key), msg, stB.t - 1, stB', rand))
        | some ct1 =>
          -- Re-sending existing `ct_1` is deterministic.
          let ich := stB.ich + 1
          let ch? := some (ich, ecCt1.encode ct1 ich)
          let msg := (ch?, stB.ack, stB.t, some 1)
          let stB' := { stB with ich := ich }
          pure (some (none, msg, stB.t - 1, stB', offRand))

/-- `CKA-Rec-B`.

```text
parse (ek_A, ct_0, ct_1, st_ct, t, i_ch, L_ch, ack) <- st_B
parse (ch, ack', t', _) <- rho
if t < t' then  -- first message of next epoch
  t <- t + 1
  (ct_0, ct_1, st_ct) <- (⊥, ⊥, ⊥)
  (ek_A, L_ch) <- (⊥, ∅)
  (ack.ek-rec, ack.ct_0-rec) <- (false, false)
if t = t' ∧ ek_A = ⊥ then
  L_ch <- L_ch ∪ {ch}
  ek_A <- Decode(L_ch)
  ack.ek-rec <- (ek_A ≠ ⊥)
if ack'.ct_0-rec and t = t' then  -- incorporate A's acknowledgment
  ack.ct_0-rec <- true
st_B <- (ek_A, ct_0, ct_1, st_ct, t, i_ch, L_ch, ack)
return ((⊥, ⊥), t' - 1, st_B)
``` -/
-- ANCHOR: recvB
def recvB (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    [DecidableEq Sym]
    (ecEk : ErasureCodePayload PK Sym) (stB : StB onoff Sym) (ρ : Message Sym) :
    Option (Option (ℕ × K) × ℕ × StB onoff Sym) :=
-- ANCHOR_END: recvB
  let (ch?, ack', t', _b?) := ρ
  -- first message of the next epoch: advance and reset the per-epoch state
  let stB :=
    if stB.t < t' then
      { stB with
        t := stB.t + 1
        ct0 := none, ct1 := none, stCt := none
        ekA := none, lch := ∅
        ack := { ekRec := false, ctRec := false } }
    else
      stB
  -- collect chunks of `ek_A` for the current epoch
  let stB :=
    if stB.t = t' ∧ stB.ekA.isNone then
      let lch :=
        match ch? with
        | none => stB.lch
        | some ch => insert ch stB.lch
      let ekA? := ecEk.decode lch
      { stB with ekA := ekA?, lch := lch, ack := { stB.ack with ekRec := ekA?.isSome } }
    else
      stB
  -- incorporate A's acknowledgement only for messages of the current epoch
  let stB :=
    if ack'.ctRec && stB.t == t' then
      { stB with ack := { stB.ack with ctRec := true } }
    else
      stB
  some (none, t' - 1, stB)

/-- A's vulnerable epoch set (Fig. 16: `{t}` iff `dk_A ≠ ⊥`). -/
-- ANCHOR: vulnerableStates
def vulnA (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (stA : StA onoff Sym) : Finset ℕ :=
  if stA.dkA.isSome then {stA.t} else ∅

/-- B's vulnerable epoch set (Fig. 16: `{t}` iff `st_ct ≠ ⊥`). -/
def vulnB (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (stB : StB onoff Sym) : Finset ℕ :=
  if stB.stCt.isSome then {stB.t} else ∅
-- ANCHOR_END: vulnerableStates

/-- The Opp-UniKEM-CKA protocol as an `SCKAScheme` instance. -/
-- ANCHOR: scheme
def scheme (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
  [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff) :
    SCKAScheme m Unit (StA onoff Sym) (StB onoff Sym) K (Message Sym)
      (SendRand leak.KeygenRand leak.OffRand leak.OnRand) where
  initKeyGen := initKeyGen
  initA := initA kem onoff
  initB := initB kem onoff
  sendA := sendA kem onoff ecEk
  sendArleak := sendArleak kem onoff ecEk leak
  recvA := recvA kem onoff hDet ecCt0 ecCt1
  sendB := sendB kem onoff ecCt0 ecCt1
  sendBrleak := sendBrleak kem onoff ecCt0 ecCt1 leak
  recvB := recvB kem onoff ecEk
-- ANCHOR_END: scheme

end Construction

end oppUniKemCKA
