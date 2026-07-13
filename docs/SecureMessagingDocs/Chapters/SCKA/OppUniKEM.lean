import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Bibliography
import SecureMessaging.SCKA.OppUniKEM.Construction

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true

open Verso.Genre
open Verso.Genre.Manual
open Verso.Code.External
open Informal

set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Opp-UniKEM-CKA" =>

:::group "cka_protocols_opp_unikem_cka"
Opp-UniKEM-CKA.
:::

:::defTitle "opp_unikem_cka_spec" "Opp-UniKEM-CKA protocol"
:::

:::::::definition "opp_unikem_cka_spec" (parent := "cka_protocols_opp_unikem_cka") (lean := "oppUniKemCKA.initKeyGen, oppUniKemCKA.initA, oppUniKemCKA.initB, oppUniKemCKA.vulnA, oppUniKemCKA.vulnB, oppUniKemCKA.sendA, oppUniKemCKA.sendArleak, oppUniKemCKA.recvA, oppUniKemCKA.sendB, oppUniKemCKA.sendBrleak, oppUniKemCKA.recvB, oppUniKemCKA.scheme")
Specification of the Opp-UniKEM-CKA protocol from Figure 16 of
{Informal.citet SCKA25}[].
::::::gameGrid
:::::gameCell "\\textsf{Initialisation}" (kind := "compact")
$`\mathsf{CKA}\text{-}\mathsf{InitKeyGen}(): \quad
I_{\mathsf{CKA}}\gets\bot;\quad \mathsf{return}\;I_{\mathsf{CKA}}`
```anchor initKeyGen (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def initKeyGen : m Unit := pure ()
```

$`\mathsf{CKA}\text{-}\mathsf{Init}\text{-}\mathsf{A}(\bot): \quad
\stA\gets(\bot,\bot,\bot,1,0,\emptyset,(\mathsf{false},\mathsf{false}));\quad
\mathsf{return}\;\stA`
```anchor initA (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def initA (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (_ik : Unit) : m (StA onoff Sym) :=
  pure { dkA := none, ekA := none, ct0 := none, t := 1, ich := 0, lch := ∅,
         ack := { ekRec := false, ctRec := false } }
```

$`\mathsf{CKA}\text{-}\mathsf{Init}\text{-}\mathsf{B}(\bot): \quad
\stB\gets(\bot,\bot,\bot,\bot,1,0,\emptyset,(\mathsf{false},\mathsf{false}));\quad
\mathsf{return}\;\stB`
```anchor initB (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def initB (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (_ik : Unit) : m (StB onoff Sym) :=
  pure { ekA := none, ct0 := none, ct1 := none, stCt := none, t := 1, ich := 0,
         lch := ∅, ack := { ekRec := false, ctRec := false } }
```
:::::

:::::gameCell "\\textsf{Vulnerable epochs}" (kind := "compact")
$`\stA.\mathsf{vuln}: \quad
\mathsf{return}\;\{t\}\;\mathsf{if}\;dk_A\ne\bot\;\mathsf{else}\;\emptyset`
```anchor vulnA (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def vulnA (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (stA : StA onoff Sym) : Finset ℕ :=
  if stA.dkA.isSome then {stA.t} else ∅
```

$`\stB.\mathsf{vuln}: \quad
\mathsf{return}\;\{t\}\;\mathsf{if}\;st_{ct}\ne\bot\;\mathsf{else}\;\emptyset`
```anchor vulnB (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def vulnB (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (stB : StB onoff Sym) : Finset ℕ :=
  if stB.stCt.isSome then {stB.t} else ∅
```
:::::

:::::gameCell "\\mathsf{CKA}\text{-}\\mathsf{Send}\text{-}\\mathsf{A}(\\stA)" (kind := "compact-send")
$`\begin{array}{l}
(dk_A,ek_A,ct_0,t,i_{ch},L_{ch},ack)\gets\stA \\
ch\gets\bot \\
\mathsf{if}\;dk_A=\bot\;\mathsf{then} \\
\quad (ek_A,dk_A)\sample\KeyGen \\
\quad i_{ch}\gets0 \\
\mathsf{if}\;\neg ack.ek\text{-}rec\;\mathsf{then} \\
\quad i_{ch}\gets i_{ch}+1 \\
\quad ch\gets\mathsf{Encode}(ek_A,i_{ch}) \\
\rho\gets(ch,ack,t,\bot) \\
\stA\gets(dk_A,ek_A,ct_0,t,i_{ch},L_{ch},ack) \\
\mathsf{return}\;((\bot,\bot),\rho,t-1,\stA)
\end{array}`

```anchor sendA (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def sendA (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
  (ecEk : ErasureCodePayload PK Sym) (stA : StA onoff Sym) :
    m (Option (Option (ℕ × K) × Message Sym × ℕ × StA onoff Sym)) := do
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
```

:::leanPillCaption "rleak version leaking KeyGen coins"
:::
```anchor sendArleak (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def sendArleak (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
  (leak : KEMScheme.OnOffRandLeak kem onoff) (stA : StA onoff Sym) :
  m (Option (Option (ℕ × K) × Message Sym × ℕ × StA onoff Sym ×
    SendRand leak.KeygenRand leak.OffRand leak.OnRand)) := do
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
```
:::::

:::::gameCell "\\mathsf{CKA}\text{-}\\mathsf{Rec}\text{-}\\mathsf{A}(\\stA,\\rho)" (kind := "compact-recv")
$`\begin{array}{l}
(dk_A,ek_A,ct_0,t,i_{ch},L_{ch},ack)\gets\stA \\
(ch,ack',t',b)\gets\rho \\
I_B\gets\bot \\
t_{I_B}\gets\bot \\
\mathsf{if}\;t=t'\;\mathsf{then} \\
\quad \mathsf{if}\;ct_0=\bot\wedge b=0\;\mathsf{then} \\
\qquad L_{ch}\gets L_{ch}\cup\{ch\} \\
\qquad ct_0\gets\mathsf{Decode}(L_{ch}) \\
\qquad \mathsf{if}\;ct_0\ne\bot\;\mathsf{then} \\
\qquad\quad ack.ct_0\text{-}rec\gets\mathsf{true} \\
\qquad\quad L_{ch}\gets\emptyset \\
\quad \mathsf{else}\;\mathsf{if}\;b=1\;\mathsf{then} \\
\qquad L_{ch}\gets L_{ch}\cup\{ch\} \\
\qquad ct_1\gets\mathsf{Decode}(L_{ch}) \\
\qquad \mathsf{if}\;ct_1\ne\bot\;\mathsf{then} \\
\qquad\quad I_B\gets\Decaps(dk_A,(ct_0,ct_1)) \\
\qquad\quad t_{I_B}\gets t \\
\qquad\quad t\gets t+1 \\
\qquad\quad L_{ch}\gets\emptyset \\
\qquad\quad (dk_A,ek_A,ct_0)\gets(\bot,\bot,\bot) \\
\qquad\quad (ack.ek\text{-}rec,ack.ct_0\text{-}rec)
  \gets(\mathsf{false},\mathsf{false}) \\
\mathsf{if}\;ack'.ek\text{-}rec\wedge t=t'\;\mathsf{then} \\
\quad ack.ek\text{-}rec\gets\mathsf{true} \\
\stA\gets(dk_A,ek_A,ct_0,t,i_{ch},L_{ch},ack) \\
\mathsf{return}\;((t_{I_B},I_B),t'-1,\stA)
\end{array}`

```anchor recvA (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def recvA (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    [DecidableEq Sym]
  (hDet : kem.DeterministicDecaps)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
  (stA : StA onoff Sym) (ρ : Message Sym) :
    Option (Option (ℕ × K) × ℕ × StA onoff Sym) :=
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
```
:::::

:::::gameCell "\\mathsf{CKA}\text{-}\\mathsf{Send}\text{-}\\mathsf{B}(\\stB)" (kind := "compact-send")
$`\begin{array}{l}
(ek_A,ct_0,ct_1,st_{ct},t,i_{ch},L_{ch},ack)\gets\stB \\
I_B\gets\bot \\
t_{I_B}\gets\bot \\
ch\gets\bot \\
\mathsf{if}\;ct_0=\bot\;\mathsf{then} \\
\quad (st_{ct},ct_0)\sample\Encaps.\mathsf{Off} \\
\quad i_{ch}\gets0 \\
\mathsf{if}\;\neg ack.ct_0\text{-}rec\;\mathsf{then} \\
\quad i_{ch}\gets i_{ch}+1 \\
\quad ch\gets\mathsf{Encode}(ct_0,i_{ch}) \\
\quad b\gets0 \\
\mathsf{else}\;\mathsf{if}\;ek_A\ne\bot\;\mathsf{then} \\
\quad \mathsf{if}\;ct_1=\bot\;\mathsf{then} \\
\qquad (ct_1,I_B)\sample \\
\qquad\quad \Encaps.\mathsf{On}(st_{ct},ek_A) \\
\qquad t_{I_B}\gets t \\
\qquad i_{ch}\gets0 \\
\quad i_{ch}\gets i_{ch}+1 \\
\quad ch\gets\mathsf{Encode}(ct_1,i_{ch}) \\
\quad b\gets1 \\
\rho\gets(ch,ack,t,b) \\
\stB\gets(ek_A,ct_0,ct_1,st_{ct},t,i_{ch},L_{ch},ack) \\
\mathsf{return}\;((t_{I_B},I_B),\rho,t-1,\stB)
\end{array}`

```anchor sendB (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def sendB (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (stB : StB onoff Sym) :
    m (Option (Option (ℕ × K) × Message Sym × ℕ × StB onoff Sym)) := do
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
```

:::leanPillCaption "rleak version leaking encapsulation coins"
:::
```anchor sendBrleak (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def sendBrleak (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff) (stB : StB onoff Sym) :
    m (Option (Option (ℕ × K) × Message Sym × ℕ × StB onoff Sym ×
      SendRand leak.KeygenRand leak.OffRand leak.OnRand)) :=
  do
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
```
:::::

:::::gameCell "\\mathsf{CKA}\text{-}\\mathsf{Rec}\text{-}\\mathsf{B}(\\stB,\\rho)" (kind := "compact-recv")
$`\begin{array}{l}
(ek_A,ct_0,ct_1,st_{ct},t,i_{ch},L_{ch},ack)\gets\stB \\
(ch,ack',t',\_)\gets\rho \\
\mathsf{if}\;t<t'\;\mathsf{then} \\
\quad t\gets t+1 \\
\quad (ct_0,ct_1,st_{ct})\gets(\bot,\bot,\bot) \\
\quad (ek_A,L_{ch})\gets(\bot,\emptyset) \\
\quad (ack.ek\text{-}rec,ack.ct_0\text{-}rec)
  \gets(\mathsf{false},\mathsf{false}) \\
\mathsf{if}\;t=t'\wedge ek_A=\bot\;\mathsf{then} \\
\quad L_{ch}\gets L_{ch}\cup\{ch\} \\
\quad ek_A\gets\mathsf{Decode}(L_{ch}) \\
\quad ack.ek\text{-}rec\gets(ek_A\ne\bot) \\
\mathsf{if}\;ack'.ct_0\text{-}rec\wedge t=t'\;\mathsf{then} \\
\quad ack.ct_0\text{-}rec\gets\mathsf{true} \\
\stB\gets(ek_A,ct_0,ct_1,st_{ct},t,i_{ch},L_{ch},ack) \\
\mathsf{return}\;((\bot,\bot),t'-1,\stB)
\end{array}`

```anchor recvB (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def recvB (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    [DecidableEq Sym]
    (ecEk : ErasureCodePayload PK Sym) (stB : StB onoff Sym) (ρ : Message Sym) :
    Option (Option (ℕ × K) × ℕ × StB onoff Sym) :=
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
```
:::::
::::::

{usesLabel}`uses` {uses "scka_scheme"}[] · {uses "erasure_code_scheme"}[] · {uses "on_off_kem_scheme"}[] · {uses "on_off_kem_rand_leak"}[] · {githubLabel}`github` {githubIssue 106}[]
:::::::

:::defTitle "opp_unikem_cka_correctness" "Opp-UniKEM-CKA correctness"
:::

::::theorem "opp_unikem_cka_correctness" (parent := "cka_protocols_opp_unikem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "opp_unikem_cka_spec"}[] · {uses "scka_correctness"}[] · {uses "erasure_code_correctness"}[] · {uses "on_off_kem_scheme"}[] · {uses "on_off_kem_rand_leak"}[] · {githubLabel}`github` {githubIssue 107}[]
::::

:::defTitle "opp_unikem_cka_security" "Opp-UniKEM-CKA security"
:::

::::theorem "opp_unikem_cka_security" (parent := "cka_protocols_opp_unikem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "opp_unikem_cka_spec"}[] · {uses "scka_security"}[] · {uses "erasure_code_scheme"}[] · {uses "on_off_kem_scheme"}[] · {uses "on_off_kem_rand_leak"}[] · {githubLabel}`github` {githubIssue 108}[]
::::
