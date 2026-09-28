import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Bibliography
import SecureMessaging.SCKA.OppUniKEM.Correctness
import SecureMessaging.SCKA.OppUniKEM.Security

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
set_option maxHeartbeats 800000
set_option maxRecDepth 16384

#doc (Manual) "Opp-UniKEM-CKA" =>

:::group "cka_protocols_opp_unikem_cka"
Opp-UniKEM-CKA.
:::

:::defTitle "opp_unikem_cka_spec" "Opp-UniKEM-CKA protocol"
:::

:::::::definition "opp_unikem_cka_spec" (parent := "cka_protocols_opp_unikem_cka") (lean := "oppUniKemCKA.initKeyGen, oppUniKemCKA.initA, oppUniKemCKA.initB, oppUniKemCKA.vulnA, oppUniKemCKA.vulnB, oppUniKemCKA.sendExposureA, oppUniKemCKA.sendExposureB, oppUniKemCKA.exposureA, oppUniKemCKA.exposureB, oppUniKemCKA.sendA, oppUniKemCKA.sendArleak, oppUniKemCKA.recvA, oppUniKemCKA.sendB, oppUniKemCKA.sendBrleak, oppUniKemCKA.recvB, oppUniKemCKA.scheme") (tags := "gh-106") (uses := "scka_scheme, erasure_code_scheme, on_off_kem_scheme, on_off_kem_rand_leak")
Figure 16 of {Informal.citet SCKA25}[]. In the receive algorithms,
- $`t` is the epoch index of the receiver's state,
- $`t'` is the epoch index of the delivered message.

We make two corrections to these algorithms, marked with surrounding boxes:

* $`\mathsf{Rec}\text{-}\A` and $`\mathsf{Rec}\text{-}\B` record
  received acknowledgements only if $`t=t'`;
* $`\mathsf{Rec}\text{-}\B` returns $`t'-1` rather than $`t-1`.

::::::gameGrid
:::::gameCell "\\textsf{Initialisation}" (kind := "compact")
$`\Init\text{-}\KeyGen(): \quad
I_{\mathsf{CKA}}\gets\bot;\quad \mathsf{return}\;I_{\mathsf{CKA}}`
```anchor initKeyGen (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def initKeyGen : m Unit := pure ()
```

$`\begin{array}{l}
\InitA(\bot): \\
\quad(\dkA,\ekA,\ctzero,t,\ich,\Lch,\ack)
  \gets(\bot,\bot,\bot,1,0,\emptyset,(\mathsf{false},\mathsf{false})); \\
\quad\stA\gets(\dkA,\ekA,\ctzero,t,\ich,\Lch,\ack); \\
\quad\mathsf{return}\;\stA
\end{array}`
```anchor initA (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def initA (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (_ik : Unit) : m (StA onoff Sym) :=
  pure { dkA := none, ekA := none, ct0 := none, t := 1, ich := 0, lch := ∅,
         ack := { ekRec := false, ctRec := false } }
```

$`\begin{array}{l}
\InitB(\bot): \\
\quad(\ekA,\ctzero,\ctone,\stct,t,\ich,\Lch,\ack)
  \gets(\bot,\bot,\bot,\bot,1,0,\emptyset,(\mathsf{false},\mathsf{false})); \\
\quad\stB\gets(\ekA,\ctzero,\ctone,\stct,t,\ich,\Lch,\ack); \\
\quad\mathsf{return}\;\stB
\end{array}`
```anchor initB (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def initB (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (_ik : Unit) : m (StB onoff Sym) :=
  pure { ekA := none, ct0 := none, ct1 := none, stCt := none, t := 1, ich := 0,
         lch := ∅, ack := { ekRec := false, ctRec := false } }
```
:::::

:::::gameCell "\\textsf{Vulnerable epochs}" (kind := "compact")
$`\stA.\mathsf{vuln}: \quad
\mathsf{return}\;\{t\}\;\mathsf{if}\;\dkA\ne\bot\;\mathsf{else}\;\emptyset`
```anchor vulnA (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def vulnA (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (stA : StA onoff Sym) : Finset ℕ :=
  if stA.dkA.isSome then {stA.t} else ∅
```

$`\stB.\mathsf{vuln}: \quad
\mathsf{return}\;\{t\}\;\mathsf{if}\;\stct\ne\bot\;\mathsf{else}\;\emptyset`
```anchor vulnB (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def vulnB (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (stB : StB onoff Sym) : Finset ℕ :=
  if stB.stCt.isSome then {stB.t} else ∅
```
:::::

:::::gameCell "\\textsf{Send-coin exposure}" (kind := "compact")
For a send from epoch $`t`, the exposure sets used by {bpref "scka_oracles"}[] are

$`\begin{array}{ll}
L_\A(\stA,\stA',r)=\{t\} & r=\mathsf{keygen}(r_K),\\
L_\B(\stB,\stB',r)=\{t\} & r=\mathsf{off}(r_0),\ \mathsf{on}(r_1),\ \mathsf{offOn}(r_0,r_1),\\
L_X(\mathsf{st},\mathsf{st}',\mathsf{none})=\emptyset & \text{deterministic retransmission}.
\end{array}`

```anchor sendExposureA (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def sendExposureA {kem : KEMScheme m K PK SK C} {onoff : kem.OnOffStructure}
    {KeygenRand OffRand OnRand : Type}
    (stA _stA' : StA onoff Sym) (rand : SendRand KeygenRand OffRand OnRand) : Finset ℕ :=
  match rand with
  | .keygen _ => {stA.t}
  | _ => ∅
```

```anchor sendExposureB (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def sendExposureB {kem : KEMScheme m K PK SK C} {onoff : kem.OnOffStructure}
    {KeygenRand OffRand OnRand : Type}
    (stB _stB' : StB onoff Sym) (rand : SendRand KeygenRand OffRand OnRand) : Finset ℕ :=
  match rand with
  | .off _ | .on _ | .offOn _ _ => {stB.t}
  | _ => ∅
```

State corruption uses the vulnerable-epoch rules in the preceding box.
Thus A's erased decapsulation key and B's erased offline state expose no
past epoch. The two complete policies are:

```anchor exposureA (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
abbrev exposureA (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (leak : kem.OnOffRandLeak onoff) :
    SCKAScheme.ExposurePolicy (StA onoff Sym)
      (SendRand leak.KeygenRand leak.OffRand leak.OnRand) where
  corrupt := vulnA kem onoff
  send := sendExposureA
```

```anchor exposureB (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
abbrev exposureB (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (leak : kem.OnOffRandLeak onoff) :
    SCKAScheme.ExposurePolicy (StB onoff Sym)
      (SendRand leak.KeygenRand leak.OffRand leak.OnRand) where
  corrupt := vulnB kem onoff
  send := sendExposureB
```
:::::

:::::gameCell "\\SendA(\\stA)" (kind := "compact-send")
$`\begin{array}{l}
(\dkA,\ekA,\ctzero,t,\ich,\Lch,\ack)\gets\stA, \chunk\gets\bot \\
\mathsf{if}\;\dkA=\bot\;\mathsf{then}\pcomment{\text{first message of epoch}} \\
\quad (\ekA,\dkA)\sample\KeyGen \\
\quad \ich\gets0 \\
\mathsf{if}\;\neg\ack.\ekrec\;\mathsf{then}
  \pcomment{\ekA\ \text{not acknowledged by }\B} \\
\quad \ich\gets\ich+1 \\
\quad \chunk\gets\mathsf{Encode}(\ekA,\ich) \\
\rho\gets(\chunk,\ack,t,\bot) \\
\stA\gets(\dkA,\ekA,\ctzero,t,\ich,\Lch,\ack) \\
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
          some (ecEk.encode ekA ich)
  let msg := (ch?, stA.ack, stA.t, none)
  let stA' := { stA with dkA := dkA, ekA := ekA, ich := ich }
  pure (some (none, msg, stA.t - 1, stA'))
```

:::leanPillCaption "rleak version leaking key generation coins"
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
            some (ecEk.encode ekA ich)
    let msg := (ch?, stA.ack, stA.t, none)
    let stA' := { stA with dkA := dkA, ekA := ekA, ich := ich }
    -- normal send output plus randomness-leakage
    pure (some (none, msg, stA.t - 1, stA', rand))
```
:::::

:::::gameCell "\\RecA(\\stA,\\rho)" (kind := "compact-recv")
$`\begin{array}{l}
(\dkA,\ekA,\ctzero,t,\ich,\Lch,\ack)\gets\stA \\
(\chunk,\ack',t',b)\gets\rho \\
I_{\B}\gets\bot, t_{I_{\B}}\gets\bot \\
\mathsf{if}\;t=t'\;\mathsf{then} \\
\quad \mathsf{if}\;\ctzero=\bot\wedge b=0\;\mathsf{then}
  \pcomment{\ctzero\ \text{not received yet}} \\
\qquad \Lch\gets\Lch\cup\{\chunk\} \\
\qquad \ctzero\gets\mathsf{Decode}(\Lch) \\
\qquad \mathsf{if}\;\ctzero\ne\bot\;\mathsf{then} \\
\qquad\quad \ack.\ctrec\gets\mathsf{true}, \Lch\gets\emptyset \\
\quad \mathsf{else}\;\mathsf{if}\;b=1\;\mathsf{then}
  \pcomment{\ctone\ \text{not received yet}} \\
\qquad \Lch\gets\Lch\cup\{\chunk\} \\
\qquad \ctone\gets\mathsf{Decode}(\Lch) \\
\qquad \mathsf{if}\;\ctone\ne\bot\;\mathsf{then}
  \pcomment{\ctone\ \text{recovered from chunk}} \\
\qquad\quad I_{\B}\gets\Decaps(\dkA,(\ctzero,\ctone)) \\
\qquad\quad t_{I_{\B}}\gets t, t\gets t+1, \Lch\gets\emptyset \\
\qquad\quad (\dkA,\ekA,\ctzero)\gets(\bot,\bot,\bot) \\
\qquad\quad (\ack.\ekrec,\ack.\ctrec)
  \gets(\mathsf{false},\mathsf{false}) \\
\mathsf{if}\;\ack'.\ekrec\;\boxed{\wedge\;t=t'}\;\mathsf{then}
  \pcomment{\text{incorporate }\B\text{'s acknowledgment}} \\
\quad \ack.\ekrec\gets\mathsf{true} \\
\stA\gets(\dkA,\ekA,\ctzero,t,\ich,\Lch,\ack) \\
\mathsf{return}\;((t_{I_{\B}},I_{\B}),t'-1,\stA)
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

:::::gameCell "\\SendB(\\stB)" (kind := "compact-send")
$`\begin{array}{l}
(\ekA,\ctzero,\ctone,\stct,t,\ich,\Lch,\ack)\gets\stB \\
I_{\B}\gets\bot, t_{I_{\B}}\gets\bot, \chunk\gets\bot \\
\mathsf{if}\;\ctzero=\bot\;\mathsf{then}\pcomment{\text{first message of epoch}} \\
\quad (\stct,\ctzero)\sample\Encaps.\mathsf{Off} \\
\quad \ich\gets0 \\
\mathsf{if}\;\neg\ack.\ctrec\;\mathsf{then}
  \pcomment{\ctzero\ \text{not acknowledged by }\A} \\
\quad \ich\gets\ich+1 \\
\quad \chunk\gets\mathsf{Encode}(\ctzero,\ich) \\
\quad b\gets0 \\
\mathsf{else}\;\mathsf{if}\;\ekA\ne\bot\;\mathsf{then}
  \pcomment{\ekA\ \text{received}} \\
\quad \mathsf{if}\;\ctone=\bot\;\mathsf{then} \\
\qquad (\ctone,I_{\B})\sample \Encaps.\mathsf{On}(\stct,\ekA) \\
\qquad t_{I_{\B}}\gets t, \ich\gets0 \\
\quad \ich\gets\ich+1 \\
\quad \chunk\gets\mathsf{Encode}(\ctone,\ich) \\
\quad b\gets1 \\
\rho\gets(\chunk,\ack,t,b) \\
\stB\gets(\ekA,\ctzero,\ctone,\stct,t,\ich,\Lch,\ack) \\
\mathsf{return}\;((t_{I_{\B}},I_{\B}),\rho,t-1,\stB)
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
  let ch? := some (ecCt0.encode ct0 ich)
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
        let ch? := some (ecCt1.encode ct1 ich)
        let msg := (ch?, stB.ack, stB.t, some 1)
        let stB' := { stB with ct1 := some ct1, ich := ich }
        pure (some (some (stB.t, key), msg, stB.t - 1, stB'))
    | some ct1 =>
      let ich := stB.ich + 1
      let ch? := some (ecCt1.encode ct1 ich)
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
      let ch? := some (ecCt0.encode ct0 ich)
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
            let ch? := some (ecCt1.encode ct1 ich)
            let msg := (ch?, stB.ack, stB.t, some 1)
            let stB' := { stB with ct1 := some ct1, ich := ich }
            pure (some (some (stB.t, key), msg, stB.t - 1, stB', rand))
        | some ct1 =>
          -- Re-sending existing `ct_1` is deterministic.
          let ich := stB.ich + 1
          let ch? := some (ecCt1.encode ct1 ich)
          let msg := (ch?, stB.ack, stB.t, some 1)
          let stB' := { stB with ich := ich }
          pure (some (none, msg, stB.t - 1, stB', offRand))
```
:::::

:::::gameCell "\\RecB(\\stB,\\rho)" (kind := "compact-recv")
$`\begin{array}{l}
(\ekA,\ctzero,\ctone,\stct,t,\ich,\Lch,\ack)\gets\stB \\
(\chunk,\ack',t',\_)\gets\rho \\
\mathsf{if}\;t<t'\;\mathsf{then}\pcomment{\text{first message of next epoch}} \\
\quad t\gets t+1 \\
\quad (\ctzero,\ctone,\stct)\gets(\bot,\bot,\bot) \\
\quad (\ekA,\Lch)\gets(\bot,\emptyset) \\
\quad (\ack.\ekrec,\ack.\ctrec)
  \gets(\mathsf{false},\mathsf{false}) \\
\mathsf{if}\;t=t'\wedge\ekA=\bot\;\mathsf{then} \\
\quad \Lch\gets\Lch\cup\{\chunk\} \\
\quad \ekA\gets\mathsf{Decode}(\Lch) \\
\quad \ack.\ekrec\gets(\ekA\ne\bot) \\
\mathsf{if}\;\ack'.\ctrec\;\boxed{\wedge\;t=t'}\;\mathsf{then}
  \pcomment{\text{incorporate }\A\text{'s acknowledgment}} \\
\quad \ack.\ctrec\gets\mathsf{true} \\
\stB\gets(\ekA,\ctzero,\ctone,\stct,t,\ich,\Lch,\ack) \\
\mathsf{return}\;((\bot,\bot),\boxed{t'-1},\stB)
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
  -- Return the delivered message's sending epoch `t' - 1`.
  some (none, t' - 1, stB)
```
:::::
::::::

:::leanPillCaption "SCKA scheme instance"
:::
```anchor scheme (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
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
```

*Why the leakage rule changes.* Consider correct single-chunk erasure codes
and an online leakage witness from which the encapsulated key $`k` can be
recovered. The K-PKE leakage package in {bpref "on_off_kem_rand_leak"}[]
returns its sampled message, which is precisely this key. The following
trace reaches the first epoch's challenge:

1. $`\OSendA;\ \ORecB(1)` transmits A's public key.
2. $`\OSendB;\ \ORecA(1)` transmits B's offline ciphertext.
3. $`\OSendA;\ \ORecB(2)` acknowledges that ciphertext.
4. $`\OSendBRLeak` performs online encapsulation and reveals $`k` through its coins.
5. $`\OChall(1)` requests the epoch key.

Under the original state-difference rule, B's vulnerable set is $`\{1\}`
both before and after step 4, so that leak records no new exposure.
Comparing the challenge response with $`k` gives distinguishing gap
$`1-1/|K|` and guessing advantage $`(1-1/|K|)/2`: real responses always equal
$`k`, while uniform responses equal it with probability $`1/|K|`.
Under the corrected rule, step 4 exposes epoch one and step 5 returns
$`\bot`. The theorem below concerns this corrected game. This is a weaker
SCKA security requirement; it imposes the same KEM IND-CPA assumption.

:::::::

:::defTitle "opp_unikem_cka_correctness" "Opp-UniKEM-CKA correctness"
:::

::::theorem "opp_unikem_cka_correctness" (parent := "cka_protocols_opp_unikem_cka") (lean := "oppUniKemCKA.correctness_true_ge") (tags := "gh-107") (uses := "opp_unikem_cka_spec, scka_correctness, erasure_code_correctness, on_off_kem_scheme, on_off_kem_rand_leak")
Assume that:

* $`\adv` is any SCKA correctness adversary making at most $`q` send-oracle
  queries;
* the underlying KEM has deterministic decapsulation,
  and has correctness error at most $`\varepsilon`;
* and the three erasure codes are correct.

Then $`\Pr\bigl[\Exp{\textsf{cor}}{\textsf{Opp-UniKEM-CKA}}(\adv)=1\bigr]
  \ge 1-q\varepsilon`, i.e., the Opp-UniKEM-CKA protocol is correct with probability at least
$`1-q\varepsilon`.


```anchor correctnessTrueGe (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Correctness)
theorem correctness_true_ge [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEkCorrect : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Correct : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Correct : ecCt1.ec.Correct)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SendQueryBound adv q) :
    Pr[= true |
      SCKAScheme.correctnessExp
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] ≥
      1 - (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp
```
::::

:::defTitle "opp_unikem_cka_security" "Opp-UniKEM-CKA security"
:::

::::::::theorem "opp_unikem_cka_security" (parent := "cka_protocols_opp_unikem_cka") (lean := "oppUniKemCKA.security") (tags := "gh-108") (uses := "opp_unikem_cka_spec, scka_security, scka_oracles, erasure_code_correctness, on_off_kem_scheme, on_off_kem_rand_leak")
*Parameters and assumptions.* Let $`\Pi` be the Opp-UniKEM protocol in
{bpref "opp_unikem_cka_spec"}[], with the corrected exposure policies above.
Fix:

* a KEM with finite nonempty key space $`K`, public-key space $`PK`,
  secret-key space $`SK`, ciphertext space $`C`, and lossless samplers;
* deterministic decapsulation and an {bpref "on_off_kem_scheme"}[] witness:
  $`C\simeq C_0\times C_1`, and for every $`pk`, encapsulation equals
  $`(st,c_0)\sample\mathsf{Enc.Off}();\ (c_1,k)\sample\mathsf{Enc.On}(st,pk)`
  followed by ciphertext reassembly;
* an {bpref "on_off_kem_rand_leak"}[] witness for key generation, offline
  encapsulation, and online encapsulation: discarding returned coins gives
  the ordinary algorithm's distribution at every input;
* three erasure codes for $`PK`, $`C_0`, and $`C_1` over symbol type $`Sym`,
  satisfying {bpref "erasure_code_correctness"}[]: every set of honest indexed
  chunks at or above its threshold decodes the payload, and every smaller
  honest set returns $`\bot`;
* an adaptive adversary $`\mathcal A` using the full SCKA interface and an
  integer $`q\ge0` bounding all ordinary and randomness-leaking sends on
  every oracle-response path. Receives, corruptions, challenges, and uniform
  random queries have no additional query bound. Previously sent messages
  may be delayed, reordered, or delivered repeatedly by their recorded index.

The Lean formulation uses `SampleableType K` for uniform key sampling and
`DecidableEq K`, `DecidableEq Sym` for the game's equality checks.
Let $`\varepsilon` be the KEM correctness error: the probability that
$`\mathsf{Decaps}(sk,ct)\ne k` for
$`(pk,sk)\sample\mathsf{KeyGen}()` and $`(ct,k)\sample\mathsf{Encaps}(pk)`.
A decapsulation failure $`\bot` counts as an error.
Let $`\mathcal B=\mathsf{securityReduction}(\mathcal A,q)` be the explicit
IND-CPA adversary defined below.

*Security bound.*

$$`\boxed{\operatorname{Adv}^{\mathsf{guess}}_{\mathsf{SCKA},\Pi}(\mathcal A)
\le \frac q2\operatorname{Adv}^{\mathsf{IND\text{-}CPA}}_{\mathsf{KEM}}(\mathcal B)
+q\varepsilon.}`

The theorem permits multiple adaptive challenges at distinct unexposed epochs.
The game rejects exposed, repeated, and unavailable-key challenges. It also
rejects corruption or coin leakage that would expose a previously challenged
epoch, retaining the pre-query state. State corruption before sampling and
after erasure follows the same exposure policy.

```anchor security (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Security.Theorem)
theorem security
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    SCKAScheme.sckaGuessAdvantage (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)
      adv (exposureA kem onoff leak) (exposureB kem onoff leak) ≤
    ((q : ℝ) / 2) * kem.IND_CPA_Advantage ProbCompRuntime.probComp
      (Security.Embedding.securityReduction kem onoff ecEk ecCt0 ecCt1 leak adv q) +
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal := by
  by_cases hzero : q = 0
  · subst q
    rw [security_zero_sends kem onoff hDet ecEk ecCt0 ecCt1 leak adv hq]
    simp
  · have h := Security.security_guess_le_hybrid_gap kem onoff hDet ecEk hEk
      ecCt0 hCt0 ecCt1 hCt1 leak adv q hq
    rw [Security.Embedding.hybrid_gap_eq_query_factor kem onoff hDet ecEk hEk
      ecCt0 hCt0 ecCt1 hCt1 leak adv q hzero] at h
    convert h using 1
    ring
```

The send budget counts all four send oracles together, including queries
whose leakage guard rejects their result:

```anchor securitySendQueryBound (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Security.Basic)
def SecuritySendQueryBound {kem : KEMScheme ProbComp K PK SK C}
    {onoff : kem.OnOffStructure} {leak : kem.OnOffRandLeak onoff}
    (adv : SecurityAdversary leak Sym) (q : ℕ) : Prop :=
  adv.IsQueryBoundP (fun t => isSecuritySendQuery t = true) q
```

*Advantage conventions.* For SCKA, $`G_b(\mathcal A)` returns the adversary's
raw Boolean output, with all eligible challenges real for $`b=0` and
independently uniform for $`b=1`. The sampled-bit game instead accepts when
the adversary guesses its bit:

$$`\begin{aligned}
\operatorname{Adv}^{\mathsf{dist}}_{\mathsf{SCKA},\Pi}(\mathcal A)
 &=|\Pr[G_1(\mathcal A)=1]-\Pr[G_0(\mathcal A)=1]|,\\
\operatorname{Adv}^{\mathsf{guess}}_{\mathsf{SCKA},\Pi}(\mathcal A)
 &=|\Pr[b'=b]-\tfrac12|
 =\tfrac12\operatorname{Adv}^{\mathsf{dist}}_{\mathsf{SCKA},\Pi}(\mathcal A).
\end{aligned}`

```anchor securityExpFixedBit (project := ".") (module := SecureMessaging.SCKA.Defs)
def securityExpFixedBit [SampleableType I] [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (adversary : SCKAAdversary StA StB I Rho Rand)
    (b : Bool) (exposureA : ExposurePolicy StA Rand)
      (exposureB : ExposurePolicy StB Rand) : ProbComp Bool := do
  let ik ← scka.initKeyGen
  let stA ← scka.initA ik
  let stB ← scka.initB ik
  let (b', _) ← (simulateQ (sckaSecurityImpl b exposureA exposureB scka) adversary).run
    (initGameState stA stB)
  return b'
```

```anchor sckaDistAdvantage (project := ".") (module := SecureMessaging.SCKA.Defs)
noncomputable def sckaDistAdvantage [SampleableType I] [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (adversary : SCKAAdversary StA StB I Rho Rand)
    (exposureA : ExposurePolicy StA Rand) (exposureB : ExposurePolicy StB Rand) : ℝ :=
  |(Pr[= true | securityExpFixedBit scka adversary true exposureA exposureB]).toReal -
   (Pr[= true | securityExpFixedBit scka adversary false exposureA exposureB]).toReal|
```

```anchor sckaAdvantageNormalization (project := ".") (module := SecureMessaging.SCKA.Defs)
lemma sckaGuessAdvantage_eq_sckaDistAdvantage_div_two [SampleableType I] [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (adversary : SCKAAdversary StA StB I Rho Rand)
    (exposureA : ExposurePolicy StA Rand) (exposureB : ExposurePolicy StB Rand) :
    sckaGuessAdvantage scka adversary exposureA exposureB =
      sckaDistAdvantage scka adversary exposureA exposureB / 2 := by
  simp only [sckaGuessAdvantage, sckaDistAdvantage]
  rw [securityExp_toReal_sub_half, abs_div]
  congr 1
  exact abs_of_pos two_pos
```

For KEM IND-CPA, sample $`(pk^*,sk^*)\sample\mathsf{KeyGen}()`,
$`(ct^*,k)\sample\mathsf{Encaps}(pk^*)`, and independent $`u\sample K`.
The two-stage adversary receives $`pk^*` before the challenge and receives
$`(ct^*,k)` in the real branch or $`(ct^*,u)` in the random branch.
The existing KEM definition uses

$$`\operatorname{Adv}^{\mathsf{IND\text{-}CPA}}_{\mathsf{KEM}}(\mathcal B)
=|\Pr[\mathcal B_{\mathsf{real}}=1]-\Pr[\mathcal B_{\mathsf{random}}=1]|.`

Its fixed-bit convention is `true` for real and `false` for random.
Thus the KEM quantity is a full distinguishing gap; the SCKA guessing
quantity is half a distinguishing gap.

*The reduction.* Let $`e` be the selected epoch. The simulator keeps honest
protocol records and replaces only eligible challenge responses. A private
field has three states: absent after erasure, present but unavailable to the
reduction, or present with a known value. In the boxes, $`\mathsf{hidden}`
denotes the present-but-unavailable case. The challenge key $`k^*` is kept
separate from the honest key tables.

::::::gameGrid
:::::gameCell "\\mathcal B.\\mathsf{preChallenge}(pk^*)" (kind := "game")
$`\begin{array}{l}
\pif\;q=0\;\pthen\; e\gets1\\
\pelse\;e\sample\{1,\ldots,q\}\\
\Return(pk^*,e)
\end{array}`

```anchor embedding_epochChoice (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulator)
def epochChoice (q : ℕ) : ProbComp ℕ :=
  if hq : q = 0 then pure 1
  else
    letI : NeZero q := ⟨hq⟩
    (fun i : Fin q => i.val + 1) <$> ($ᵗ (Fin q) : ProbComp (Fin q))
```

:::::
:::::gameCell "\\mathcal B.\\mathsf{postChallenge}((pk^*,e),ct^*,k^*)" (kind := "game")
$`\begin{array}{l}
(c_0^*,c_1^*)\gets\mathsf{split}(ct^*)\\
\widetilde{s}\gets\mathsf{InitialState}\\
b'\gets\mathcal A^{\mathsf{Sim}_{e,pk^*,ct^*,k^*}}\\
\pif\;\mathsf{Sim}\text{ terminates}\;\pthen\;\Return0\\
\Return b'
\end{array}`

```anchor securityReduction (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulator)
def securityReduction [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (q : ℕ) : base.IND_CPA_Adversary where
  State := PK × ℕ
  preChallenge pk := do pure (pk, ← epochChoice q)
  postChallenge state ct key := run base onoff ecEk ecCt0 ecCt1 leak adv state.2 state.1 ct key
```

```anchor embedding_run (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulator)
def run [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (e : ℕ) (pkStar : PK) (ctStar : C) (kStar : K) :
    ProbComp Bool := do
  let result ← ((simulateQ (oracle base onoff ecEk ecCt0 ecCt1 leak e pkStar ctStar kStar)
    adv).run).run' (initial onoff)
  pure (result.getD false)
```

:::::
:::::gameCell "\\mathsf{Sim}:\\text{ sampling and delivery}" (kind := "oracle")
$`\begin{array}{l}
\text{First A-send at epoch }e:\\
\quad(pk,sk)\gets(pk^*,\mathsf{hidden})\\
\text{First B-send at epoch }e:\\
\quad(st,c_0)\gets(\mathsf{hidden},c_0^*)\\
\text{Online encapsulation with hidden }st:\\
\quad(c_1,k)\gets(c_1^*,\mathsf{hidden})\\
\text{Other sampling phases: run the KEM honestly}\\
\text{Send: encode and record the protocol message}\\
\text{Receive}(n):\text{ deliver the recorded message }n\\
\text{A's ciphertext completion: record B's symbolic key}\\
\text{Uniform query: return a fresh uniform sample}
\end{array}`

The key-generation, offline, and online substitutions are exactly:

```anchor embedding_primitives (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Primitives)
def keygen (kem : KEMScheme ProbComp K PK SK C) (selected : Bool) (pkStar : PK) :
    ProbComp (PK × Option SK) :=
  if selected then pure (pkStar, none) else Prod.map id some <$> kem.keygen

/-- Offline encapsulation for a simulator query. In the selected epoch,
return the offline component of `ctStar` with unavailable offline state;
otherwise sample the original offline algorithm. -/
def encapsOff {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (selected : Bool) (ctStar : C) : ProbComp (Option onoff.St × onoff.C₀) :=
  if selected then pure (none, (onoff.split ctStar).1)
  else Prod.map some id <$> onoff.encapsOff

/-- Online encapsulation uses the original algorithm for known offline
state. Unavailable state denotes the selected epoch: return `ctStar`'s
online component and mark its honest encapsulated key as unavailable. -/
def encapsOn {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (ctStar : C) (st : Option onoff.St) (pk : PK) : ProbComp (onoff.C₁ × Option K) :=
  match st with
  | none => pure ((onoff.split ctStar).2, none)
  | some st => Prod.map id some <$> onoff.encapsOn st pk
```

:::::
:::::gameCell "\\mathsf{Sim}:\\mathsf{Chall}(t)" (kind := "challenge")
$`\begin{array}{l}
\req\;t\notin\mathsf{Exposed}\cup\mathsf{Challenged}\\
\req\;\text{a key is recorded for epoch }t\\
\pif\;0<t<e\;\pthen\;z\sample K\\
\pelse\;\pif\;t=e\;\pthen\;z\gets k^*\\
\pelse\;z\gets\text{recorded honest key}\\
\mathsf{Challenged}\gets\mathsf{Challenged}\cup\{t\}\\
\Return z
\end{array}`

Each successful challenge updates only the challenged set. It preserves
both honest key tables, including the selected epoch's hidden key marker.

```anchor embedding_challenge (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulator)
def challenge [SampleableType K]
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (e : ℕ) (kStar : K) : QueryImpl (ℕ →ₒ Option K)
      (StateT (SimState onoff Sym) ProbComp) :=
  fun t => do
    let s ← get
    if t ∈ s.exposed ∨ t ∈ s.challenged then pure none
    else
      let key := match s.keyA t with
        | some k => some k
        | none => s.keyB t
      match key with
      | none => pure none
      | some honest =>
        let k ← if 0 < t ∧ t < e then liftM ($ᵗ K : ProbComp K)
          else pure (if t = e then kStar else honest.getD kStar)
        set { s with challenged := insert t s.challenged }
        pure (some k)
```

:::::
:::::gameCell "\\mathsf{Sim}:\\text{ corruption and coin leakage}" (kind := "oracle")
$`\begin{array}{l}
\text{Compute the proposed response and its exposure set }E\\
\pif\;E\cap\mathsf{Challenged}\ne\emptyset\;\pthen\\
\quad\text{retain the input state};\ \Return\bot\\
\text{Apply the oracle's state and exposure updates}\\
\pif\;\text{the response needs hidden material}\;\pthen\\
\quad\text{terminate the simulation with output }0\\
\Return\text{the permitted state or coins}
\end{array}`

An absent field can be revealed after erasure. Present hidden fields and
hidden sampling coins terminate the simulation. A deterministic retransmission
returns the no-coins constructor and continues. The full oracle applies the
game's guard before converting its response:

```anchor embedding_revealField (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulator)
def revealField {α : Type} : Option (Option α) → Option (Option α)
  | none => some none
  | some none => none
  | some (some a) => some (some a)
```

```anchor embedding_revealCoins (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulator)
def revealCoins {KG OFF ON : Type} :
    SendRand (Option KG) (Option OFF) (Option ON) → Option (SendRand KG OFF ON)
  | .none => some .none
  | .keygen r => .keygen <$> r
  | .off r => .off <$> r
  | .on r => .on <$> r
  | .offOn r₀ r₁ => do pure (.offOn (← r₀) (← r₁))
```

```anchor embedding_oracle (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulator)
def oracle [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (e : ℕ) (pkStar : PK) (ctStar : C) (kStar : K) :
    QueryImpl (securitySpec leak Sym) (OptionT (StateT (SimState onoff Sym) ProbComp)) :=
  fun t => (get : OptionT (StateT (SimState onoff Sym) ProbComp) (SimState onoff Sym)) >>= fun s =>
    let selectedA := decide (s.stA.t = e)
    let selectedB := decide (s.stB.t = e)
    let key := s.keyB s.stA.t
    let simKem := kem base onoff selectedA selectedB pkStar ctStar key
    let simOnOff := onOff base onoff selectedA selectedB pkStar ctStar key
    let simLeak := leakage base onoff leak selectedA selectedB pkStar ctStar key
    let scka := scheme simKem simOnOff
      (deterministic base onoff selectedA selectedB pkStar ctStar key) ecEk ecCt0 ecCt1 simLeak
    match (motive := ∀ query,
        OptionT (StateT (SimState onoff Sym) ProbComp) ((securitySpec leak Sym).Range query)) t with
    | .inl (.inl (.inl (.inl (.inl t)))) =>
      liftM (SCKAScheme.sckaCorrectnessImpl scka t)
    | .inl (.inl (.inl (.inl (.inr u)))) =>
      revealAfter (revealResponse (fun (out : ℕ × Option ℕ × Message Sym ×
          SendRand (Option leak.KeygenRand) (Option leak.OffRand) (Option leak.OnRand)) => do
        let (n, epoch, msg, coins) := out
        pure (n, epoch, msg, ← revealCoins coins)))
        (SCKAScheme.oracleSendArleak sendExposureA scka u)
    | .inl (.inl (.inl (.inr u))) =>
      revealAfter (revealResponse (fun (out : ℕ × Option ℕ × Message Sym ×
          SendRand (Option leak.KeygenRand) (Option leak.OffRand) (Option leak.OnRand)) => do
        let (n, epoch, msg, coins) := out
        pure (n, epoch, msg, ← revealCoins coins)))
        (SCKAScheme.oracleSendBrleak sendExposureB scka u)
    | .inl (.inl (.inr t)) => liftM (challenge (Sym := Sym) onoff e kStar t)
    | .inl (.inr u) =>
      revealAfter (revealResponse (revealA (onoff := onoff) (Sym := Sym)))
        (SCKAScheme.oracleCorruptA (vulnA (Sym := Sym) simKem simOnOff)
          (StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym) (Option K) (Message Sym) u)
    | .inr u =>
      revealAfter (revealResponse (revealB (onoff := onoff) (Sym := Sym)))
        (SCKAScheme.oracleCorruptB (vulnB (Sym := Sym) simKem simOnOff)
          (StateA (Option SK) PK onoff.C₀ Sym) (Option K) (Message Sym) u)
```

:::::
::::::

*Why this reduction proves the bound.* Let $`H_i` be the auxiliary game
that uses encapsulated keys at A's ciphertext completion and randomizes
eligible challenges for epochs $`1,\ldots,i`. It retains the honest keys in
its transcript. The inherited transcript invariant covers every recorded
message and every permitted delivery order. Epoch accounting ensures that
every available challenge epoch lies in $`\{1,\ldots,q\}`.
For $`q>0`, write $`\mathcal B^{(e)}` for the reduction with its selected
epoch fixed to $`e\in\{1,\ldots,q\}`. The comparisons are:

$$`\begin{array}{ccccc}
G_0 & \xleftrightarrow{\ \le q\varepsilon\ } &
H_0\xleftrightarrow{\ \mathcal B^{(1)}\ }H_1\ \cdots
H_{q-1}\xleftrightarrow{\ \mathcal B^{(q)}\ }H_q &
\xleftrightarrow{\ \le q\varepsilon\ } & G_1\\
\text{real SCKA} && \text{auxiliary epoch hybrids} && \text{random SCKA}
\end{array}`

At each endpoint, the tracked probability of KEM inconsistency is at most
$`q\varepsilon`; before inconsistency, the real and auxiliary oracle
responses and successor states agree. For adjacent hybrids at $`e`, the
reduction above matches their executions stopped on exposure of $`e`.
Deferring online, offline, and key-generation samples establishes this
correspondence for adaptive executions. Once $`e` is exposed, its challenge
is rejected in both hybrids, and the identical continuations cancel in the
signed difference. A previously challenged epoch is protected by the
exposure guards, so those paths continue normally.

```anchor fixedBranch_signed_gap_eq (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Adjacent)
theorem fixedBranch_signed_gap_eq
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff) (adv : SecurityAdversary leak Sym) (i : ℕ) :
    (Pr[= true | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv (i + 1) true]).toReal -
      (Pr[= true | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv (i + 1) false]).toReal =
    (Pr[= true | idealEpochHybridExp base onoff hDet ecEk ecCt0 ecCt1 leak adv i]).toReal -
      (Pr[= true | idealEpochHybridExp
        base onoff hDet ecEk ecCt0 ecCt1 leak adv (i + 1)]).toReal := by
  rw [fixedBranch_eq_auxiliary base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak (i + 1) (Nat.succ_pos i) true adv,
    fixedBranch_eq_auxiliary base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak (i + 1) (Nat.succ_pos i) false adv]
  simp only [Bool.not_true, Bool.not_false, adjacentMode_succ_false, adjacentMode_succ_true]
  have hstop := idealEpochHybrid_signed_gap_stop_eq base onoff hDet ecEk ecCt0 ecCt1
    leak i adv (oppUniKemCKA.Reduction.Internal.initialGame base onoff)
    (by simp [oppUniKemCKA.Reduction.Internal.initialGame, SCKAScheme.initGameState])
  change
    (Pr[= true | idealEpochHybridExp base onoff hDet ecEk ecCt0 ecCt1 leak adv (i + 1)]).toReal -
      (Pr[= true | idealEpochHybridExp base onoff hDet ecEk ecCt0 ecCt1 leak adv i]).toReal = _
    at hstop
  change
    (Pr[= true | stoppedRun (idealEpochHybridImpl base onoff hDet ecEk ecCt0 ecCt1 leak i)
      (fun s => decide (i + 1 ∈ s.exposed)) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff)]).toReal -
    (Pr[= true | stoppedRun (idealEpochHybridImpl base onoff hDet ecEk ecCt0 ecCt1 leak (i + 1))
      (fun s => decide (i + 1 ∈ s.exposed)) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff)]).toReal = _
  linarith only [hstop]
```

Writing $`p_i=\Pr[H_i(\mathcal A)=1]`, uniform selection of $`e` gives, for
$`q>0`, the signed gap $`q^{-1}\sum_{e=1}^{q}(p_{e-1}-p_e)=q^{-1}(p_0-p_q)`.
Taking absolute values gives the factor $`q`. The endpoint costs sum to
$`2q\varepsilon` in distinguishing advantage, and division by two yields
the theorem's $`q/2` and $`q\varepsilon` terms.

```anchor hybrid_gap_eq_query_factor (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Adjacent)
theorem hybrid_gap_eq_query_factor
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff) (adv : SecurityAdversary leak Sym)
    (q : ℕ) (hq : q ≠ 0) :
    |(Pr[= true | idealEpochHybridExp base onoff hDet ecEk ecCt0 ecCt1 leak adv 0]).toReal -
      (Pr[= true | idealEpochHybridExp base onoff hDet ecEk ecCt0 ecCt1 leak adv q]).toReal| =
    (q : ℝ) * base.IND_CPA_Advantage ProbCompRuntime.probComp
      (securityReduction base onoff ecEk ecCt0 ecCt1 leak adv q) := by
  rw [KEMScheme.IND_CPA_Advantage_eq_fixed_branch_dist,
    securityReduction_signed_gap_eq base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak adv q hq, abs_mul, abs_inv,
    abs_of_nonneg (show (0 : ℝ) ≤ (q : ℝ) from Nat.cast_nonneg q),
    ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hq), one_mul]
```

*Boundary cases.* If the KEM is perfectly correct, $`\varepsilon=0` and
only the $`q/2` IND-CPA term remains. If $`q=0`, every challenge is unavailable
and the two fixed-bit SCKA experiments agree; the guessing advantage is zero.
The reduction's choice $`e=1` in this case makes its constructor total.

```anchor security_perfectKEM (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Security.Theorem)
theorem security_perfectKEM
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    SCKAScheme.sckaGuessAdvantage (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)
      adv (exposureA kem onoff leak) (exposureB kem onoff leak) ≤
    ((q : ℝ) / 2) * kem.IND_CPA_Advantage ProbCompRuntime.probComp
      (Security.Embedding.securityReduction kem onoff ecEk ecCt0 ecCt1 leak adv q) := by
  have herror := (KEMScheme.correctnessError_eq_zero_iff_perfectlyCorrect
    kem ProbCompRuntime.probComp).2 hkem
  simpa only [herror, ENNReal.toReal_zero, mul_zero, add_zero] using
    security kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak adv q hq
```

```anchor security_zero_sends (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Security.ZeroSend)
theorem security_zero_sends
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (hq : SecuritySendQueryBound adv 0) :
    SCKAScheme.sckaGuessAdvantage (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)
      adv (exposureA kem onoff leak) (exposureB kem onoff leak) = 0 := by
  have hrun := security_run_eq_of_zero_sends kem onoff hDet ecEk ecCt0 ecCt1 leak adv hq
  have hexp :
      SCKAScheme.securityExpFixedBit (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)
        adv true (exposureA kem onoff leak) (exposureB kem onoff leak) =
      SCKAScheme.securityExpFixedBit (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)
        adv false (exposureA kem onoff leak) (exposureB kem onoff leak) := by
    simpa [SCKAScheme.securityExpFixedBit, scheme, initKeyGen, initA, initB,
      initialGame, initialA, initialB] using congrArg (fun x => Prod.fst <$> x) hrun
  rw [SCKAScheme.sckaGuessAdvantage_eq_sckaDistAdvantage_div_two]
  simp [SCKAScheme.sckaDistAdvantage, hexp]
```

::::::::
