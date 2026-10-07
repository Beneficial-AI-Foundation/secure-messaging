import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Bibliography
import SecureMessaging.SCKA.OppUniKEM.Correctness

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

:::::::definition "opp_unikem_cka_spec" (parent := "cka_protocols_opp_unikem_cka") (lean := "oppUniKemCKA.initKeyGen, oppUniKemCKA.initA, oppUniKemCKA.initB, oppUniKemCKA.SendRand, oppUniKemCKA.sendA, oppUniKemCKA.sendArleak, oppUniKemCKA.recvA, oppUniKemCKA.sendB, oppUniKemCKA.sendBrleak, oppUniKemCKA.recvB, oppUniKemCKA.scheme") (tags := "gh-106") (uses := "scka_scheme, scka_oracles, erasure_code_scheme, on_off_kem_scheme, on_off_kem_rand_leak")
Figure 16 of {Informal.citet SCKA25}[]. In the receive algorithms,
- $`t` is the epoch index of the receiver's state,
- $`t'` is the epoch index of the delivered message.

We make two corrections to these algorithms, marked with surrounding boxes:

* $`\mathsf{Rec}\text{-}\A` and $`\mathsf{Rec}\text{-}\B` record
  received acknowledgements only if $`t=t'`;
* $`\mathsf{Rec}\text{-}\B` returns $`t'-1` rather than $`t-1`.

::::::gameGrid
:::::gameCell "\\textsf{Initialisation}" (kind := "scheme")
$`\Init\text{-}\KeyGen(): \quad
I_{\mathsf{CKA}}\gets\bot;\quad \mathsf{return}\;I_{\mathsf{CKA}}`
:::leanPillCaption "Trivial initial shared key"
:::

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
:::leanPillCaption "A's initial state"
:::

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
:::leanPillCaption "B's initial state"
:::

```anchor initB (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def initB (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (_ik : Unit) : m (StB onoff Sym) :=
  pure { ekA := none, ct0 := none, ct1 := none, stCt := none, t := 1, ich := 0,
         lch := ∅, ack := { ekRec := false, ctRec := false } }
```
:::::

:::::gameCell "\\SendA(\\stA)" (kind := "compact")
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

:::leanPillCaption "A's send transition"
:::

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

:::::

:::::gameCell "\\SendB(\\stB)" (kind := "compact")
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

:::leanPillCaption "B's send transition"
:::

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

:::::

:::::gameCell "\\SendARLeak(\\stA)" (kind := "compact")
$`\begin{array}{l}
(\dkA,\ekA,\ctzero,t,\ich,\Lch,\ack)\gets\stA \\
\chunk\gets\bot,\quad r_K\gets\bot \\
\pif\;\dkA=\bot\;\pthen \\
\quad ((\ekA,\dkA),r_K)\sample\KeyGen^{\mathsf{rleak}}() \\
\quad \ich\gets0 \\
\pif\;\neg\ack.\ekrec\;\pthen \\
\quad \ich\gets\ich+1 \\
\quad \pif\;\ekA\ne\bot\;\pthen\;
  \chunk\gets\mathsf{Encode}(\ekA,\ich) \\
\rho\gets(\chunk,\ack,t,\bot) \\
\stA\gets(\dkA,\ekA,\ctzero,t,\ich,\Lch,\ack) \\
\Return((\bot,\bot),\rho,t-1,\stA,r_K)
\end{array}`

:::leanPillCaption "A's send with key-generation coins"
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

:::::gameCell "\\SendBRLeak(\\stB)" (kind := "compact")
$`\begin{array}{l}
(\ekA,\ctzero,\ctone,\stct,t,\ich,\Lch,\ack)\gets\stB \\
I_\B,t_{I_\B},\chunk,b\gets\bot,\quad r_0,r_1\gets\bot \\
i\gets\ich \\
\pif\;\ctzero=\bot\;\pthen \\
\quad ((\stct,\ctzero),r_0)\sample\Encaps.\mathsf{Off}^{\mathsf{rleak}}() \\
\quad i\gets0 \\
\pif\;\neg\ack.\ctrec\;\pthen \\
\quad \ich\gets i+1,\quad b\gets0 \\
\quad \chunk\gets\mathsf{Encode}(\ctzero,\ich) \\
\pelse\;\pif\;\ekA\ne\bot\;\pthen \\
\quad b\gets1 \\
\quad \pif\;\ctone=\bot\;\pthen \\
\qquad \pif\;\stct\ne\bot\;\pthen \\
\qquad\quad ((\ctone,I_\B),r_1)\sample
  \Encaps.\mathsf{On}^{\mathsf{rleak}}(\stct,\ekA) \\
\qquad\quad t_{I_\B}\gets t,\quad \ich\gets1 \\
\qquad\quad \chunk\gets\mathsf{Encode}(\ctone,\ich) \\
\quad \pelse \\
\qquad \ich\gets\ich+1 \\
\qquad \chunk\gets\mathsf{Encode}(\ctone,\ich) \\
\rho\gets(\chunk,\ack,t,b) \\
\stB\gets(\ekA,\ctzero,\ctone,\stct,t,\ich,\Lch,\ack) \\
\Return((t_{I_\B},I_\B),\rho,t-1,\stB,(r_0,r_1))
\end{array}`

:::leanPillCaption "B's send with offline and online encapsulation coins"
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

:::::gameCell "\\RecA(\\stA,\\rho)" (kind := "compact")
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

:::leanPillCaption "A's receive transition and key output"
:::

```anchor recvA (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def recvA (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    [DecidableEq Sym]
  (decapsDet : SK → C → Option K)
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
                  match decapsDet dkA (onoff.split.symm (ct0, ct1)) with
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

:::::gameCell "\\RecB(\\stB,\\rho)" (kind := "compact")
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

:::leanPillCaption "B's receive transition and epoch update"
:::

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

:::leanPillCaption "Randomness returned by the leaking sends"
:::

```anchor SendRand (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
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
```

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
  recvA := recvA kem onoff hDet.decapsDet ecCt0 ecCt1
  sendB := sendB kem onoff ecCt0 ecCt1
  sendBrleak := sendBrleak kem onoff ecCt0 ecCt1 leak
  recvB := recvB kem onoff ecEk
```

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


:::leanPillCaption "Correctness bound for at most $`q` send queries"
:::

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

:::defTitle "opp_unikem_cka_vulnerable_epochs" "Opp-UniKEM-CKA vulnerable epochs"
:::

:::::::definition "opp_unikem_cka_vulnerable_epochs" (parent := "cka_protocols_opp_unikem_cka") (lean := "oppUniKemCKA.vulnCorrA, oppUniKemCKA.vulnCorrB, oppUniKemCKA.vulnRleakA, oppUniKemCKA.vulnRleakB, oppUniKemCKA.exposureA, oppUniKemCKA.exposureB") (tags := "gh-108") (uses := "opp_unikem_cka_spec, scka_oracles, on_off_kem_rand_leak")
Recall the local state structures from {bpref "opp_unikem_cka_spec"}[]:

$$`\begin{aligned}
\stA &= (\dkA,\ekA,\ctzero,t_\A,\ich,\Lch,\ack), \\
\stB &= (\ekA,\ctzero,\ctone,\stct,t_\B,\ich,\Lch,\ack).
\end{aligned}`

The randomness outputs of $`\SendARLeak` and $`\SendBRLeak` are $`r_K` and $`(r_0,r_1)`,
respectively. The values $`r_K,r_0,r_1` are the coins of $`\KeyGen`, $`\Encaps.\mathsf{Off}`,
and $`\Encaps.\mathsf{On}`, respectively; each is $`\bot` if that algorithm was not called
during the send. Define

$$`\mathsf{vuln}^{\mathsf{corr}}_\A(\stA)=\begin{cases}
\{t_\A\} & \dkA\ne\bot,\\ \emptyset & \text{otherwise}.\end{cases}`

:::leanPillCaption "Epochs exposed by corruption of A"
:::

```anchor vulnCorrA (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def vulnCorrA (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (stA : StA onoff Sym) : Finset ℕ :=
  if stA.dkA.isSome then {stA.t} else ∅
```

$$`\mathsf{vuln}^{\mathsf{corr}}_\B(\stB)=\begin{cases}
\{t_\B\} & \stct\ne\bot,\\ \emptyset & \text{otherwise}.\end{cases}`

:::leanPillCaption "Epochs exposed by corruption of B"
:::

```anchor vulnCorrB (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def vulnCorrB (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (stB : StB onoff Sym) : Finset ℕ :=
  if stB.stCt.isSome then {stB.t} else ∅
```

$$`\mathsf{vuln}^{\mathsf{rleak}}_\A(\stA,r_K)=\begin{cases}
\{t_\A\} & r_K\ne\bot,\\ \emptyset & \text{otherwise}.\end{cases}`

:::leanPillCaption "Epochs exposed by A's send coins"
:::

```anchor vulnRleakA (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def vulnRleakA {kem : KEMScheme m K PK SK C} {onoff : kem.OnOffStructure}
    {KeygenRand OffRand OnRand : Type}
    (stA : StA onoff Sym) (rand : SendRand KeygenRand OffRand OnRand) : Finset ℕ :=
  match rand with
  | .keygen _ => {stA.t}
  | _ => ∅
```

$$`\mathsf{vuln}^{\mathsf{rleak}}_\B(\stB,(r_0,r_1))=\begin{cases}
\{t_\B\} & (r_0,r_1)\ne(\bot,\bot),\\ \emptyset & \text{otherwise}.\end{cases}`

:::leanPillCaption "Epochs exposed by B's send coins"
:::

```anchor vulnRleakB (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def vulnRleakB {kem : KEMScheme m K PK SK C} {onoff : kem.OnOffStructure}
    {KeygenRand OffRand OnRand : Type}
    (stB : StB onoff Sym) (rand : SendRand KeygenRand OffRand OnRand) : Finset ℕ :=
  match rand with
  | .off _ | .on _ | .offOn _ _ => {stB.t}
  | _ => ∅
```

The sets $`\mathsf{vuln}^{\mathsf{corr}}_\A(\stA)` and
$`\mathsf{vuln}^{\mathsf{corr}}_\B(\stB)` are denoted
$`\stA.\mathsf{vuln}` and $`\stB.\mathsf{vuln}`, respectively, in Figure 16 of
{Informal.citet SCKA25}[].

:::leanPillCaption "A's corruption and randomness-leakage functions"
:::

```anchor exposureA (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
abbrev exposureA (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (leak : kem.OnOffRandLeak onoff) :
    SCKAScheme.VulnerableEpochs (StA onoff Sym)
      (SendRand leak.KeygenRand leak.OffRand leak.OnRand) where
  corrupt := vulnCorrA kem onoff
  rleak := vulnRleakA
```

:::leanPillCaption "B's corruption and randomness-leakage functions"
:::

```anchor exposureB (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
abbrev exposureB (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (leak : kem.OnOffRandLeak onoff) :
    SCKAScheme.VulnerableEpochs (StB onoff Sym)
      (SendRand leak.KeygenRand leak.OffRand leak.OnRand) where
  corrupt := vulnCorrB kem onoff
  rleak := vulnRleakB
```
:::::::

*Towards the security theorem: the cost of imperfect KEM correctness.*
The security game is {bpref "scka_oracles"}[] with the vulnerable epochs of
{bpref "opp_unikem_cka_vulnerable_epochs"}[]. Its challenge oracle answers with the key
recorded by $`\A` when present, and that key is $`\A`'s decapsulation result.
A reduction to the KEM cannot decapsulate at the epoch where it embeds its
challenge, so the proof first passes to an *auxiliary* game in which $`\A`
records $`\B`'s encapsulated key on completing $`\ctone`. Let $`H_i` be the
auxiliary game whose challenges at epochs $`1,\dots,i` return uniform keys,
and let $`p_i=\Pr[H_i(\adv)=1]`. For every adversary with at most $`q`
ordinary or leaking sends,

$$`\mathsf{Adv}^{\mathsf{guess}}_{\mathsf{SCKA},\Pi}(\adv)
\le \tfrac12\,|p_0-p_q| + q\varepsilon .`

The term $`q\varepsilon` is the price of the auxiliary game: a persistent
flag records the first KEM inconsistency, each send raises its probability
by at most $`\varepsilon`, and the real and auxiliary games coincide until
the flag is set. The identification of $`H_0` and $`H_q` with the two
fixed-bit auxiliary experiments uses that recorded epochs never exceed the
number of sends. Bounding $`|p_0-p_q|` by the KEM's IND-CPA advantage is the
subject of the security theorem below.

```anchor security_guess_le_hybrid_gap (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Security.Endpoints)
theorem security_guess_le_hybrid_gap
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    SCKAScheme.sckaGuessAdvantage (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)
      adv (exposureA kem onoff leak) (exposureB kem onoff leak) ≤
    |(Pr[= true | idealEpochHybridExp kem onoff hDet ecEk ecCt0 ecCt1 leak adv 0]).toReal -
      (Pr[= true | idealEpochHybridExp kem onoff hDet ecEk ecCt0 ecCt1 leak adv q]).toReal| / 2 +
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal := by
  rw [SCKAScheme.sckaGuessAdvantage_eq_sckaDistAdvantage_div_two,
    SCKAScheme.sckaDistAdvantage,
    idealEpochHybridExp_zero,
    idealEpochHybridExp_last kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak adv q hq]
  let G := fun b => (Pr[= true | SCKAScheme.securityExpFixedBit
    (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv b
    (exposureA kem onoff leak) (exposureB kem onoff leak)]).toReal
  let I := fun b => (Pr[= true | idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1
    leak (fun _ => b) adv]).toReal
  have h0 : |G false - I false| ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal :=
    security_correctness_endpoint_le kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak false adv q hq
  have h1 : |G true - I true| ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal :=
    security_correctness_endpoint_le kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak true adv q hq
  have htriangle := abs_sub_le (G true) (I true) (G false)
  have htriangle' := abs_sub_le (I true) (I false) (G false)
  rw [abs_sub_comm (I true) (I false), abs_sub_comm (I false) (G false)] at htriangle'
  change |G true - G false| / 2 ≤ |I false - I true| / 2 + _
  linarith
```

:::defTitle "opp_unikem_cka_security" "Opp-UniKEM-CKA security"
:::

::::theorem "opp_unikem_cka_security" (parent := "cka_protocols_opp_unikem_cka") (tags := "gh-108") (uses := "opp_unikem_cka_spec, opp_unikem_cka_vulnerable_epochs, scka_security, erasure_code_scheme, on_off_kem_scheme, on_off_kem_rand_leak")
$`\todo`

:::leanPill "missing"
:::
::::
