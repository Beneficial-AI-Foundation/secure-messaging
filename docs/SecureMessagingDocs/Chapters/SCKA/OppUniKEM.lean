import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Visuals.OppUniKEMVulnerableEpochs
import SecureMessagingDocs.Bibliography
import SecureMessaging.SCKA.OppUniKEM.Correctness
import SecureMessaging.SCKA.OppUniKEM.Security

/-! # Blueprint chapter: Opp-UniKEM-CKA -/

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

Boxes mark three corrections and explicit checks added to Figure 16:

* $`\mathsf{Rec}\text{-}\A` and $`\mathsf{Rec}\text{-}\B` record
  received acknowledgements only if $`t=t'`;
* $`\mathsf{Rec}\text{-}\B` returns $`t'-1` rather than $`t-1`;
* $`\mathsf{Rec}\text{-}\A` decodes only present chunks and aborts on missing
  decapsulation inputs or failed decapsulation.

See errata 4–6 in the {ref "scka-errata"}[errata] for details.

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

:::::gameCell "\\RecA(\\stA,\\rho)" (kind := "compact") (tag := "opp-unikem-rec-a")
$`\begin{array}{l}
(\dkA,\ekA,\ctzero,t,\ich,\Lch,\ack)\gets\stA \\
(\chunk,\ack',t',b)\gets\rho \\
I_{\B}\gets\bot, t_{I_{\B}}\gets\bot \\
\mathsf{if}\;t=t'\;\mathsf{then} \\
\quad \mathsf{if}\;\ctzero=\bot\wedge b=0\;\boxed{\wedge\;\chunk\ne\bot}\;\mathsf{then}
  \pcomment{\ctzero\ \text{not received yet}} \\
\qquad \Lch\gets\Lch\cup\{\chunk\} \\
\qquad \ctzero\gets\mathsf{Decode}(\Lch) \\
\qquad \mathsf{if}\;\ctzero\ne\bot\;\mathsf{then} \\
\qquad\quad \ack.\ctrec\gets\mathsf{true}, \Lch\gets\emptyset \\
\quad \mathsf{else}\;\mathsf{if}\;b=1\;\boxed{\wedge\;\chunk\ne\bot}\;\mathsf{then}
  \pcomment{\ctone\ \text{not received yet}} \\
\qquad \ctone\gets\mathsf{Decode}(\Lch\cup\{\chunk\}) \\
\qquad \mathsf{if}\;\ctone=\bot\;\mathsf{then}\;\Lch\gets\Lch\cup\{\chunk\} \\
\qquad \mathsf{else}
  \pcomment{\ctone\ \text{recovered from chunk}} \\
\qquad\quad \boxed{\mathsf{if}\;\dkA=\bot\vee\ctzero=\bot\;\mathsf{then}\;\mathsf{return}\;\bot} \\
\qquad\quad I_{\B}\gets\Decaps(\dkA,(\ctzero,\ctone)) \\
\qquad\quad \boxed{\mathsf{if}\;I_{\B}=\bot\;\mathsf{then}\;\mathsf{return}\;\bot} \\
\qquad\quad t_{I_{\B}}\gets t, t\gets t+1, \Lch\gets\emptyset \\
\qquad\quad (\dkA,\ekA,\ctzero)\gets(\bot,\bot,\bot) \\
\qquad\quad (\ack.\ekrec,\ack.\ctrec)
  \gets(\mathsf{false},\mathsf{false}) \\
\quad \mathsf{if}\;\ack'.\ekrec\;\boxed{\wedge\;t=t'}\;\mathsf{then}
  \pcomment{\text{incorporate }\B\text{'s acknowledgment}} \\
\qquad \ack.\ekrec\gets\mathsf{true} \\
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
    Option (Option (ℕ × K) × ℕ × StA onoff Sym) := do
  let (ch?, ack', t', b?) := ρ
  let (key?, stA') ←
    if stA.t = t' then do
      let (key?, stA') ←
        match stA.ct0, b?, ch? with
        | none, some 0, some ch =>
            -- `ct_0` not received yet
            let lch := insert ch stA.lch
            match ecCt0.decode lch with
            -- still not received enough chunks to decode `ct_0`
            | none => some ((none : Option (ℕ × K)), { stA with ct0 := none, lch := lch })
            -- decoded `ct_0` successfully
            | some ct0 =>
                some (none,
                  { stA with
                    ct0 := some ct0
                    lch := ∅
                    ack := { stA.ack with ctRec := true } })
        | _, some 1, some ch =>
            let lch := insert ch stA.lch
            match ecCt1.decode lch with
            | none => some (none, { stA with lch := lch })
            | some ct1 =>
              -- Decapsulation requires both `dk_A` and `ct_0`.
              match stA.dkA, stA.ct0 with
              | some dkA, some ct0 =>
                  match decapsDet dkA (onoff.split.symm (ct0, ct1)) with
                  | none => none
                  | some key =>
                      some (some (stA.t, key),
                        { stA with
                          dkA := none
                          ekA := none
                          ct0 := none
                          t := stA.t + 1
                          lch := ∅
                          ack := { ekRec := false, ctRec := false } })
              | _, _ => none
        | _, _, _ => some (none, stA)
      -- Incorporate B's acknowledgement only if this receive did not advance A
      -- to the next epoch; otherwise a final `ct_1` message would carry the old
      -- epoch's ack into the fresh epoch.
      let stA' :=
        if ack'.ekRec && stA'.t == t' then
          { stA' with ack := { stA'.ack with ekRec := true } }
        else
          stA'
      pure (key?, stA')
    else
      pure (none, stA)
  pure (key?, t' - 1, stA')
```
:::::

:::::gameCell "\\RecB(\\stB,\\rho)" (kind := "compact") (tag := "opp-unikem-rec-b")
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
    Pr{let x ← (SCKAScheme.correctnessExp
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv)}[x = true] ≥
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
during the send.

For $`X\in\{\A,\B\}`, let $`\mathsf{St}_X` be the state space of $`X` and $`R_X`
the space of randomness outputs of its leaking send. We define the functions
$`\mathsf{vuln}^{\mathsf{corr}}_X:\mathsf{St}_X\to\mathcal P_{\mathrm{fin}}(\mathbb N)` and
$`\mathsf{vuln}^{\mathsf{rleak}}_X:\mathsf{St}_X\times R_X\to\mathcal P_{\mathrm{fin}}(\mathbb N)`,
which parametrise the security game of {bpref "scka_oracles"}[], as follows.

::::::gameGrid
:::::gameCell "\\mathsf{vuln}^{\\mathsf{corr}}_\\A" (kind := "compact")
$$`\mathsf{vuln}^{\mathsf{corr}}_\A(\stA)=\begin{cases}
\{t_\A\} & \dkA\ne\bot,\\ \emptyset & \text{otherwise}.\end{cases}`

:::leanPillCaption "Epochs exposed by corruption of A"
:::

```anchor vulnCorrA (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def vulnCorrA (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (stA : StA onoff Sym) : Finset ℕ :=
  if stA.dkA.isSome then {stA.t} else ∅
```
:::::

:::::gameCell "\\textsf{Illustration: corruption of A}" (kind := "compact")
:::oppUniKemVulnCorrA
:::
:::::

:::::gameCell "\\mathsf{vuln}^{\\mathsf{corr}}_\\B" (kind := "compact")
$$`\mathsf{vuln}^{\mathsf{corr}}_\B(\stB)=\begin{cases}
\{t_\B\} & \stct\ne\bot,\\ \emptyset & \text{otherwise}.\end{cases}`

:::leanPillCaption "Epochs exposed by corruption of B"
:::

```anchor vulnCorrB (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def vulnCorrB (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (stB : StB onoff Sym) : Finset ℕ :=
  if stB.stCt.isSome then {stB.t} else ∅
```
:::::

:::::gameCell "\\textsf{Illustration: corruption of B}" (kind := "compact")
:::oppUniKemVulnCorrB
:::
:::::

:::::gameCell "\\mathsf{vuln}^{\\mathsf{rleak}}_\\A" (kind := "compact")
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
  | .none | .off _ | .on _ | .offOn _ _ => ∅
```
:::::

:::::gameCell "\\textsf{Illustration: randomness leakage by A}" (kind := "compact")
:::oppUniKemVulnRleakA
:::
:::::

:::::gameCell "\\mathsf{vuln}^{\\mathsf{rleak}}_\\B" (kind := "compact")
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
  | .none | .keygen _ => ∅
```
:::::

:::::gameCell "\\textsf{Illustration: randomness leakage by B}" (kind := "compact")
:::oppUniKemVulnRleakB
:::
:::::
::::::

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

:::defTitle "opp_unikem_cka_security" "Opp-UniKEM-CKA security"
:::

::::::::theorem "opp_unikem_cka_security" (parent := "cka_protocols_opp_unikem_cka") (lean := "oppUniKemCKA.security") (tags := "gh-108") (uses := "opp_unikem_cka_spec, opp_unikem_cka_vulnerable_epochs, scka_security, scka_oracles, erasure_code_correctness, on_off_kem_scheme, on_off_kem_rand_leak")
*Parameters and assumptions.* Let $`\Pi` be the Opp-UniKEM protocol in
{bpref "opp_unikem_cka_spec"}[], with the vulnerable epochs of {bpref "opp_unikem_cka_vulnerable_epochs"}[].
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
after erasure follows the same vulnerable epochs.

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
  have h := Security.security_guess_le_hybrid_gap kem onoff hDet ecEk hEk
    ecCt0 hCt0 ecCt1 hCt1 leak adv q hq
  have hideal := Security.ideal_security_guess_le kem onoff hDet ecEk hEk
    ecCt0 hCt0 ecCt1 hCt1 leak adv q
  linarith
```

The send budget counts all four send oracles together, including queries
whose leakage guard rejects their result:

```anchor securitySendQueryBound (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Security.Basic)
def SecuritySendQueryBound {kem : KEMScheme ProbComp K PK SK C}
    {onoff : kem.OnOffStructure} {leak : kem.OnOffRandLeak onoff}
    (adv : SecurityAdversary leak Sym) (q : ℕ) : Prop :=
  adv.IsQueryBoundP (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true) q
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
    (b : Bool) (vulnA : VulnerableEpochs StA Rand)
      (vulnB : VulnerableEpochs StB Rand) : ProbComp Bool := do
  let ik ← scka.initKeyGen
  let stA ← scka.initA ik
  let stB ← scka.initB ik
  let (b', _) ← (simulateQ (sckaSecurityImpl b vulnA vulnB scka) adversary).run
    (initGameState stA stB)
  return b'
```

```anchor sckaDistAdvantage (project := ".") (module := SecureMessaging.SCKA.Defs)
noncomputable def sckaDistAdvantage [SampleableType I] [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (adversary : SCKAAdversary StA StB I Rho Rand)
    (vulnA : VulnerableEpochs StA Rand) (vulnB : VulnerableEpochs StB Rand) : ℝ :=
  |(Pr[= true | securityExpFixedBit scka adversary true vulnA vulnB]).toReal -
   (Pr[= true | securityExpFixedBit scka adversary false vulnA vulnB]).toReal|
```

```anchor sckaAdvantageNormalization (project := ".") (module := SecureMessaging.SCKA.Defs)
lemma sckaGuessAdvantage_eq_sckaDistAdvantage_div_two [SampleableType I] [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (adversary : SCKAAdversary StA StB I Rho Rand)
    (vulnA : VulnerableEpochs StA Rand) (vulnB : VulnerableEpochs StB Rand) :
    sckaGuessAdvantage scka adversary vulnA vulnB =
      sckaDistAdvantage scka adversary vulnA vulnB / 2 := by
  simp only [sckaGuessAdvantage, sckaDistAdvantage]
  rw [securityExp_toReal_sub_half, abs_div]
  congr 1
  exact abs_of_pos two_pos
```

For KEM IND-CPA, sample $`(pk^*,sk^*)\sample\mathsf{KeyGen}()`,
$`(ct^*,k)\sample\mathsf{Encaps}(pk^*)`, and independent $`u\sample K`.
The two-stage adversary receives $`pk^*` before the challenge and receives
$`(ct^*,k)` in the real branch or $`(ct^*,u)` in the random branch.
VCVio defines the KEM advantage `KEMScheme.IND_CPA_Advantage` as the normalized guessing
advantage $`|2\Pr[b'=b]-1|` of the IND-CPA game with a uniform hidden bit $`b`. By
`KEMScheme.IND_CPA_Advantage_eq_fixed_branch_dist`, it equals the full distinguishing gap

$$`\operatorname{Adv}^{\mathsf{IND\text{-}CPA}}_{\mathsf{KEM}}(\mathcal B)
=|\Pr[\mathcal B_{\mathsf{real}}=1]-\Pr[\mathcal B_{\mathsf{random}}=1]|,`

with fixed-bit convention `true` for real and `false` for random. The SCKA guessing quantity is
half a distinguishing gap.

*The reduction.* Let $`e` be the selected epoch. The simulator keeps honest
protocol records and replaces only eligible challenge responses. A private
field has three states: absent after erasure, present but unavailable to the
reduction, or present with a known value. In the boxes, $`\mathsf{hidden}`
denotes the present-but-unavailable case. The challenge key $`k^*` is kept
separate from the honest key tables. $`\mathcal B` runs $`\mathcal A` once and answers each of
its queries with one operation of the simulated game; this cost statement is not formalized.

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
\text{A's ciphertext completion: record B's key of that epoch}\\
\text{Uniform query: return a fresh uniform sample}
\end{array}`

The key-generation, offline, and online substitutions are exactly:

```anchor embedding_primitives (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulator)
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
        (SCKAScheme.oracleSendArleak vulnRleakA scka u)
    | .inl (.inl (.inl (.inr u))) =>
      revealAfter (revealResponse (fun (out : ℕ × Option ℕ × Message Sym ×
          SendRand (Option leak.KeygenRand) (Option leak.OffRand) (Option leak.OnRand)) => do
        let (n, epoch, msg, coins) := out
        pure (n, epoch, msg, ← revealCoins coins)))
        (SCKAScheme.oracleSendBrleak vulnRleakB scka u)
    | .inl (.inl (.inr t)) => liftM (challenge (Sym := Sym) onoff e kStar t)
    | .inl (.inr u) =>
      revealAfter (revealResponse (revealA (onoff := onoff) (Sym := Sym)))
        (SCKAScheme.oracleCorruptA (vulnCorrA (Sym := Sym) simKem simOnOff)
          (StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym) (Option K) (Message Sym) u)
    | .inr u =>
      revealAfter (revealResponse (revealB (onoff := onoff) (Sym := Sym)))
        (SCKAScheme.oracleCorruptB (vulnCorrB (Sym := Sym) simKem simOnOff)
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

The endpoint step is `security_guess_le_hybrid_gap`: half the auxiliary
$`H_0`/$`H_q` gap plus $`q\varepsilon` bounds the guessing advantage.

```anchor security_guess_le_hybrid_gap (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Security.IdealHybrids)
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

The adjacent step identifies the reduction's fixed branch at $`e=i+1` with the signed
difference of the hybrids $`H_i` and $`H_{i+1}`:

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
    (leak : base.OnOffRandLeak onoff) (adv : SecurityAdversary leak Sym) (q : ℕ) :
    |(Pr[= true | idealEpochHybridExp base onoff hDet ecEk ecCt0 ecCt1 leak adv 0]).toReal -
      (Pr[= true | idealEpochHybridExp base onoff hDet ecEk ecCt0 ecCt1 leak adv q]).toReal| =
    (q : ℝ) * base.IND_CPA_Advantage ProbCompRuntime.probComp
      (securityReduction base onoff ecEk ecCt0 ecCt1 leak adv q) := by
  rcases Nat.eq_zero_or_pos q with rfl | hpos
  · simp
  have hq : q ≠ 0 := hpos.ne'
  rw [KEMScheme.IND_CPA_Advantage_eq_fixed_branch_dist,
    securityReduction_signed_gap_eq base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak adv q hq, abs_mul, abs_inv,
    abs_of_nonneg (show (0 : ℝ) ≤ (q : ℝ) from Nat.cast_nonneg q),
    ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hq), one_mul]
```

*Boundary cases.* If the KEM is perfectly correct, $`\varepsilon=0` and
only the $`q/2` IND-CPA term remains. If $`q=0`, both sides of the bound are
zero: without sends no key is ever recorded, every challenge is unavailable,
and the guessing advantage is exactly zero. The main theorem needs no separate
treatment of this case; the reduction's choice $`e=1` for $`q=0` only makes
its constructor total.

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

::::::::
