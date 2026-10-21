import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Bibliography
import SecureMessaging.SCKA.OppBiKEM.Correctness

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

#doc (Manual) "Opp-BiKEM-CKA" =>

:::group "cka_protocols_opp_bikem_cka"
Opp-BiKEM-CKA.
:::

:::defTitle "opp_bikem_cka_spec" "Opp-BiKEM-CKA protocol"
:::

:::::::definition "opp_bikem_cka_spec"(parent := "cka_protocols_opp_bikem_cka")(lean := "oppBiKemCKA.initKeyGen, oppBiKemCKA.initA, oppBiKemCKA.initB, oppBiKemCKA.vulnA, oppBiKemCKA.vulnB, oppBiKemCKA.sendA, oppBiKemCKA.sendArleak, oppBiKemCKA.recvA, oppBiKemCKA.sendB, oppBiKemCKA.sendBrleak, oppBiKemCKA.recvB, oppBiKemCKA.scheme")(tags := "gh-109")(uses := "scka_scheme, erasure_code_scheme")

Figures 17 and 18 of {Informal.citet SCKA25}[].

Instead of directly following the paper's presentation of `A`'s (Figure 17) and `B`'s (Figure 18)
protocols, we implement shared functions, parameterized by `Role`.
These functions specialize for `A` or `B` by using the `Role.offset` variable,
that distinguishes between roles at different indices that `A` and `B` play.


The pseudocode below marks with surrounding boxes the corrections we made with respect to the paper.
See the {ref "opp-bikem-errata"}[errata box] for detailed explanations and justifications for the corrections.

::::::gameGrid


:::::gameCell "\\textsf{Initialisation}" (kind := "compact")



$`\begin{array}{l}
\mathsf{CKA}\text{-}\mathsf{InitA}(I_{\mathsf{CKA}}=\bot): \\
\quad \mathsf{EK}_{B}[t]\gets\bot,\ \mathsf{DK}_{A}[t]\gets\bot\quad\text{for all }t \\
\quad (\mathsf{ACK}[t].\mathsf{ekRec},\mathsf{ACK}[t].\mathsf{ctRec}) \\
\qquad\gets(\mathsf{false},\mathsf{false})\quad\text{for all }t \\
\quad (\mathsf{ACK}[-1].\mathsf{ctRec},\mathsf{ACK}[0].\mathsf{ctRec}) \\
\qquad\gets(\mathsf{true},\mathsf{true}) \\
\quad \mathsf{st}_{\mathrm{res}}\gets(-1,\mathsf{EK}_{B},\bot,0) \\
\quad \mathsf{st}_{\mathrm{req}}\gets(0,\mathsf{DK}_{A},\bot,\emptyset) \\
\quad \mathsf{return}\;(\mathsf{st}_{\mathrm{res}},\mathsf{st}_{\mathrm{req}},\mathsf{ACK})
\end{array}`

$`\begin{array}{l}
\mathsf{CKA}\text{-}\mathsf{InitB}(I_{\mathsf{CKA}}=\bot): \\
\quad \mathsf{EK}_{A}[t]\gets\bot,\ \mathsf{DK}_{B}[t]\gets\bot\quad\text{for all }t \\
\quad (\mathsf{ACK}[t].\mathsf{ekRec},\mathsf{ACK}[t].\mathsf{ctRec}) \\
\qquad\gets(\mathsf{false},\mathsf{false})\quad\text{for all }t \\
\quad (\mathsf{ACK}[-1].\mathsf{ctRec},\mathsf{ACK}[0].\mathsf{ctRec}) \\
\qquad\gets(\mathsf{true},\mathsf{true}) \\
\quad \mathsf{st}_{\mathrm{res}}\gets(0,\mathsf{EK}_{A},\bot,0) \\
\quad \mathsf{st}_{\mathrm{req}}\gets(-1,\mathsf{DK}_{B},\bot,\emptyset) \\
\quad \mathsf{return}\;(\mathsf{st}_{\mathrm{res}},\mathsf{st}_{\mathrm{req}},\mathsf{ACK})
\end{array}`

```anchor init (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def init (role : Role) (_ik : Unit) : m (State PK SK C Sym) :=
  pure { req := { reqEpoch := if role = .A then 0 else -1
                  dk := [], ek := none, receivedChunks := ∅ }
         res := { resEpoch := if role = .A then -1 else 0
                  ekPeer := fun _ => none
                  ct := none, ich := 0 }
         ack := { ekRec := ∅, ctRec := {-1, 0} } }
```
:::::

:::::gameCell "\\textsf{Vulnerable epochs}" (kind := "compact")

$`\begin{array}{l}
\mathsf{st}_A.\mathsf{vuln}:\quad\mathsf{return}\;\{t:\mathsf{DK}_A[t]\ne\bot\}
\end{array}`
$`\begin{array}{l}
\mathsf{st}_B.\mathsf{vuln}:\quad\mathsf{return}\;\{t:\mathsf{DK}_B[t]\ne\bot\}
\end{array}`

```anchor vuln (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def vuln (st : State PK SK C Sym) : Finset ℕ :=
  let storedEpochs := (st.req.dk.map Prod.fst).toFinset
  let positiveEpochs := storedEpochs.filter fun t => 0 < t
  positiveEpochs.image Int.toNat

/-- Positive epochs whose secret decapsulation keys remain in A's state. -/
def vulnA (st : StA PK SK C Sym) : Finset ℕ := vuln st

/-- Positive epochs whose secret decapsulation keys remain in B's state. -/
def vulnB (st : StB PK SK C Sym) : Finset ℕ := vuln st
```

:::::

:::::gameCell "\\textsf{Specialized calls for A and B}" (kind := "compact-send")

:::leanPillCaption "A call to the shared function that discards randomness"
:::
```anchor send (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def send (role : Role) (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) :
    m (Option (Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym)) := do
  let out ← sendWith role
    (do let keys ← kem.keygen; pure (keys, ()))
    (fun pk => do let out ← kem.encaps pk; pure (out, ())) ecEk ecCt st
  pure (out.map fun (key?, ρ, t, st, _) => (key?, ρ, t, st))
```

:::leanPillCaption "Send-A without leaking randomness"
:::
```anchor sendA (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
/-- Run A's send step. -/
def sendA (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stA : StA PK SK C Sym) := send .A kem ecEk ecCt stA
```



:::leanPillCaption "Send-A with leaking randomness"
:::
```anchor sendArleak (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
/-- Run A's send step, also returning randomness used for key generation and encapsulation. -/
def sendArleak (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) (stA : StA PK SK C Sym) :=
  sendWith .A leak.keygenRleak leak.encapsRleak ecEk ecCt stA
```

:::leanPillCaption "Send-B without leaking randomness"
:::
```anchor sendB (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
/-- Run B's send step. -/
def sendB (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stB : StB PK SK C Sym) := send .B kem ecEk ecCt stB
```

:::leanPillCaption "Send-B with leaking randomness"
:::
```anchor sendBrleak (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
/-- Run B's send step, also returning randomness used for key generation and encapsulation. -/
def sendBrleak (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) (stB : StB PK SK C Sym) :=
  sendWith .B leak.keygenRleak leak.encapsRleak ecEk ecCt stB
```


:::::

:::::gameCell "\\textsf{Specialized receive calls for A and B}" (kind := "compact-recv")

:::leanPillCaption "Receive-A"
:::
```anchor recvA (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
/-- Process a message at A (by specializing `recv` function) -/
def recvA (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stA : StA PK SK C Sym) (ρ : Message Sym) := recv .A kem hDet ecEk ecCt stA ρ
```

:::leanPillCaption "Receive-B"
:::
```anchor recvB (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
/-- Process a message at B (by specializing `recv` function) -/
def recvB (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stB : StB PK SK C Sym) (ρ : Message Sym) := recv .B kem hDet ecEk ecCt stB ρ
```

:::::




:::::gameCell "\\textsf{Shared send implementation}" (kind := "compact")

For party $`P`, the shared send follows Figures 17–18 with offset $`\delta_P`,
where $`\delta_A=1` and $`\delta_B=-1`. We write $`\bar P` for the peer of party $`P`.
The boxes mark the ciphertext guard, the acknowledgement-index correction and, for $`P=B`, the Send-B counter corrections.

$`\begin{array}{l}
(t_{\mathrm{res}\text{-}P},\mathsf{EK}_{\bar P},\mathit{ct}_P,i_{\mathrm{ch}})\gets\mathsf{st}_{\mathrm{res}} \\
(t_{\mathrm{req}\text{-}P},\mathsf{DK}_P,\mathit{ek}_P,L_{\mathrm{ch}})\gets\mathsf{st}_{\mathrm{req}} \\
I_P\gets\bot,\ t_{I_P}\gets\bot,\ \mathit{ch}\gets\bot,\ b\gets\bot \\
\mathsf{if}\;\mathit{ek}_P=\bot\wedge\mathsf{ACK}[t_{\mathrm{res}\text{-}P}].\mathsf{ctRec} \\
\qquad\wedge\mathsf{ACK}[t_{\mathrm{res}\text{-}P}+\delta_P].\mathsf{ctRec}\;\mathsf{then} \\
\quad t_{\mathrm{res}\text{-}P}\gets t_{\mathrm{res}\text{-}P}+2,\quad i_{\mathrm{ch}}\gets0 \\
\quad (\mathit{ek}_P,\mathit{dk}_P)\sample\KeyGen \\
\quad \mathsf{DK}_P[\boxed{t_{\mathrm{res}\text{-}P}}+\delta_P]\gets\mathit{dk}_P \\
\mathsf{if}\;\neg\mathsf{ACK}[\boxed{t_{\mathrm{res}\text{-}P}}+\delta_P].\mathsf{ekRec}\;\mathsf{then} \\
\quad i_{\mathrm{ch}}\gets i_{\mathrm{ch}}+1,\quad b\gets0 \\
\quad \mathit{ch}\gets\mathsf{Encode}(\mathit{ek}_P,i_{\mathrm{ch}}) \\
\mathsf{else\ if}\;\neg\mathsf{ACK}[\boxed{t_{\mathrm{res}\text{-}P}}].\mathsf{ctRec}\;\mathsf{then} \\
\quad\mathsf{if}\;\mathit{ct}_P=\bot\wedge\mathsf{ACK}[t_{\mathrm{res}\text{-}P}].\mathsf{ekRec}\;\mathsf{then} \\
\qquad t_{I_P}\gets t_{\mathrm{res}\text{-}P},\quad i_{\mathrm{ch}}\gets0 \\
\qquad(\mathit{ct}_P,I_P)\sample\Encaps(\mathsf{EK}_{\bar P}[t_{\mathrm{res}\text{-}P}]) \\
\quad\boxed{\mathsf{if}\;\mathit{ct}_P\ne\bot\;\mathsf{then}} \\
\qquad i_{\mathrm{ch}}\gets i_{\mathrm{ch}}+1,\quad b\gets1 \\
\qquad \mathit{ch}\gets\mathsf{Encode}(\mathit{ct}_P,i_{\mathrm{ch}}) \\
t^{\mathrm{snd}}_P\gets\max\{t:\mathsf{ACK}[t].\mathsf{ctRec} \\
\qquad\wedge\mathsf{ACK}[t-1].\mathsf{ctRec}\} \\
\mathit{ack}\gets(\mathsf{ACK}[\boxed{t_{\mathrm{req}\text{-}P}-\delta_P}].\mathsf{ekRec},\mathsf{ACK}[t_{\mathrm{req}\text{-}P}].\mathsf{ctRec}) \\
\rho\gets(\mathit{ch},t_{\mathrm{res}\text{-}P},t_{\mathrm{req}\text{-}P},t^{\mathrm{snd}}_P,\mathit{ack},b) \\
\mathsf{st}_{\mathrm{res}}\gets(t_{\mathrm{res}\text{-}P},\mathsf{EK}_{\bar P},\mathit{ct}_P,i_{\mathrm{ch}}) \\
\mathsf{st}_{\mathrm{req}}\gets(t_{\mathrm{req}\text{-}P},\mathsf{DK}_P,\mathit{ek}_P,L_{\mathrm{ch}}) \\
\mathsf{return}\;((t_{I_P},I_P),\rho,t^{\mathrm{snd}}_P, \\
\qquad(\mathsf{st}_{\mathrm{res}},\mathsf{st}_{\mathrm{req}},\mathsf{ACK}))
\end{array}`

```anchor sendWith (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def sendWith {RKey REnc : Type} (role : Role)
    (keygen : m ((PK × SK) × RKey)) (encaps : PK → m ((C × K) × REnc))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) :
    m (Option (Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym ×
      SendRand RKey REnc)) := do
  let mut ⟨tRes, ekPeer, ct, ich⟩ := st.res
  let mut ⟨tReq, dk, ek, receivedChunks⟩ := st.req
  let ack := st.ack
  let mut key? : Option (ℕ × K) := none
  let mut ch? : Option (ℕ × Sym) := none
  let mut bit? : Option Bit := none
  let mut rKey? : Option RKey := none
  let mut rEnc? : Option REnc := none
  -- if ready to advance the epoch (Line 4 in the paper CKA-Send-P)
  if ek.isNone && decide (tRes ∈ ack.ctRec ∧
      tRes + role.offset ∈ ack.ctRec) then
    let ((newEk, newDk), rKey) ← keygen
    tRes := tRes + 2
    -- the epoch for which the decapsulation key was generated
    -- (tRes+1 in CKA-Send-A, line 8; tRes-1 in CKA-Send-B, line 8)
    let keyEpoch := tRes + role.offset
    dk := (keyEpoch, newDk) :: dk.filter (fun p => p.1 != keyEpoch)
    ek := some newEk
    ich := 0
    rKey? := some rKey
  -- if the encapsulation key was not yet received by the peer (lines 9-12 in CKA-Send-P)
  if tRes + role.offset ∉ ack.ekRec then
    -- Per paper's convention: if there is no key, return error
    let some localEk := ek | return none
    ich := ich + 1
    ch? := some (ecEk.encode localEk ich)
    bit? := some 0
  -- if the encapsulation key was received, but ciphertext was **not** yet received by the peer
  else if tRes ∉ ack.ctRec then
    -- if no ciphertext is stored and the peer's encapsulation key has been received
    -- (lines 14-16 in CKA-Send-P)
    if ct.isNone && decide (tRes ∈ ack.ekRec) then
      -- Receipt was recorded, so encapsulation now requires this key.
      let some peerEk := ekPeer tRes | return none
      let ((newCt, key), rEnc) ← encaps peerEk
      ct := some newCt
      key? := some (tRes.toNat, key)
      ich := 0
      rEnc? := some rEnc
    -- Corrected line 17: a ciphertext chunk is sent only once a ciphertext exists.
    -- While waiting for the peer's key, the message carries no payload.
    if let some ciphertext := ct then
      ich := ich + 1
      ch? := some (ecCt.encode ciphertext ich)
      bit? := some 1
  let st : State PK SK C Sym :=
    { res := ⟨tRes, ekPeer, ct, ich⟩
      req := ⟨tReq, dk, ek, receivedChunks⟩
      ack }
  let ρ : Message Sym :=
    { ch := ch?, bit := bit?, tRes, tReq
      -- Largest nonnegative index with two adjacent acknowledged ciphertexts
      -- (both t and t-1 in ack.ctRec).
      -- The empty maximum is zero; honest states initially acknowledge `-1` and `0`.
      sendingEpoch := (ack.ctRec.filter fun t => t - 1 ∈ ack.ctRec).sup Int.toNat
      ack := { ekRec := decide (tReq - role.offset ∈ ack.ekRec)
               ctRec := decide (tReq ∈ ack.ctRec) } }
  return some (key?, ρ, ρ.sendingEpoch, st,
    { keygenRand := rKey?, encapsRand := rEnc? })
```


:::::

:::::gameCell "\\textsf{Shared receive implementation}" (kind := "compact")
For party $`P`, the shared receive follows Figures 17–18 with offset $`\delta_P`,
where $`\delta_A=1` and $`\delta_B=-1`. We write $`\bar P` for the peer of party $`P`.
The boxes mark the acknowledgement-index correction and, for $`P=A`, the corrected received-ciphertext variable.

$`\begin{array}{l}
(t_{\mathrm{res}\text{-}P},\mathsf{EK}_{\bar P},\mathit{ct}_P,i_{\mathrm{ch}})\gets\mathsf{st}_{\mathrm{res}} \\
(t_{\mathrm{req}\text{-}P},\mathsf{DK}_P,\mathit{ek}_P,L_{\mathrm{ch}})\gets\mathsf{st}_{\mathrm{req}} \\
(\mathit{ch},t_{\mathrm{res}\text{-}\bar P},t_{\mathrm{req}\text{-}\bar P},t^{\mathrm{snd}}_{\bar P},\mathit{ack},b)\gets\rho \\
I_{\bar P}\gets\bot,\quad t_{I_{\bar P}}\gets\bot \\
\mathsf{if}\;\mathit{ack}.\mathsf{ctRec}\;\mathsf{then} \\
\quad\mathsf{ACK}[t_{\mathrm{req}\text{-}\bar P}].\mathsf{ctRec}\gets\mathsf{true} \\
\mathsf{if}\;\mathit{ack}.\mathsf{ekRec}\;\mathsf{then} \\
\quad\mathsf{ACK}[\boxed{t_{\mathrm{req}\text{-}\bar P}+\delta_P}].\mathsf{ekRec}\gets\mathsf{true} \\
\mathsf{if}\;t_{\mathrm{res}\text{-}\bar P}<t_{\mathrm{req}\text{-}P}\;\mathsf{then}\;\mathsf{break} \\
\mathsf{else\ if}\;t_{\mathrm{res}\text{-}\bar P}>t_{\mathrm{req}\text{-}P}\;\mathsf{then}\;t_{\mathrm{req}\text{-}P}\gets t_{\mathrm{req}\text{-}P}+2 \\
\mathsf{if}\;\mathsf{EK}_{\bar P}[t_{\mathrm{req}\text{-}P}-\delta_P]=\bot\wedge b=0\;\mathsf{then} \\
\quad L_{\mathrm{ch}}\gets L_{\mathrm{ch}}\cup\{\mathit{ch}\} \\
\quad \mathit{ek}_{\bar P}\gets\mathsf{Decode}(L_{\mathrm{ch}}) \\
\quad\mathsf{if}\;\mathit{ek}_{\bar P}\ne\bot\;\mathsf{then} \\
\qquad L_{\mathrm{ch}}\gets\emptyset \\
\qquad\mathsf{EK}_{\bar P}[t_{\mathrm{req}\text{-}P}-\delta_P]\gets\mathit{ek}_{\bar P} \\
\qquad\mathsf{ACK}[t_{\mathrm{req}\text{-}P}-\delta_P].\mathsf{ekRec}\gets\mathsf{true} \\
\mathsf{else\ if}\;\neg\mathsf{ACK}[t_{\mathrm{req}\text{-}P}].\mathsf{ctRec}\wedge b=1\;\mathsf{then} \\
\quad L_{\mathrm{ch}}\gets L_{\mathrm{ch}}\cup\{\mathit{ch}\} \\
\quad \boxed{\mathit{ct}_{\bar P}}\gets\mathsf{Decode}(L_{\mathrm{ch}}) \\
\quad\mathsf{if}\;\mathit{ct}_{\bar P}\ne\bot\;\mathsf{then} \\
\qquad L_{\mathrm{ch}}\gets\emptyset \\
\qquad\mathsf{ACK}[t_{\mathrm{req}\text{-}P}].\mathsf{ctRec}\gets\mathsf{true} \\
\qquad t_{I_{\bar P}}\gets t_{\mathrm{req}\text{-}P} \\
\qquad I_{\bar P}\gets\Decaps(\mathsf{DK}_P[t_{\mathrm{req}\text{-}P}],\mathit{ct}_{\bar P}) \\
\qquad\mathsf{DK}_P[t_{\mathrm{req}\text{-}P}]\gets\bot \\
\mathsf{if}\;\mathsf{ACK}[t_{\mathrm{res}\text{-}P}].\mathsf{ctRec}\;\mathsf{then}\;\mathit{ct}_P\gets\bot \\
\mathsf{if}\;\mathsf{ACK}[t_{\mathrm{res}\text{-}P}+\delta_P].\mathsf{ekRec}\;\mathsf{then}\;\mathit{ek}_P\gets\bot \\
\mathsf{st}_{\mathrm{res}}\gets(t_{\mathrm{res}\text{-}P},\mathsf{EK}_{\bar P},\mathit{ct}_P,i_{\mathrm{ch}}) \\
\mathsf{st}_{\mathrm{req}}\gets(t_{\mathrm{req}\text{-}P},\mathsf{DK}_P,\mathit{ek}_P,L_{\mathrm{ch}}) \\
\mathsf{return}\;((t_{I_{\bar P}},I_{\bar P}),t^{\mathrm{snd}}_{\bar P}, \\
\qquad(\mathsf{st}_{\mathrm{res}},\mathsf{st}_{\mathrm{req}},\mathsf{ACK}))
\end{array}`


```anchor recv (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def recv (role : Role) (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym) :
    Option (Option (ℕ × K) × ℕ × State PK SK C Sym) := do
  let mut ⟨resEpoch, ekPeer, ct, ich⟩ := st.res
  let mut ⟨reqEpoch, dk, ek, receivedChunks⟩ := st.req
  let ⟨ch?, peerResEpoch, peerReqEpoch, sendingEpoch, peerAck, bit?⟩ := ρ
  let mut localAck := st.ack
  let mut key? : Option (ℕ × K) := none
  -- Incorporate the peer's acknowledgements first.
  if peerAck.ctRec then
    localAck := { localAck with ctRec := insert peerReqEpoch localAck.ctRec }
  if peerAck.ekRec then
    localAck := { localAck with
      ekRec := insert (peerReqEpoch + role.offset) localAck.ekRec }
  -- outdated message: retain only the acknowledgement updates
  if peerResEpoch < reqEpoch then
    return (none, sendingEpoch, { st with ack := localAck })
   -- first message of the new epoch, lines 11-12
  if reqEpoch < peerResEpoch then
    reqEpoch := reqEpoch + 2
  -- Captures the relation of "1 removed" epochs
  --   - if A is requesting the key for epoch t, it receives B's public key for t-1
  --   - if B is requesting the key for epoch t, it receives A's public key for t+1
  let peerKeyEpoch := reqEpoch - role.offset
  -- if the peer's encapsulating key has not been received yet, lines 13-19
  if (ekPeer peerKeyEpoch).isNone ∧ bit? = some 0 then
    let (chunks, peerEk?) := insertChunkAndDecode ecEk receivedChunks ch?
    receivedChunks := chunks
    if let some peerEk := peerEk? then
      ekPeer := Function.update ekPeer peerKeyEpoch (some peerEk)
      receivedChunks := ∅
      localAck := { localAck with ekRec := insert peerKeyEpoch localAck.ekRec }
  -- if ciphertext has not been received and the bit is 1, lines 20-28
  else if reqEpoch ∉ localAck.ctRec ∧ bit? = some 1 then
    let (chunks, peerCt?) := insertChunkAndDecode ecCt receivedChunks ch?
    receivedChunks := chunks
    if let some peerCt := peerCt? then
      -- Paper convention: A missing required key or failed decapsulation should
      -- fail the whole function (return `none` in our Option), accomplished here by bindings.
      let secretKey ← dk.lookup reqEpoch
      let key ← hDet.decapsDet secretKey peerCt
      receivedChunks := ∅
      localAck := { localAck with ctRec := insert reqEpoch localAck.ctRec }
      key? := some (reqEpoch.toNat, key)
      dk := dk.filter (fun p => p.1 != reqEpoch)
   -- deleting the stored material that has been fully delivered (lines 29-32)
  if resEpoch ∈ localAck.ctRec then
    ct := none
  if resEpoch + role.offset ∈ localAck.ekRec then
    ek := none
  return (key?, sendingEpoch,
    { res := ⟨resEpoch, ekPeer, ct, ich⟩
      req := ⟨reqEpoch, dk, ek, receivedChunks⟩
      ack := localAck })
```
:::::

::::::

:::leanPillCaption "SCKA scheme instance"
:::
```anchor scheme (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
/-- Assemble Opp-BiKEM as an SCKA scheme from a KEM with deterministic decapsulation,
public-key and ciphertext erasure codes, and randomness-leaking KEM operations. -/
def scheme (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) :
    SCKAScheme m Unit (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
      (SendRand leak.KeygenRand leak.EncapsRand) where
  initKeyGen := initKeyGen
  initA := initA
  initB := initB
  sendA := sendA kem ecEk ecCt
  sendArleak := sendArleak kem ecEk ecCt leak
  recvA := recvA kem hDet ecEk ecCt
  sendB := sendB kem ecEk ecCt
  sendBrleak := sendBrleak kem ecEk ecCt leak
  recvB := recvB kem hDet ecEk ecCt
```

:::::::

:::defTitle "opp_bikem_cka_correctness" "Opp-BiKEM-CKA correctness"
:::

::::theorem "opp_bikem_cka_correctness" (parent := "cka_protocols_opp_bikem_cka") (lean := "oppBiKemCKA.correctness_true_ge") (tags := "gh-110") (uses := "opp_bikem_cka_spec, scka_correctness, erasure_code_correctness")
Assume that:

* $`\adv` is any SCKA correctness adversary making at most $`q` send-oracle
  queries;
* the underlying KEM has deterministic decapsulation,
  and has correctness error at most $`\varepsilon`;
* and the two erasure codes, for public keys and for ciphertexts, are correct.

Then $`\Pr\bigl[\Exp{\textsf{cor}}{\textsf{Opp-BiKEM-CKA}}(\adv)=1\bigr]
  \ge 1-q\varepsilon`, i.e., the Opp-BiKEM-CKA protocol is correct with probability at least
$`1-q\varepsilon`.


```anchor correctnessTrueGe (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Correctness)
theorem correctness_true_ge
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    Pr[= true | SCKAScheme.correctnessExp (scheme kem hDet ecEk ecCt leak) adv] ≥
      1 - (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp
```
::::

:::defTitle "opp_bikem_cka_security" "Opp-BiKEM-CKA security"
:::

::::theorem "opp_bikem_cka_security" (parent := "cka_protocols_opp_bikem_cka") (tags := "gh-111") (uses := "opp_bikem_cka_spec, scka_security, erasure_code_scheme")
$`\todo`

:::leanPill "missing"
:::
::::

# Errata
%%%
tag := "opp-bikem-errata"
number := false
htmlSplit := .never
%%%

::::gameCell "\\textsf{Opp-BiKEM-CKA errata}" (kind := "errata")

The following errata explain the differences from the paper.
The {bpref "opp_bikem_cka_spec"}[protocol definition] uses the corrections from errata 1, 2 and 3.

*Erratum 1: Sending is blocked while waiting for the peer's key.*

In Figures 17–18, `CKA-Send-P` can reach line 19, `ch ← Encode(ct_P, i_ch)`, with `ct_P = ⊥`,
where `P` stands for either `A` or `B`.
In Figure 17, `CKA-Send-A`, lines 13–19 read as follows; Figure 18, `CKA-Send-B`, is symmetric.

```
13: elseif ¬ACK[t_res-A].ct-rec            / ct_A not yet received by B
14:   if ct_A = ⊥ ∧ ACK[t_res-A].ek-rec
15:     t_IA ← t_res-A; i_ch ← 0
16:     (ct_A, I_A) ← Enc(EK_B[t_res-A])
17:   i_ch += 1
18:   b ← 1
19:   ch ← Encode(ct_A, i_ch)               / ct_A may still be ⊥ here
```

When line 13 holds but line 14 does not, `ct_A` is still `⊥` at line 19:
B has acknowledged A's key, but A has not yet decoded B's key.
Under the paper's §2 convention, `Encode(⊥, ·)` fails, so the send aborts, as does the
`SM-Send-A` call that invokes it (Figure 2, line 1).
A cannot send any message until it decodes `ek_B`.

This state occurs in honest runs with in-order delivery, because the parties send their
encapsulation keys concurrently.
Let `n ≥ 2` be the number of chunks needed to decode an encapsulation key.
Initially, A has `t_res-A = −1` and `t_req-A = 0`, B has `t_res-B = 0` and `t_req-B = −1`,
and both have `ACK[−1].ct-rec = ACK[0].ct-rec = true`.
The trace uses the corrected indices from errata 2 and 3.

1. A sends `n` messages. Line 4 holds, so A sets `t_res-A = 1` and generates `ek_A` for
   epoch 2. `ACK[2].ek-rec` is false, so each message carries a chunk of `ek_A` (line 9).
2. B receives them. The first message moves `t_req-B` to 1 (Rec-B lines 11–12).
   After the `n`-th message, B decodes `ek_A` and sets `ACK[2].ek-rec` (Rec-B lines 18–19).
3. B sends one message. Line 4 holds, so B sets `t_res-B = 2` and generates `ek_B` for
   epoch 1. Line 9 sends the first chunk of `ek_B`, and line 21 acknowledges `ACK[2].ek-rec`.
4. A receives it. A records `ACK[2].ek-rec` (Rec-A line 8), moves `t_req-A` to 2, and stores
   the chunk (lines 13–15). One chunk is insufficient to decode, so `ACK[1].ek-rec` stays false.
5. A sends. Line 4 is false (`ACK[1].ct-rec` is false), line 9 is false (`ACK[2].ek-rec` holds),
   line 13 is true (`ACK[1].ct-rec` is false), and line 14 is false (`ACK[1].ek-rec` is false).
   Lines 17–19 run with `ct_A = ⊥`.

The correction is to send a ciphertext chunk only when a ciphertext exists:
lines 17–19 of Figures 17–18 are guarded by $`\boxed{\mathsf{if}\;\mathit{ct}_P\ne\bot}`,
and lines 19–21 of Figure 19 likewise.
The corrected lines 13–20 of Figure 17 read as follows; Figure 18 is symmetric.

```
13: elseif ¬ACK[t_res-A].ct-rec
14:   if ct_A = ⊥ ∧ ACK[t_res-A].ek-rec
15:     t_IA ← t_res-A; i_ch ← 0
16:     (ct_A, I_A) ← Enc(EK_B[t_res-A])
17:   if ct_A ≠ ⊥
18:     i_ch += 1
19:     b ← 1
20:     ch ← Encode(ct_A, i_ch)
```

While waiting, the message carries only epochs and acknowledgements, with `ch = ⊥` and `b = ⊥`,
and `i_ch` is unchanged.
`OppBiKEM/Construction.lean` uses this guard, recorded as correction 4 in its module docstring.

*Erratum 2: Public-key acknowledgements use the wrong indices.*

In Figures 17–18, Send line 21 sends the `ek-rec` acknowledgement at the wrong epoch.
Rec line 8 also records it at the wrong epoch.
The following table gives the printed and corrected indices.

:::table +header (align := left)
*
  * Line
  * Printed
  * Corrected
*
  * Figure 17, `CKA-Send-A` line 21
  * `ACK[t_req-A + 1].ek-rec`
  * `ACK[t_req-A − 1].ek-rec`
*
  * Figure 17, `CKA-Rec-A` line 8
  * `ACK[t_req-B − 1].ek-rec ← true`
  * `ACK[t_req-B + 1].ek-rec ← true`
*
  * Figure 18, `CKA-Send-B` line 21
  * `ACK[t_req-B − 1].ek-rec`
  * `ACK[t_req-B + 1].ek-rec`
*
  * Figure 18, `CKA-Rec-B` line 8
  * `ACK[t_req-A + 1].ek-rec ← true`
  * `ACK[t_req-A − 1].ek-rec ← true`
:::

The corrected indices identify the entries set when a party decodes its peer's key:
`ACK[t_req-A − 1].ek-rec` in Rec-A line 19 and `ACK[t_req-B + 1].ek-rec` in Rec-B line 19.
The printed indices differ by two epochs.

With the printed indices, neither party learns that its first public key arrived.
The following trace starts from initialization and delivers every message once, in order.
Let `n ≥ 1` be the number of chunks needed to decode an encapsulation key.
The trace applies the Send-B variable fix from erratum 3.

Initially, A has `t_res-A = −1` and `t_req-A = 0`.
B has `t_res-B = 0` and `t_req-B = −1`.
Both have `ACK[−1].ct-rec = ACK[0].ct-rec = true`, and every `ek-rec` entry is false.

1. A sends `n` messages. Send-A line 4 holds, so A sets `t_res-A = 1` and generates
   `ek_A` for epoch 2. `ACK[2].ek-rec` is false, so each message carries a chunk of `ek_A` (line 9).
2. B receives them. The first message moves `t_req-B` to 1 (Rec-B lines 11–12).
   After the `n`-th message, B decodes `ek_A` and sets `ACK[2].ek-rec` (Rec-B line 19).
3. B sends `n` messages. Send-B line 4 holds, so B sets `t_res-B = 2` and generates
   `ek_B` for epoch 1. Each message carries a chunk of `ek_B`.
   Line 21 acknowledges `ACK[t_req-B − 1].ek-rec = ACK[0].ek-rec`, which is false.
   The entry B just set is `ACK[2]`.
4. A receives them. Rec-A line 8 records nothing. The first message moves `t_req-A` to 2.
   After the `n`-th message, A decodes `ek_B` and sets `ACK[1].ek-rec` (line 19).
   `ACK[2].ek-rec` is still false, so A keeps `ek_A` (lines 31–32).
5. A sends. Line 4 is false (`ek_A ≠ ⊥`) and line 9 is true (`ACK[2].ek-rec` is false),
   so A resends a chunk of `ek_A`.
   Line 21 acknowledges `ACK[t_req-A + 1].ek-rec = ACK[3].ek-rec`, which is false.
   The entry A just set is `ACK[1]`.
6. B receives it and sends. Rec-B line 8 records nothing, so B's `ACK[1].ek-rec` stays false.
   B keeps `ek_B` (lines 31–32) and resends a chunk of `ek_B`, again acknowledging `ACK[0].ek-rec`.

Steps 5–6 repeat forever. A leaves line 9 only once `ACK[2].ek-rec` holds.
Rec-A line 19 sets only odd entries because `t_req-A` is even.
Line 8 sets `ACK[t_req-B − 1]`, which equals `ACK[2]` only once `t_req-B = 3`.
That requires A to advance to `t_res-A = 3` (Send-A line 4), which requires `ek_A = ⊥`.
Clearing `ek_A` requires `ACK[2].ek-rec` (Rec-A lines 31–32), so A cannot advance.

B leaves line 9 only once `ACK[1].ek-rec` holds.
Rec-B line 19 sets only even entries because `t_req-B` is odd.
Line 8 sets `ACK[t_req-A + 1]`, which equals `ACK[1]` only for messages A sends with `t_req-A = 0`.
A sends those messages before decoding `ek_B`, so their acknowledgement bit is false.

Neither party reaches the ciphertext branch at line 13, so no key is ever established.
With the corrected indices, step 3 acknowledges `ACK[2]` and step 5 acknowledges `ACK[1]`, and the run proceeds.
`OppBiKEM/Construction.lean` uses the corrected indices, recorded as correction 3 in its module docstring.

*Erratum 3: Variable typos in Send-B and Rec-A.*

In Figure 18, `CKA-Send-B`, lines 8, 9, and 13 use `t_res-A`, which is absent from B's state.
The corrected variable is $`\boxed{t_{\mathrm{res}\text{-}B}}`, as in lines 14–16.
The corrected expressions are `DK_B[t_res-B − 1] ← dk_B`, `¬ACK[t_res-B − 1].ek-rec`, and `¬ACK[t_res-B].ct-rec`.

In Figure 17, `CKA-Rec-A`, line 22 reads `ct_A ← Decode(L_ch)`, which overwrites A's own ciphertext.
The corrected assignment is `ct_B ← Decode(L_ch)`, with $`\boxed{\mathit{ct}_B}`, as used in lines 23 and 27.
`OppBiKEM/Construction.lean` uses the corrected variables, recorded as correction 1 in its module docstring.

::::
