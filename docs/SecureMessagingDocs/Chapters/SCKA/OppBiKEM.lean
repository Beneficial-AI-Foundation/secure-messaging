import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Bibliography
import SecureMessaging.SCKA.OppBiKEM.Construction

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

:::::::definition "opp_bikem_cka_spec" (parent := "cka_protocols_opp_bikem_cka") (lean := "oppBiKemCKA.initKeyGen, oppBiKemCKA.initA, oppBiKemCKA.initB, oppBiKemCKA.vulnA, oppBiKemCKA.vulnB, oppBiKemCKA.sendA, oppBiKemCKA.sendArleak, oppBiKemCKA.recvA, oppBiKemCKA.sendB, oppBiKemCKA.sendBrleak, oppBiKemCKA.recvB, oppBiKemCKA.scheme")
Figures 17 and 18 of {Informal.citet SCKA25}[]. This construction uses a standard
KEM: $`A` encapsulates in odd epochs and $`B` encapsulates in even epochs. Both parties
send public-key chunks opportunistically, before transmitting ciphertext chunks.
There is no offline/online ciphertext split. TODO: check this claim

Each party has two counters:

- $`t_{\mathrm{req}}` for the epoch in which it plays the *requester* role (a requester decapsulates the received encapsulated key).
- $`t_{\mathrm{res}}` for the epoch in which it plays the *responder* role (a responder encapsulates the key using the requester's public key).

The two roles share Lean helpers, with offsets $`\delta_\A=1` and
$`\delta_\B=-1`.

We make the following corrections with respect to the pseudocode:

* In Figure 18, $`\mathsf{CKA}\text{-}\SendB`, lines 8, 9, and 13, replace
  $`\boxed{t_{\mathrm{res},A}\mapsto t_{\mathrm{res},B}}`.
  B's local state contains B's responder counter.
* In Figure 17, $`\mathsf{CKA}\text{-}\mathsf{Rec}\text{-}\A`, line 22, replace
  $`\boxed{\mathit{ct}_A\mapsto\mathit{ct}_B}`. Lines 23 and 27 already use B's ciphertext.
* Public-key acknowledgement indices are corrected at both ends of each message:
  in Figure 17, Send-A line 21 uses
  $`\boxed{t_{\mathrm{req},A}-1}` and Rec-A line 8 uses
  $`\boxed{t_{\mathrm{req},B}+1}`;
  in Figure 18, Send-B line 21 uses
  $`\boxed{t_{\mathrm{req},B}+1}` and Rec-B line 8 uses
  $`\boxed{t_{\mathrm{req},A}-1}`.
  These are the public-key entries set by decoding. The printed formulas
  advertise different entries, leaving the first public keys unacknowledged.
* The KEM interface returns $`(\ek,\dk)` from key generation and takes the
  secret key before the ciphertext in decapsulation. We follow that interface.
* Encoding an absent payload sends no chunk. Missing decapsulation prerequisites
  or failed decapsulation return no key, without acknowledging the ciphertext or
  erasing its secret key. These make the partial pseudocode total, following the
  Opp-UniKEM convention.
* The outdated-message `break` returns after incorporating the message's indexed
  acknowledgements, without processing its payload or running the later cleanup.

Unlike Opp-UniKEM's single current-epoch acknowledgement, these acknowledgements
are stored by epoch. An old message may acknowledge an old payload; it does not
acknowledge the receiver's newest payload.

::::::gameGrid

:::::gameCell "\\textsf{Roles, state, and messages}" (kind := "compact")

The arrays of public keys and secret keys are indexed by epoch. In Lean, public
keys use a function returning `Option PK`; stored secret keys use a finite
association list. Removing an entry models secret-key erasure. The chunk buffer
is a `Finset`, so receiving the same indexed chunk twice does not add information.

Internal counters use `ℤ`, since the paper starts at $`-1`. Actual SCKA key
outputs and sending epochs use `ℕ`. The initialized dummy epochs never generate
honest keys.

```anchor role (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
inductive Role where
  | A
  | B
  deriving DecidableEq

def Role.offset : Role → ℤ
  | .A => 1
  | .B => -1
```
```anchor state (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
structure State (PK SK C Sym : Type) where
  resEpoch : ℤ
  ekPeer : ℤ → Option PK
  ct : Option C
  ich : ℕ
  reqEpoch : ℤ
  dk : List (ℤ × SK)
  ek : Option PK
  received_chunks : Finset (ℕ × Sym)
  ack : Acknowledgements

abbrev StA := State
abbrev StB := State
```
```anchor message (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
abbrev Bit := Fin 2

structure Message (Sym : Type) where
  ch : Option (ℕ × Sym)
  resEpoch : ℤ
  reqEpoch : ℤ
  sendingEpoch : ℕ
  ack : Ack
  bit : Option Bit
```
```anchor sendRand (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
structure SendRand (KeygenRand EncapsRand : Type) where
  keygen : Option KeygenRand
  encaps : Option EncapsRand
```
:::::

:::::gameCell "\\textsf{Acknowledgements and sending epoch}" (kind := "compact")

$`t^{\mathrm{snd}}=\max\{t\ge0:\mathsf{ACK}[t].\mathsf{ctRec}
\wedge\mathsf{ACK}[t-1].\mathsf{ctRec}\}`.

The two finite sets represent the true entries of the acknowledgement array.
`Finset.sup` computes the maximum, using zero for an empty set. A message carries
this sending epoch explicitly; receive returns that value even on delayed delivery.

```anchor acknowledgements (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
structure Acknowledgements where
  ekRec : Finset ℤ
  ctRec : Finset ℤ

/-- Largest nonnegative index with two adjacent acknowledged ciphertexts
(both t and t-1 in act.ctRec).
The empty maximum is zero; honest states initially acknowledge `-1` and `0`. -/
def Acknowledgements.sendingEpoch (ack : Acknowledgements) : ℕ :=
  (ack.ctRec.filter fun t => t - 1 ∈ ack.ctRec).sup Int.toNat
```
:::::

:::::gameCell "\\textsf{Initialisation}" (kind := "compact")

$`I_{\mathsf{CKA}}=\bot`,
$`(t_{\mathrm{res}\text{-}\A},t_{\mathrm{req}\text{-}\A})=(-1,0)`, and
$`(t_{\mathrm{res}\text{-}\B},t_{\mathrm{req}\text{-}\B})=(0,-1)`.
All payloads and arrays start empty, except for the ciphertext acknowledgements
at $`-1` and $`0`, which enable the first key generation.

```anchor initKeyGen (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def initKeyGen : m Unit := pure ()
```
```anchor init (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def init (role : Role) (_ik : Unit) : m (State PK SK C Sym) :=
  pure { resEpoch := if role = .A then -1 else 0
         reqEpoch := if role = .A then 0 else -1
         ekPeer := fun _ => none
         ct := none, ich := 0, dk := [], ek := none, received_chunks := ∅
         ack := { ekRec := ∅, ctRec := {-1, 0} } }
```
```anchor initA (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def initA : Unit → m (StA PK SK C Sym) := init .A
```
```anchor initB (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def initB : Unit → m (StB PK SK C Sym) := init .B
```
:::::

:::::gameCell "\\textsf{Vulnerable epochs}" (kind := "compact")

$`\mathsf{st}_P.\mathsf{vuln}=\{t>0:\mathsf{DK}_P[t]\ne\bot\}`.
Only retained decapsulation keys contribute. Public keys and ciphertexts do not
require secrecy. Dummy epochs are excluded from the natural-number SCKA interface.

```anchor vuln (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def vuln (st : State PK SK C Sym) : Finset ℕ :=
  ((st.dk.map Prod.fst).toFinset.filter fun t => 0 < t).image Int.toNat

def vulnA (st : StA PK SK C Sym) : Finset ℕ := vuln st

def vulnB (st : StB PK SK C Sym) : Finset ℕ := vuln st
```
:::::

:::::gameCell "\\mathsf{CKA}\\text{-}\\mathsf{Send}\\text{-}P" (kind := "compact")

Writing $`r=t_{\mathrm{res}}` and $`\delta=\delta_P`, the shared send follows
Figures 17–18 in this order:

* If the local public key is absent and ciphertexts $`r` and $`r+\delta` are
  acknowledged, advance $`r` by two, generate a key pair, and store its secret
  key at $`r+\delta`.
* Until that public key is acknowledged, send its next chunk (selector zero).
* Otherwise, if ciphertext $`r` is not acknowledged, encapsulate once the peer's
  public key at $`r` is available, output key $`(r,I_P)`, and send ciphertext
  chunks (selector one). Reset the chunk counter when generating the ciphertext.
* Attach the counters, sending epoch, and acknowledgements for the peer's public
  key at $`t_{\mathrm{req}}-\delta` and ciphertext at $`t_{\mathrm{req}}`.

The shared helper takes the randomized KEM calls as arguments. Ordinary sends
supply calls with dummy `Unit` coins; leaking sends supply the existing
`KEMScheme.RandLeak` operations. Both therefore execute the same branches.

```anchor sendWith (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def sendWith {RKey REnc : Type} (role : Role)
    (keygen : m ((PK × SK) × RKey)) (encaps : PK → m ((C × K) × REnc))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) :
    m (Option (Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym ×
      SendRand RKey REnc)) := do
  let (st, rKey?) ←
    if st.ek.isNone && decide (st.resEpoch ∈ st.ack.ctRec ∧
        st.resEpoch + role.offset ∈ st.ack.ctRec) then do
      let ((ek, dk), rKey) ← keygen
      let t := st.resEpoch + 2
      let keyEpoch := t + role.offset
      pure ({ st with resEpoch := t, ich := 0, ek := some ek
                      dk := (keyEpoch, dk) :: st.dk.filter (fun p => p.1 != keyEpoch) },
            some rKey)
    else pure (st, none)
  let (key?, ch?, bit?, st, rEnc?) ←
    if st.resEpoch + role.offset ∉ st.ack.ekRec then do
      let ich := st.ich + 1
      let ch? := st.ek.map (fun ek => ecEk.encode ek ich)
      pure (none, ch?, some (0 : Bit), { st with ich }, none)
    else if st.resEpoch ∉ st.ack.ctRec then do
      let (key?, st, rEnc?) ←
        if st.ct.isNone && decide (st.resEpoch ∈ st.ack.ekRec) then
          match st.ekPeer st.resEpoch with
          | none => pure (none, st, none)
          | some ekPeer => do
              let ((ct, key), rEnc) ← encaps ekPeer
              pure (some (st.resEpoch.toNat, key), { st with ct := some ct, ich := 0 },
                some rEnc)
        else pure (none, st, none)
      let ich := st.ich + 1
      let ch? := st.ct.map (fun ct => ecCt.encode ct ich)
      pure (key?, ch?, some (1 : Bit), { st with ich }, rEnc?)
    else pure (none, none, none, st, none)
  let ρ := message role st ch? bit?
  pure (some (key?, ρ, ρ.sendingEpoch, st, { keygen := rKey?, encaps := rEnc? }))
```
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
```anchor sendA (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def sendA (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stA : StA PK SK C Sym) := send .A kem ecEk ecCt stA
```
```anchor sendB (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def sendB (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stB : StB PK SK C Sym) := send .B kem ecEk ecCt stB
```
```anchor sendArleak (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def sendArleak (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) (stA : StA PK SK C Sym) :=
  sendWith .A leak.keygenRleak leak.encapsRleak ecEk ecCt stA
```
```anchor sendBrleak (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def sendBrleak (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) (stB : StB PK SK C Sym) :=
  sendWith .B leak.keygenRleak leak.encapsRleak ecEk ecCt stB
```
:::::

:::::gameCell "\\mathsf{CKA}\\text{-}\\mathsf{Rec}\\text{-}P" (kind := "compact")

A received acknowledgement concerns the sender's requestor counter: record
ciphertext receipt at $`t'_{\mathrm{req}}` and public-key receipt at
$`t'_{\mathrm{req}}+\delta_P`.

Ignore outdated payloads; if the peer's responder counter is newer, advance the
local requestor counter by two. Decode public-key chunks into the peer-key array
at $`t_{\mathrm{req}}-\delta_P`. Decode ciphertext chunks for epoch
$`t_{\mathrm{req}}`; successful decapsulation outputs that epoch's key,
acknowledges its ciphertext, clears the chunk buffer, and erases its secret key.
Finally, clear acknowledged outgoing payloads.

For a Lean beginner, the pattern `some dk` unwraps an available secret key.
`hDet.decapsDet` is a pure decapsulation function whose witness proves agreement
with the KEM's monadic operation. This is needed because SCKA receive functions
are pure. An inner `none` means no epoch key was produced; the outer `some`
means the receive operation returned successfully.

```anchor recv (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def recv (role : Role) (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym) :
    Option (Option (ℕ × K) × ℕ × State PK SK C Sym) :=
  let ack := st.ack
  let ack := if ρ.ack.ctRec then { ack with ctRec := insert ρ.reqEpoch ack.ctRec } else ack
  let ack := if ρ.ack.ekRec then
      { ack with ekRec := insert (ρ.reqEpoch + role.offset) ack.ekRec } else ack
  let st := { st with ack }
  if ρ.resEpoch < st.reqEpoch then
    some (none, ρ.sendingEpoch, st)
  else
    let st := if st.reqEpoch < ρ.resEpoch then
        { st with reqEpoch := st.reqEpoch + 2 } else st
    let peerKeyEpoch := st.reqEpoch - role.offset
    let (key?, st) :=
      match ρ.bit, ρ.ch with
      | some 0, some ch =>
          if (st.ekPeer peerKeyEpoch).isNone then
            let received_chunks := insert ch st.received_chunks
            match ecEk.decode received_chunks with
            | none => (none, { st with received_chunks })
            | some ekPeer =>
                (none, { st with received_chunks := ∅
                                 ekPeer := Function.update st.ekPeer peerKeyEpoch (some ekPeer)
                                 ack := { st.ack with ekRec := insert peerKeyEpoch st.ack.ekRec } })
          else (none, st)
      | some 1, some ch =>
          if st.reqEpoch ∉ st.ack.ctRec then
            match st.dk.lookup st.reqEpoch with
            | none => (none, st)
            | some dk =>
                let received_chunks := insert ch st.received_chunks
                match ecCt.decode received_chunks with
                | none => (none, { st with received_chunks })
                | some ct =>
                    match hDet.decapsDet dk ct with
                    | none => (none, st)
                    | some key =>
                        (some (st.reqEpoch.toNat, key),
                          { st with received_chunks := ∅
                                    dk := st.dk.filter (fun p => p.1 != st.reqEpoch)
                                    ack := { st.ack with
                                      ctRec := insert st.reqEpoch st.ack.ctRec } })
          else (none, st)
      | _, _ => (none, st)
    let st := if st.resEpoch ∈ st.ack.ctRec then { st with ct := none } else st
    let st := if st.resEpoch + role.offset ∈ st.ack.ekRec then { st with ek := none } else st
    some (key?, ρ.sendingEpoch, st)
```
```anchor recvA (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def recvA (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stA : StA PK SK C Sym) (ρ : Message Sym) := recv .A kem hDet ecEk ecCt stA ρ
```
```anchor recvB (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def recvB (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stB : StB PK SK C Sym) (ρ : Message Sym) := recv .B kem hDet ecEk ecCt stB ρ
```
:::::

::::::

:::leanPillCaption "SCKA scheme instance"
:::
```anchor scheme (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
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

{usesLabel}`uses` {uses "scka_scheme"}[] · {uses "erasure_code_scheme"}[] · {githubLabel}`github` {githubIssue 109}[]
:::::::

:::defTitle "opp_bikem_cka_correctness" "Opp-BiKEM-CKA correctness"
:::

::::theorem "opp_bikem_cka_correctness" (parent := "cka_protocols_opp_bikem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "opp_bikem_cka_spec"}[] · {uses "scka_correctness"}[] · {uses "erasure_code_correctness"}[] · {githubLabel}`github` {githubIssue 110}[]
::::

:::defTitle "opp_bikem_cka_security" "Opp-BiKEM-CKA security"
:::

::::theorem "opp_bikem_cka_security" (parent := "cka_protocols_opp_bikem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "opp_bikem_cka_spec"}[] · {uses "scka_security"}[] · {uses "erasure_code_scheme"}[] · {githubLabel}`github` {githubIssue 111}[]
::::
