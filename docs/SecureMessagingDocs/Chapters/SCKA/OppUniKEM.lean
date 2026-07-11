import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
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

::::definition "opp_unikem_cka_spec" (parent := "cka_protocols_opp_unikem_cka") (lean := "oppUniKemCKA.scheme")
```anchor initAlgorithms (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def initKeyGen : m Unit := pure ()

def initA (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
		(_ik : Unit) : m (StA onoff Sym) :=
	pure { dkA := none, ekA := none, ct0 := none, t := 1, ich := 0, lch := ∅,
				 ack := { ekRec := false, ctRec := false } }

def initB (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
		(_ik : Unit) : m (StB onoff Sym) :=
	pure { ekA := none, ct0 := none, ct1 := none, stCt := none, t := 1, ich := 0,
				 lch := ∅, ack := { ekRec := false, ctRec := false } }
```

```anchor sendA (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def sendA (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
	(ecEk : ErasureCodePayload PK Sym) (stA : StA onoff Sym) :
		m (Option (Option (ℕ × K) × Message Sym × ℕ × StA onoff Sym)) := do
```

```anchor sendArleak (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def sendArleak (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
		(ecEk : ErasureCodePayload PK Sym)
	(leak : KEMScheme.OnOffRandLeak kem onoff) (stA : StA onoff Sym) :
	m (Option (Option (ℕ × K) × Message Sym × ℕ × StA onoff Sym ×
		SendRand leak.KeygenRand leak.OffRand leak.OnRand)) := do
```

```anchor recvA (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def recvA (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
		[DecidableEq Sym]
	(hDet : kem.DeterministicDecaps)
		(ecCt0 : ErasureCodePayload onoff.C₀ Sym)
		(ecCt1 : ErasureCodePayload onoff.C₁ Sym)
	(stA : StA onoff Sym) (ρ : Message Sym) :
		Option (Option (ℕ × K) × ℕ × StA onoff Sym) :=
```

```anchor sendB (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def sendB (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
		(ecCt0 : ErasureCodePayload onoff.C₀ Sym)
		(ecCt1 : ErasureCodePayload onoff.C₁ Sym) (stB : StB onoff Sym) :
		m (Option (Option (ℕ × K) × Message Sym × ℕ × StB onoff Sym)) := do
```

```anchor sendBrleak (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def sendBrleak (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
		(ecCt0 : ErasureCodePayload onoff.C₀ Sym)
		(ecCt1 : ErasureCodePayload onoff.C₁ Sym)
		(leak : KEMScheme.OnOffRandLeak kem onoff) (stB : StB onoff Sym) :
		m (Option (Option (ℕ × K) × Message Sym × ℕ × StB onoff Sym ×
			SendRand leak.KeygenRand leak.OffRand leak.OnRand)) :=
	do
```

```anchor recvB (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def recvB (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
		[DecidableEq Sym]
		(ecEk : ErasureCodePayload PK Sym) (stB : StB onoff Sym) (ρ : Message Sym) :
		Option (Option (ℕ × K) × ℕ × StB onoff Sym) :=
```

```anchor vulnerableStates (project := ".") (module := SecureMessaging.SCKA.OppUniKEM.Construction)
def vulnA (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
		(stA : StA onoff Sym) : Finset ℕ :=
	if stA.dkA.isSome then {stA.t} else ∅

def vulnB (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
		(stB : StB onoff Sym) : Finset ℕ :=
	if stB.stCt.isSome then {stB.t} else ∅
```

{usesLabel}`uses` {uses "scka_scheme"}[] · {uses "erasure_code_scheme"}[] · {uses "on_off_kem_scheme"}[] · {uses "on_off_kem_rand_leak"}[] · {githubLabel}`github` {githubIssue 106}[]
::::

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
