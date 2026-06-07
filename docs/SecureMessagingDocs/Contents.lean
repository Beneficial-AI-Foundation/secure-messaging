import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Chapters.AEAD.Defs
import SecureMessagingDocs.Chapters.AEAD.AESGCM
import SecureMessagingDocs.Chapters.AEAD.EncryptThenMAC
import SecureMessagingDocs.Chapters.CKA.Defs
import SecureMessagingDocs.Chapters.CKA.FromDDH
import SecureMessagingDocs.Chapters.CKA.FromKEM
import SecureMessagingDocs.Chapters.CKA.FromLWE
import SecureMessagingDocs.Chapters.ErasureCodes.Defs
import SecureMessagingDocs.Chapters.ErasureCodes.ReedSolomon
import SecureMessagingDocs.Chapters.FSAEAD.Defs
import SecureMessagingDocs.Chapters.FSAEAD.FromAEADPRG
import SecureMessagingDocs.Chapters.OnOffKEM.Defs
import SecureMessagingDocs.Chapters.OnOffKEM.FromMLKEM
import SecureMessagingDocs.Chapters.PRFPRNG.Defs
import SecureMessagingDocs.Chapters.PRFPRNG.FromPRPPRG
import SecureMessagingDocs.Chapters.RKEM.Defs
import SecureMessagingDocs.Chapters.RKEM.FromDDHNonFS
import SecureMessagingDocs.Chapters.RKEM.FromDDHFS
import SecureMessagingDocs.Chapters.RKEM.FromKEM
import SecureMessagingDocs.Chapters.RKEM.KatanaPlain
import SecureMessagingDocs.Chapters.RKEM.KatanaOptimised
import SecureMessagingDocs.Chapters.SCKA.Defs
import SecureMessagingDocs.Chapters.SCKA.UniKEM
import SecureMessagingDocs.Chapters.SCKA.BiKEM
import SecureMessagingDocs.Chapters.SCKA.RKEM
import SecureMessagingDocs.Chapters.SCKA.OppUniKEM
import SecureMessagingDocs.Chapters.SCKA.OppBiKEM
import SecureMessagingDocs.Chapters.SCKA.OppRKEM
import SecureMessagingDocs.Chapters.SecureMessaging.Defs
import SecureMessagingDocs.Chapters.SecureMessaging.DoubleRatchetAbstract
import SecureMessagingDocs.Chapters.SecureMessaging.DoubleRatchetSignal
import SecureMessagingDocs.Chapters.SecureMessaging.TripleRatchet
import SecureMessagingDocs.Chapters.SecureMessaging.SCKA

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Informal

set_option doc.verso true

#doc (Manual) "Secure Messaging — Lean Formalization" =>
%%%
authors := ["Beneficial AI Foundation"]
shortTitle := "Secure Messaging"
%%%

A Lean 4 formalization of secure messaging protocols,
building on the VCVio framework for verified cryptography.

The source code is available on
[GitHub](https://github.com/Beneficial-AI-Foundation/secure-messaging/).

The goal of this project is to provide machine-checked proofs of correctness
and security properties for cryptographic messaging protocols.

# Authenticated Encryption with Associated Data

*References:*

- {Informal.citet ACD19}[]
- {Informal.citet TR25}[]
- {Informal.citet SCKA25}[]

{include 1 SecureMessagingDocs.Chapters.AEAD.Defs}

{include 1 SecureMessagingDocs.Chapters.AEAD.AESGCM}

{include 1 SecureMessagingDocs.Chapters.AEAD.EncryptThenMAC}

# Continuous Key Agreement

*References:*

- {Informal.citet ACD19}[]

{include 1 SecureMessagingDocs.Chapters.CKA.Defs}

{include 1 SecureMessagingDocs.Chapters.CKA.FromDDH}

{include 1 SecureMessagingDocs.Chapters.CKA.FromKEM}

{include 1 SecureMessagingDocs.Chapters.CKA.FromLWE}

# Erasure Codes

*References:*

- {Informal.citet TR25}[]
- {Informal.citet SCKA25}[]

{include 1 SecureMessagingDocs.Chapters.ErasureCodes.Defs}

{include 1 SecureMessagingDocs.Chapters.ErasureCodes.ReedSolomon}

# Forward-Secure AEAD

*References:*

- {Informal.citet ACD19}[]

{include 1 SecureMessagingDocs.Chapters.FSAEAD.Defs}

{include 1 SecureMessagingDocs.Chapters.FSAEAD.FromAEADPRG}

# Online-Offline KEM

*References:*

- {Informal.citet SCKA25}[]

{include 1 SecureMessagingDocs.Chapters.OnOffKEM.Defs}

{include 1 SecureMessagingDocs.Chapters.OnOffKEM.FromMLKEM}

# PRF-PRNG

*References:*

- {Informal.citet ACD19}[]

{include 1 SecureMessagingDocs.Chapters.PRFPRNG.Defs}

{include 1 SecureMessagingDocs.Chapters.PRFPRNG.FromPRPPRG}

# Ratcheting KEM

*References:*

- {Informal.citet TR25}[]

{include 1 SecureMessagingDocs.Chapters.RKEM.Defs}

{include 1 SecureMessagingDocs.Chapters.RKEM.FromDDHNonFS}

{include 1 SecureMessagingDocs.Chapters.RKEM.FromDDHFS}

{include 1 SecureMessagingDocs.Chapters.RKEM.FromKEM}

{include 1 SecureMessagingDocs.Chapters.RKEM.KatanaPlain}

{include 1 SecureMessagingDocs.Chapters.RKEM.KatanaOptimised}

# Sparse Continuous Key Agreement

{include 1 SecureMessagingDocs.Chapters.SCKA.Defs}

{include 1 SecureMessagingDocs.Chapters.SCKA.UniKEM}

{include 1 SecureMessagingDocs.Chapters.SCKA.BiKEM}

{include 1 SecureMessagingDocs.Chapters.SCKA.RKEM}

{include 1 SecureMessagingDocs.Chapters.SCKA.OppUniKEM}

{include 1 SecureMessagingDocs.Chapters.SCKA.OppBiKEM}

{include 1 SecureMessagingDocs.Chapters.SCKA.OppRKEM}

# Secure Messaging

*References:*

- {Informal.citet ACD19}[]
- {Informal.citet TR25}[]
- {Informal.citet SCKA25}[]

{include 1 SecureMessagingDocs.Chapters.SecureMessaging.Defs}

{include 1 SecureMessagingDocs.Chapters.SecureMessaging.DoubleRatchetAbstract}

{include 1 SecureMessagingDocs.Chapters.SecureMessaging.DoubleRatchetSignal}

{include 1 SecureMessagingDocs.Chapters.SecureMessaging.TripleRatchet}

{include 1 SecureMessagingDocs.Chapters.SecureMessaging.SCKA}

{blueprint_bibliography}
