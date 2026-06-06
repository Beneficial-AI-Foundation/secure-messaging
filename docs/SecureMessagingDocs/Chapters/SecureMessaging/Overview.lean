import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Chapters.SecureMessaging.Defs
import SecureMessagingDocs.Chapters.SecureMessaging.DoubleRatchetAbstract
import SecureMessagingDocs.Chapters.SecureMessaging.DoubleRatchetSignal
import SecureMessagingDocs.Chapters.SecureMessaging.TripleRatchet
import SecureMessagingDocs.Chapters.SecureMessaging.SCKA

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Secure Messaging" =>

*References:*

- {Informal.citet ACD19}[]
- {Informal.citet TR25}[]
- {Informal.citet SCKA25}[]

{include 1 SecureMessagingDocs.Chapters.SecureMessaging.Defs}

{include 1 SecureMessagingDocs.Chapters.SecureMessaging.DoubleRatchetAbstract}

{include 1 SecureMessagingDocs.Chapters.SecureMessaging.DoubleRatchetSignal}

{include 1 SecureMessagingDocs.Chapters.SecureMessaging.TripleRatchet}

{include 1 SecureMessagingDocs.Chapters.SecureMessaging.SCKA}
