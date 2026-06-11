import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Chapters.CKA.Defs
import SecureMessagingDocs.Chapters.CKA.FromDDH
import SecureMessagingDocs.Chapters.CKA.FromKEM
import SecureMessagingDocs.Chapters.CKA.FromLWE

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true

open Verso.Genre Manual
open Informal

set_option doc.verso true

#doc (Manual) "Continuous Key Agreement" =>

*References:*

- {Informal.citet ACD19}[]
- {Informal.citet TR25}[]

{include 1 SecureMessagingDocs.Chapters.CKA.Defs}

{include 1 SecureMessagingDocs.Chapters.CKA.FromDDH}

{include 1 SecureMessagingDocs.Chapters.CKA.FromKEM}

{include 1 SecureMessagingDocs.Chapters.CKA.FromLWE}

{blueprint_graph}

{blueprint_summary}
