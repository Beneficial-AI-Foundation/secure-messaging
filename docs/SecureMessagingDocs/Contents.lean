import VersoManual
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SecureMessaging.AEAD.Defs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Secure Messaging — Lean Formalization" =>
%%%
authors := ["Beneficial AI Foundation"]
shortTitle := "Secure Messaging"
%%%

A Lean 4 formalization of secure messaging protocols,
building on the VCVio framework for verified cryptography.

The source code is available on
[GitHub](https://github.com/Beneficial-AI-Foundation/secure-messaging/).

# Overview

The goal of this project is to provide machine-checked proofs of correctness
and security properties for cryptographic messaging protocols.

{blueprint_graph}

{blueprint_summary}

# Authenticated Encryption with Associated Data

An AEAD scheme provides both confidentiality and integrity for messages,
with additional unencrypted associated data authenticated alongside the ciphertext.
The formalization follows Definition 1 of \[ACD19\].

{docstring AEADScheme}

{docstring AEADScheme.Correct}

{docstring AEADScheme.securityExp}
