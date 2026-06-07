import VersoManual

open Verso.Genre Manual

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

# Chapters

- Authenticated Encryption with Associated Data

- Continuous Key Agreement

- Erasure Codes

- Forward-Secure Authenticated Encryption with Associated Data

- On-Off Key Encapsulation Mechanisms

- Pseudorandom Functions and Pseudorandom Generators

- Ratcheted Key Encapsulation Mechanisms

- Signal Continuous Key Agreement

- Secure Messaging Protocols
