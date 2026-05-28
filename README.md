# SecureMessaging

Formal verification of protocols for secure messaging in Lean 4, built on top of
[VCVio](https://github.com/Verified-zkEVM/VCV-io). Currently targeting cryptographic primitives and protocols from:

- Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf

- Dodis, Jost, Katsumata, Prest, Schmidt.
  *Triple Ratchet: A Bandwidth Efficient Hybrid-Secure Signal Protocol.*
  EUROCRYPT 2025, https://eprint.iacr.org/2025/078.pdf

- Auerbach, Dodis, Jost, Katsumata, Schmidt.
  *How to Compare Bandwidth Constrained Two-Party Secure Messaging Protocols:
  A Quest for A More Efficient and Secure Post-Quantum Protocol.*
  USENIX Security 2025, https://eprint.iacr.org/2025/2267.pdf

The intended downstream consumer is a future Lean formalization of
[libsignal](https://github.com/signalapp/libsignal), Signal's secure-messaging
stack, which centers on the Double Ratchet and now also ships post-quantum
components (e.g. SPQR, the PQ algorithm above).

## Documentation

A Verso/Blueprint documentation site lives in [`docs/`](docs/). It is built as
a separate Lake package and currently scaffolds the shared VCV-io math
prerequisites that every protocol chapter in this library reuses. See
[`docs/README.md`](docs/README.md) for build and render instructions.

## License

Apache-2.0.
