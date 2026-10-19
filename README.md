# SecureMessaging

Formal verification of protocols for secure messaging in Lean 4, built on top of
[VCVio](https://github.com/Verified-zkEVM/VCVio). Currently targeting
cryptographic primitives and protocols from:

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

Blueprint documentation and status: [Secure Messaging](https://beneficial-ai-foundation.github.io/secure-messaging/)

## Preview the documentation locally

From the repository root, build the Verso Blueprint HTML and start a local server:

```sh
rtk proxy env LEAN_NUM_THREADS=4 nice -n 19 lake exe secureMessagingDocs
rtk proxy python3 -m http.server 8000 --bind 127.0.0.1 --directory _out/site/html-multi
```

Open <http://127.0.0.1:8000/>. Use HTTP rather than opening the HTML files directly so
hovers and Blueprint previews work. Stop the server with Ctrl-C. After changing the
documentation, rerun the build command and refresh the browser. `lake build` alone
checks the Lean modules; it does not render the HTML.

## License

Apache-2.0.
