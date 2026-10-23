# Signal verification references

## Research direction

Prioritize FS-AEAD as a milestone toward a team paper on computational security
of modular ratchet composition; then consider SCKA/ML-KEM Braid and SPQR correspondence.
Keep reusable salted-FO/FrodoKEM security as a separate cryptographic-verification track.
The strongest impact would come from closing an explicit assurance gap, connecting
proofs to maintained code, or providing reusable methods; “first in Lean” alone is a weaker claim.
Likely audiences: cryptography, formal methods, and secure-messaging engineering.

## Protocol papers
- [Double Ratchet (ACD19)](https://eprint.iacr.org/2018/1037) — CKA, FS-AEAD (§4.2), PRF-PRNG, messaging composition.
- [Triple Ratchet (2025)](https://eprint.iacr.org/2025/078) — hybrid security and RKEM.
- [SCKA (2025)](https://eprint.iacr.org/2025/2267) — bandwidth-constrained post-quantum messaging.

## Signal specifications and implementation mapping
- [Double Ratchet, SPQR, and Triple Ratchet](https://signal.org/docs/specifications/doubleratchet/)
- [ML-KEM Braid](https://signal.org/docs/specifications/mlkembraid/)
- [PQXDH](https://signal.org/docs/specifications/pqxdh/)
- [Galois: Signal Protocols, Annotated](https://galoisinc.github.io/libsignal-docs-and-models/Signal-Protocols-Annotated/Triple-Ratchet-___-Description-___-Code/High-Level-Description/) — specification-to-code links.
- [libsignal](https://github.com/signalapp/libsignal) · [SPQR implementation](https://github.com/signalapp/SparsePostQuantumRatchet)

## Component references (as required by the chosen instantiation)
- [ML-KEM: FIPS 203](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.203.pdf)
- [FrodoKEM paper](https://cic.iacr.org/p/2/3/25) · [FrodoKEM draft-03](https://datatracker.ietf.org/doc/html/draft-longa-cfrg-frodokem-03) — original reconciliation-based Frodo for CKA: ACD19 Appendix C.2.
- [GCM: SP 800-38D](https://csrc.nist.gov/pubs/sp/800/38/d/final) · [AES: FIPS 197](https://doi.org/10.6028/NIST.FIPS.197-upd1)
- [HKDF: RFC 5869](https://www.rfc-editor.org/rfc/rfc5869) · [HMAC: RFC 2104](https://www.rfc-editor.org/rfc/rfc2104)
- [SHA-2: FIPS 180-4](https://doi.org/10.6028/NIST.FIPS.180-4) · [SHA-3/SHAKE: FIPS 202](https://doi.org/10.6028/NIST.FIPS.202)
- [X25519/X448: RFC 7748](https://www.rfc-editor.org/rfc/rfc7748)
- [Reed–Solomon (1960)](https://doi.org/10.1137/0108018) · [Reed–Solomon FEC: RFC 5510](https://www.rfc-editor.org/rfc/rfc5510)
- [Authenticated-encryption composition (BN00)](https://eprint.iacr.org/2000/025) · [AEAD (Rogaway 2002)](https://web.cs.ucdavis.edu/~rogaway/papers/ad.pdf) · [Generic composition (NRS14)](https://eprint.iacr.org/2013/765)

For implementation verification, pin specification revisions and source commits.

## FrodoKEM security: focused reading
- [FrodoKEM design paper](https://cic.iacr.org/p/2/3/25/pdf) — §7.1.1/Theorem 1 and Appendix C.1 for classical-ROM CCA security; C.1.3–C.1.4 for matrix generation and PKE-to-LWE reduction.
- [Formally Verified Correctness Bounds (CCS 2025)](https://cryptojedi.org/papers/frodoec-20250831.pdf) — §4.1, Theorems 4.1–4.2: machine-checked Matrix-LWE reduction and FrodoPKE IND-CPA security; §4.2 and §5: correctness/failure bounds. Not a full KEM CCA proof.
- [On The Multi-target Security of Post-Quantum KEMs](https://eprint.iacr.org/2025/343) — salted FO: §3 construction, §4 ROM, §5 QROM (May 2026 revision; earlier title: Tight Multi-challenge Security Reductions for Key Encapsulation Mechanisms).
- [A Modular Analysis of the Fujisaki–Okamoto Transformation (HHK17)](https://eprint.iacr.org/2017/604) — foundational FO proof decomposition with correctness errors; use the revision with errata.
