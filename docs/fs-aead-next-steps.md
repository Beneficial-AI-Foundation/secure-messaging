# FS-AEAD: next steps toward Signal verification

Status checked on 2026-09-27. This recommendation targets the ACD19 Double Ratchet
composition; it is not a roadmap for the complete modern Signal implementation.

## Decision and ownership

Prioritize forward-secure AEAD (FS-AEAD), starting with its interface and security
game. This fills a missing component between existing AEAD/CKA work and the
abstract messaging construction.

Publication direction: treat FS-AEAD as a milestone toward a team paper on
computational security of ratchet composition, rather than assume it is a standalone
paper. A later direction is computational SCKA security and SPQR correspondence;
salted-FO/FrodoKEM is a separate track. Impact depends on explicit gains over prior
work, reusable proofs, and connections to concrete protocol behavior and maintained code.

The following issues are open and unassigned. Their comments and parent issues
contain no recorded claims, and no overlapping implementation PR was found:

| Order | Task | Issue |
| --- | --- | --- |
| 1 | Specify FS-AEAD interface | [#186](https://github.com/Beneficial-AI-Foundation/secure-messaging/issues/186) |
| 1 | Specify FS-AEAD security | [#187](https://github.com/Beneficial-AI-Foundation/secure-messaging/issues/187) |
| 2 | Construct FS-AEAD from AEAD and PRG | [#31](https://github.com/Beneficial-AI-Foundation/secure-messaging/issues/31) |
| 3 | Prove construction correctness | [#29](https://github.com/Beneficial-AI-Foundation/secure-messaging/issues/29) |
| 4 | Prove construction security | [#32](https://github.com/Beneficial-AI-Foundation/secure-messaging/issues/32) |

Unpublished work cannot be excluded by checking GitHub. PRF-PRNG is a separate
dependency: its issues are unassigned, but Sergiu Bursuc already contributed its
stubbed definitions in [merged PR #155](https://github.com/Beneficial-AI-Foundation/secure-messaging/pull/155).

## Primary reference and reading order

Alwen, Coretti, Dodis. *The Double Ratchet: Security Notions, Proofs, and
Modularization for the Signal Protocol.* EUROCRYPT 2019.
[ePrint 2018/1037](https://eprint.iacr.org/2018/1037.pdf).
Page numbers below are the paper's printed numbers.

1. **Section 4.2.1, Definitions 14–15 and Figure 5 (pp. 24–26):**
   FS-AEAD interface and security experiment. Model compromise and message
   delivery according to this game, including its asymmetric treatment of
   sender and receiver compromise.
2. **Section 4.2.2 and Figure 6 (pp. 25–27):** construction from AEAD and a PRG.
   Specify chain state, message counters, skipped-key storage, and state rollback
   on failed receive. Include the message index in authenticated data.
3. **Theorem 5 (p. 27):** security reduction, with bound
   `ε ≤ q · (ε_aead + ε_prg)`. The paper sketches the game hops; the Lean proof
   must supply the simulation and invariant details.
4. **Section 5, Figures 8–9:** downstream abstract messaging and Signal
   constructions. Use these to check that the FS-AEAD interface supports its
   intended consumer. The paper also discusses `FS-Stop` and `FS-Max` in §4.2.1,
   but omits formal requirements for those memory-management operations.

The construction in §4.2 uses an ordinary PRG. The separate PRF-PRNG primitive
in §4.3 belongs to the wider messaging composition and should not be conflated
with that PRG dependency.

## What the merged GCM work supplies

- [PR #234](https://github.com/Beneficial-AI-Foundation/secure-messaging/pull/234),
  by `astefano`: GCM construction and correctness, merged 2026-08-03.
- [PR #296](https://github.com/Beneficial-AI-Foundation/secure-messaging/pull/296),
  by `astefano`: one-time GCM security, merged 2026-09-27.
- Main theorem:
  [`GCM.gcmOneTimeAEAD_security`](https://github.com/Beneficial-AI-Foundation/secure-messaging/blob/main/SecureMessaging/AEAD/FromGCM/Security.lean).

This is GCM over an abstract block cipher, not a concrete AES formalization. Its
security theorem covers one encryption per key, a fixed public 96-bit IV, full
128-bit tags, and a fixed valid message length, using the repository's
ACD19-shaped one-time AEAD game. It supplies an AEAD building block; it does not
implement key evolution or prove forward security.

Build FS-AEAD generically over the AEAD interface first. A GCM instantiation can
then reuse these results, with explicit treatment of message-index/AAD encoding
and the concrete scheme's length restrictions.

## Repository entry points

- `SecureMessaging/AEAD/Defs.lean`: existing AEAD interface and game.
- `SecureMessaging/AEAD/FromGCM/Construction.lean`: GCM instance.
- `SecureMessaging/AEAD/FromGCM/Correctness.lean`: GCM correctness.
- `SecureMessaging/AEAD/FromGCM/Security.lean`: merged security entry point on
  remote `main`; absent from the inspected local Frodo branch.
- `docs/SecureMessagingDocs/Chapters/FSAEAD/Defs.lean`: blueprint placeholders.
- `docs/SecureMessagingDocs/Chapters/FSAEAD/FromAEADPRG.lean`: construction and
  proof placeholders.

Downstream milestones are [#124](https://github.com/Beneficial-AI-Foundation/secure-messaging/issues/124)
(abstract Double Ratchet construction), then
[#129](https://github.com/Beneficial-AI-Foundation/secure-messaging/issues/129)
(Signal specialization), together with their correctness/security tasks.

## Separate reference: CKA from LWE

ACD19 **§4.1.2, pp. 23–24**, gives the construction; **Theorem 4** gives its
security reduction; **Appendix C.2, p. 55**, describes the underlying Frodo and
reconciliation operations. This uses the original reconciliation-based Frodo
from Bos et al., *Frodo: Take off the Ring!* (CCS 2016), rather than the modern
FrodoKEM construction currently specified in this repository. It is a separate
instantiation project, not a prerequisite for the FS-AEAD milestone.

## Connecting the paper models to deployed Signal

Add Galois's [Signal Protocols, Annotated: Triple Ratchet high-level description](https://galoisinc.github.io/libsignal-docs-and-models/Signal-Protocols-Annotated/Triple-Ratchet-___-Description-___-Code/High-Level-Description/)
to the reference map. It explains the transition from PQXDH session establishment
to Double Ratchet plus SPQR/ML-KEM Braid, and links the initial states to concrete
Rust code. The inspected page pins libsignal links to commit
`57d41c877d5a55d881fb3f52d9b16900118ee29b` and SPQR links to
`f2589fef855c10f39d72634dab3d14654dd410bf`.

Use three complementary sources when targeting the implementation:

1. ACD19, TR25, and SCKA25 for mathematical constructions and security claims.
2. Signal's [Double Ratchet](https://signal.org/docs/specifications/doubleratchet/),
   [ML-KEM Braid](https://signal.org/docs/specifications/mlkembraid/), and
   [PQXDH](https://signal.org/docs/specifications/pqxdh/) specifications for
   concrete protocol behavior.
3. Galois's annotations and the pinned source code for the specification-to-code
   correspondence that the verification must establish.

The FS-AEAD recommendation addresses the ACD19 composition milestone. It does
not by itself establish correspondence with libsignal. For that broader goal,
track initialization, key derivation, state transitions, erasure, and error
behavior across the paper model, Signal specification, and pinned implementation.
