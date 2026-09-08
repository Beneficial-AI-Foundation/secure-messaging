# Deferred items — Phase 02

Out-of-scope discoveries logged during execution. Not fixed here.

- 2026-09-08 (02-02): pre-existing flexible-simp linter warnings in
  `SecureMessaging/SCKA/OppUniKEM/Correctness/Invariant/RecvB.lean` (lines ~393, 411, 413)
  surface on full `lake build` replay. File last touched in the Lean 4.32 update (#273),
  unrelated to the GCM games. Candidate for the batch `simp?` harvest playbook.
- Pre-existing `sorry`s in `SecureMessaging/PRP/Defs.lean` (lines 73, 85) — known: the PRP
  game is deliberately sorried until the PRP/PRF switching work (see roadmap).
