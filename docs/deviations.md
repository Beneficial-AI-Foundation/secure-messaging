# Deviations from ACD19 in the AEAD and FS-AEAD formalization

This catalogue lists every place where the Lean formalization of AEAD and FS-AEAD differs from
ACD19 (Alwen, Coretti, Dodis, "The Double Ratchet: Security Notions, Proofs, and Modularization
for the Signal Protocol", EUROCRYPT 2019, ePrint 2018/1037). For AEAD, it covers Figure 1 and Definitions 1 and 2. For
FS-AEAD, it covers Definitions 14 and 15, Figures 5 and 6, and Theorem 5. There is one entry for
each ID.

The format follows the deviation catalogue of Google DeepMind's
[code-verification](https://github.com/google-deepmind/code-verification) repository,
[`Computational/docs/DEVIATIONS.md`](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/Computational/docs/DEVIATIONS.md)
at commit `8c8d371f`. That repository also proves ACD19 Theorem 5 in Lean with VCVio. Each entry
names the matching GDM ID, so that you can compare the two formalizations. A GDM ID always has the
prefix "GDM", because the two catalogues number their entries independently: our DEV-FS1 is not
GDM DEV-FS1.

Abbreviations: AD = associated data. PRG = pseudorandom generator. OT-CCA = one-time
chosen-ciphertext security (ACD19 Definition 2). Kli21 = Klimović, "Modular Design of the Messaging
Layer Security (MLS) Protocol", Master's thesis, ETH Zürich, 2021, Appendix A.1. Ros26 = Rosulek,
"The Joy of Cryptography", 2026, Definition 9.6.5. `q` = number of calls of `O-Transmit-A` and
`O-Chall-A` together. `N` = largest index of an injection. `L = max q N`.

## How to read an entry

- ID: `DEV-AEAD<n>` for ACD19 Figure 1 and Definitions 1 and 2, `DEV-FS<n>` for ACD19 §4.2
  (Definitions 14 and 15, Figures 5 and 6, Theorem 5). IDs are never reused or renumbered. A
  new entry gets the next free number. `git grep -n DEV-FS3` finds the Lean home of DEV-FS3.
- Class:
  - `paper fix`: a gap or an error in ACD19 that we had to repair. The entry gives the attack or
    the counterexample.
  - `formalization`: the same idea, stated in another form.
  - `convention`: a choice where ACD19 is clear, but where we follow the convention of this
    project.
  - `ambiguity resolved`: ACD19 allows more than one reading, and we pick one.
- Effect on the result:
  - `none`: the result means the same as in ACD19.
  - `constants`: the bound has other factors or other terms.
  - `restricts the adversary`: the Lean game refuses something that ACD19 allows, so the result is
    weaker. No entry in this catalogue has this effect.
  - `extends`: the Lean covers more than ACD19. For an assumption game (OT-CCA), a stronger
    adversary means a stronger assumption.
- Home: the Lean declaration or the module header whose text holds the precise statement. This
  catalogue summarizes that text.

## Read these first

These entries change what Theorem 5 (`FSAEADScheme.advantage_fromAEADPRG_le`) says, compared with
ACD19 Theorem 5.

| ID | In one line | Effect |
|---|---|---|
| [DEV-AEAD1](#dev-aead1) | the AEAD game refuses only the challenge pair `(a*, e*)`. This is a stronger assumption than Figure 1, but Theorem 5 is false with Figure 1 | extends |
| [DEV-FS16](#dev-fs16) | the bound sums over `L = max q N` chain positions, not `q` | constants |
| [DEV-FS17](#dev-fs17) | the bound is `2L · (ε_prg + ε_aead)` with the FS-AEAD advantage `\|Pr - 1/2\|` | constants |
| [DEV-FS19](#dev-fs19) | running time is not modelled, and the reductions sample up to `L` chain steps (open finding C7-1) | none on the inequality |
| [DEV-FS10](#dev-fs10) | `FS-Stop` and `FS-Max` are not modelled | none |

## Counts

| Layer | paper fix | formalization | convention | ambiguity resolved | total |
|---|---:|---:|---:|---:|---:|
| AEAD | 2 | 1 | 0 | 0 | 3 |
| FS | 6 | 8 | 2 | 3 | 19 |
| total | 8 | 9 | 2 | 3 | 22 |

## AEAD: one-time IND-CCA security (ACD19 Definitions 1 and 2, Figure 1)

Homes: `SecureMessaging/AEAD/Defs.lean` and `SecureMessaging/FSAEAD/FromAEADPRG/Security.lean`.
The Lean header of `AEAD/Defs.lean` calls DEV-AEAD1 and DEV-AEAD2 "D1" and "D2".

### DEV-AEAD1

**Decryption refuses only the challenge pair `(a*, e*)`** · class: paper fix · effect: extends
(a stronger assumption than Figure 1)

- Home: the module header of `SecureMessaging/AEAD/Defs.lean`, item (D1), and
  `AEADScheme.oracleDecrypt`.
- Figure 1 refuses every query `decrypt(a, e*)`, for every `a`. Let `AE` be secure in Figure 1,
  and let `AE'` ignore the AD (it always uses a fixed AD `ā`). Then `AE'` is also secure in
  Figure 1. Figure 6 built
  on `AE'` loses Figure 5: the adversary injects the honest ciphertext with another AD before
  delivery, and B accepts it at an uncompromised index. This contradicts ACD19 Theorem 5 as
  printed.
- With the guard on the pair, `AE'` is insecure. The adversary asks `decrypt(a', e*)` with
  `a' ≠ a`. For `b = 0`, the answer is `m`. For `b = 1`, it is `⊥`. NRS14, Boneh and Shoup
  (Definition 9.10) and Ros26 use the same guard.
- GDM: DEV-AEAD1, the same guard, classed as formalization and without the counterexample.

### DEV-AEAD2

**For `b = 1`, the challenge `e*` is uniform among the ciphertexts of length `clen |m|`** ·
class: paper fix · effect: none for one ciphertext length

- Home: the module header of `SecureMessaging/AEAD/Defs.lean`, item (D2), and
  `AEADScheme.oracleEncrypt`.
- Figure 1 samples `e* ←$ C`. If `C` holds ciphertexts of several lengths, the length of `e*` can
  reveal `b`, because a real ciphertext has length `clen |m|`. This is the sample `C ↞ Σ.C(|M|)` of
  Ros26. For a ciphertext type with one length, the two games are the same
  (`LenSampleable.unifOfLen_const_prod`).
- GDM: no counterpart. GDM DEV-FS17 changes the same line for another reason: its ideal ciphertext
  can depend on the AD, for libsignal's public header.

### DEV-AEAD3

**The AEAD key comes from `keygen`, and Theorem 5 assumes that `keygen` is uniform** · class:
formalization · effect: none

- Home: `FSAEADScheme.advantage_fromAEADPRG_le`, hypothesis `hkg`.
- Figure 1 samples `K ←$ K`. `AEADScheme` has a field `keygen`, and `AEADScheme.securityExp`
  runs it. In Figure 6, the PRG outputs the AEAD keys, so Theorem 5 takes
  `hkg : ae.keygen =ᵈ $ᵗ Kae`, which gives back the sample of Figure 1.
- GDM: no counterpart.

## FS: forward-secure AEAD (ACD19 §4.2, Figures 5 and 6, Theorem 5)

Homes: `SecureMessaging/FSAEAD/Defs.lean` (DEV-FS1 to DEV-FS10),
`SecureMessaging/FSAEAD/FromAEADPRG/Construction.lean` (DEV-FS11 to DEV-FS15) and
`SecureMessaging/FSAEAD/FromAEADPRG/Security.lean` (DEV-FS16 to DEV-FS19). In the module header of
`Construction.lean`, DEV-FS11 and DEV-FS12 are "corrections 1 and 2".

### DEV-FS1

**`FS-Rcv` returns `none` on rejection** · class: paper fix · effect: none (repairs the game)

- Home: the module header of `SecureMessaging/FSAEAD/Defs.lean`, `[CORRECTIONS TO ACD19]`, and
  `FSAEADScheme.rcv`.
- Definition 14 does not say what `FS-Rcv` outputs on rejection. Suppose that a rejection
  returns an index `i`. Then `O-Inject-B` runs `delete(i)`. The adversary injects a junk
  ciphertext that B rejects, and so erases the record of an honest ciphertext in transit (Kli21). With `none`,
  `O-Inject-B` stops at `req r ≠ ⊥` and deletes nothing.
- GDM: DEV-FS3 (in part: `FS-Rcv` errors leave `v_B` unchanged), without the attack.

### DEV-FS2

**After the first `O-Corr-A`, every index that A has not sent is compromised** · class: paper
fix · effect: none (repairs the game)

- Home: the module header of `SecureMessaging/FSAEAD/Defs.lean`, `[CORRECTIONS TO ACD19]`,
  change 1, and `FSAEADScheme.oracleCorrA`.
- After `O-Corr-A` at counter `i_A^c`, the adversary knows A's state. It computes the ciphertext
  that A will send at an index `i > i_A^c` and injects it first. B must accept it. In Figure 5,
  `comp` holds only the indices that A sent, so this counts as a forgery and every correct scheme
  loses (Kli21). `record` no longer adds to `comp`.
- GDM: DEV-FS1, the same idea.

### DEV-FS3

**A send at an index that an injection consumed is not recorded** · class: paper fix · effect:
none (repairs the game)

- Home: the module header of `SecureMessaging/FSAEAD/Defs.lean`, `[CORRECTIONS TO ACD19]`,
  change 2, and `FSAEADScheme.GameState.record`.
- This completes DEV-FS2. If A is corrupted and an injection already consumed index `i_A`, B
  already moved past `i_A`, so a later honest ciphertext at `i_A` can fail. `record` then does
  nothing. Every other send is recorded, also at a compromised index, so correctness is still
  checked there.
- GDM: DEV-FS2 drops the correctness check on every compromised index. Our rule drops it only at
  an index that an injection consumed.

### DEV-FS4

**`O-Deliver-B` counts a rejected honest ciphertext as a win** · class: convention · effect: none

- Home: the module header of `SecureMessaging/FSAEAD/Defs.lean`, `[CONVENTIONS]`, and
  `FSAEADScheme.oracleDeliverB`.
- If B's output `(i', m')` differs from the record `(i, m)`, Figure 5 sets `win`. On rejection,
  there is no output to compare. We read `⊥` as an output that differs from every `(i, m)`.
- GDM: no counterpart.

### DEV-FS5

**The FS-AEAD advantage is `|Pr[A wins] - 1/2|`** · class: convention · effect: constants
(a factor 2)

- Home: the module header of `SecureMessaging/FSAEAD/Defs.lean`, `[CONVENTIONS]`, and
  `FSAEADScheme.advantage`.
- ACD19 §2.1 defines the advantage as `2 · |Pr[A wins] - 1/2|`. Our value is half of that, as for
  the guess advantages of this project (`AEADScheme.guessAdvantage`, CKA, SCKA). The AEAD terms of
  Theorem 5 use `AEADScheme.distAdvantage`, which is twice the guess advantage and equal to the
  ACD19 value. See DEV-FS17.
- GDM: DEV-FS13 uses the ACD19 value.

### DEV-FS6

**`O-Deliver-B` uses the in-transit record with the smallest index** · class: ambiguity resolved
· effect: none

- Home: `FSAEADScheme.GameState.findTrans`.
- Figure 5 takes a record `(i, a, m, e) ∈ trans` "for some `i, m`". If several records have the
  same `(a, e)`, we take the one with the smallest index. For Figure 6, the index is part of the
  ciphertext, so the record is unique.
- GDM: DEV-FS21 takes the most recent record.

### DEV-FS7

**`delete(i)` for a sent index with no record changes nothing** · class: ambiguity resolved ·
effect: none

- Home: the module header of `SecureMessaging/FSAEAD/Defs.lean`, `[AMBIGUITIES RESOLVED]`, and
  `FSAEADScheme.GameState.delete`.
- GDM: no counterpart.

### DEV-FS8

**The §2.1 keywords and the randomness oracle are encoded in the game state** · class:
formalization · effect: none

- Home: the module header of `SecureMessaging/FSAEAD/Defs.lean`, `[ENCODING OF FIGURE 5]`.
- `win` and `end` are Boolean flags. `req` is an `if … then return none` at the start of the
  oracle, before any change to the state. `end` sets `end_`, which every oracle checks first. The
  experiment returns `win || b == b'`. The adversary also has a uniform-randomness oracle, as in
  the AEAD game.
- GDM: DEV-FS3, for `req` and `end`.

### DEV-FS9

**The FS-AEAD correctness game adapts the SM correctness game of ACD19 §3.3** · class:
formalization · effect: none

- Home: `FSAEADScheme.correctnessExp` and `FSAEADScheme.oracleInjectBCorr`.
- The game has the oracles of Figure 5 without `O-Chall-A`. `O-Inject-B^corr` accepts only an
  injection at a compromised index and never sets `win`. Only `O-Deliver-B` sets `win`. Theorem 5
  does not use this game.
- GDM: no counterpart. GDM DEV-FS5 limits correctness to libsignal's skip window. Our correctness
  game has no window.

### DEV-FS10

**`FS-Stop` and `FS-Max` are not modelled** · class: formalization · effect: none

- Home: `FSAEADScheme`.
- ACD19 Definition 14 also has `FS-Stop` and `FS-Max`, which erase old skipped keys and have no
  formal requirement. `FSAEADScheme` has only the four algorithms `initS`, `initR`, `send` and
  `rcv`. The dictionary `D` of Figure 6 keeps every skipped key (DEV-FS13).
- GDM: DEV-FS11, the same.

### DEV-FS11

**`skip` stores each skipped key at its own index, `D[i_B] ← K`** · class: paper fix · effect:
none (repairs the scheme)

- Home: the module header of `SecureMessaging/FSAEAD/FromAEADPRG/Construction.lean`,
  `[CORRECTIONS TO ACD19]` item 1, and `FSAEADScheme.FromAEADPRG.skipSteps`.
- Figure 6 writes `D[u] ← K`. Each skipped key then overwrites the one before at the target index
  `u`. When the message of a skipped key arrives later, B cannot find the key, and out-of-order
  delivery fails correctness.
- GDM: DEV-FS7, the same.

### DEV-FS12

**`FS-Rcv` rejects an old index that is not in `D`** · class: paper fix · effect: none (repairs
the scheme)

- Home: the module header of `SecureMessaging/FSAEAD/FromAEADPRG/Construction.lean`,
  `[CORRECTIONS TO ACD19]` item 2, and `FSAEADScheme.FromAEADPRG.rcvKey`.
- Figure 6 handles `(i, e)` with `D[i] = ⊥` and `i ≤ i_B` as a new index: it derives the next key
  under the name `i` and sets `i_B ← i`. Attack: A sends one message, B receives it, and
  `O-Corr-A` reveals `w₁`. The adversary computes `(w₂, K₂) ← G(w₁)` and injects
  `(0, Enc(K₂, (0, a), m))`. B accepts it at index 0, which is not in `comp`, so the adversary
  wins. The repair also rejects index 0 in the initial state.
- GDM: DEV-FS8, the same rule, without this attack.

### DEV-FS13

**`D` starts as `⊥` everywhere and is a logical dictionary** · class: ambiguity resolved ·
effect: none

- Home: the module header of `SecureMessaging/FSAEAD/FromAEADPRG/Construction.lean`,
  `[AMBIGUITIES RESOLVED]`.
- Figure 6 initializes `D[·] ← λ`, but `try-skipped` and `FS-Rcv` test for `⊥`. We write `⊥` for
  both. `D` does not model the physical erasure of keys or a bound on the storage.
- GDM: no counterpart.

### DEV-FS14

**`error` is `none`, and `skip` is a recursion** · class: formalization · effect: none

- Home: the module header of `SecureMessaging/FSAEAD/FromAEADPRG/Construction.lean`,
  `[ENCODING OF FIGURE 6]`.
- ACD19 says that `error` rolls B's state back to the state before the call. With `none` there is
  no new state, so the caller keeps the old one. This also undoes the `D[i] ← ⊥` of
  `try-skipped`. `skip(u)` runs `u - 1 - i_B` steps by recursion (`skipSteps`), not by a `while`
  loop.
- GDM: DEV-FS3, in part.

### DEV-FS15

**The algorithms take a position-indexed generator `G : ℕ → W → W × Kae`** · class:
formalization · effect: none

- Home: the module header of `SecureMessaging/FSAEAD/FromAEADPRG/Construction.lean`,
  `[NOTATION]`, and `FSAEADScheme.fromAEADChain`.
- `fromAEADChain ae G` uses `G i` at chain position `i`. The security proof replaces some `G i` by
  uniform values. Theorem 5 is about `fromAEADPRG ae prg`, which uses one PRG at every position,
  as in Figure 6.
- GDM: DEV-FS10. There the scheme of the theorem takes the family.

### DEV-FS16

**The bound sums over `L = max q N` chain positions, not `q`** · class: paper fix · effect:
constants

- Home: the module header of `SecureMessaging/FSAEAD/FromAEADPRG/Security.lean` and
  `FSAEADScheme.advantage_fromAEADPRG_le` (hypotheses `SendQueryBound` and `InjectIndexBound`).
- ACD19 Theorem 5 has `q` terms. Figure 6 does not bound skipping, so B derives a key at any index
  that an injection names, and a forgery can land at an index above `q`. Our hybrids cover every
  index up to `L`. If the adversary injects only at indices up to `q`, then `L = q`. `N` is a
  parameter of the bound, not a restriction of the game.
- GDM: DEV-FS9 and DEV-FS12. GDM bounds skipping by libsignal's `maxSkip` (25,000) and sums over
  `(q + 1)(maxSkip + 1)` positions.

### DEV-FS17

**The bound is `2L · (ε_prg + ε_aead)`** · class: formalization · effect: constants

- Home: the module header of `SecureMessaging/FSAEAD/FromAEADPRG/Security.lean` and
  `FSAEADScheme.advantage_fromAEADPRG_le_of_le`.
- ACD19 states `q · (ε_aead + ε_prg)`. The factor 2 comes from the separate arguments for
  authenticity (Step 3) and confidentiality (Step 4). `L` replaces `q` (DEV-FS16). The FS-AEAD
  advantage is half of the ACD19 value (DEV-FS5), and the PRG and AEAD advantages are
  distinguishing advantages, as in ACD19. In the ACD19 convention for both sides, the bound is
  `4L · (ε_prg + ε_aead)`.
- GDM: DEV-FS13 (a factor 2 from the ACD19 advantage) and DEV-FS14 (a second hybrid chain, which
  doubles the steps).

### DEV-FS18

**Named reductions instead of "for all `t'`-attackers"** · class: formalization · effect: none

- Home: `FSAEADScheme.advantage_fromAEADPRG_le`.
- The bound names the reductions `prgRed`, `aeadRed`, `confPrgRed` and `confAeadRed`, which are
  built from the adversary. ACD19 bounds the advantage by the best advantage of any attacker with
  run time `t'`.
- GDM: DEV-FS15, the same.

### DEV-FS19

**Running time is not modelled** · class: formalization · effect: none on the inequality

- Home: the module header of `SecureMessaging/FSAEAD/FromAEADPRG/Security.lean`.
- The bound holds for every adversary, but it says nothing about the run time of the reductions
  (DEV-FS18). A reader checks their efficiency by reading their definitions. Each reduction
  samples up to `L` chain steps (`sampleTab`). If `N` is far above the run time of the adversary,
  the reductions are slower than the adversary. This is open finding C7-1 of the review of PR 421.
- GDM: DEV-FS15 and GDM DEV-SM18 (efficiency checked by reading).

## GDM entries with no deviation here

These GDM FS entries have no entry in this catalogue, because our formalization follows ACD19 at
that point, or because the entry is about libsignal.

| GDM ID | GDM rule | Here |
|---|---|---|
| DEV-FS4 | `\|m₀\| = \|m₁\|` is not checked, one message length | `O-Chall-A` checks `len m₀ = len m₁`, as in Figure 5 |
| DEV-FS5, DEV-FS9 | correctness and skipping only inside `maxSkip` | skipping without a bound, as in Figure 6 (DEV-FS16 gives the cost) |
| DEV-FS6 | `O-Corr-B` also waits until no uncompromised record is in transit | `O-Corr-B` requires only `chall = ∅`, as in Figure 5 |
| DEV-FS16 | perfect AEAD correctness is a hypothesis | Theorem 5 takes `ae.Correct`, as ACD19 Definition 1 requires |
| DEV-FS17 to DEV-FS20 | libsignal's public header, AD classes and epochs | not modelled: this formalization is of ACD19, not of libsignal |
