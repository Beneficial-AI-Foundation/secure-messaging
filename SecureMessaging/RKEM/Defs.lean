/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.ProbCompLift
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Ratcheting Key Encapsulation Mechanism (RKEM)

The forward-secure ratcheting KEM of [TripleRatchet, Def. 5.1], the main building
block used there to generically construct a CKA (compare `CKAScheme`).

An RKEM is a two-party protocol, with parties `A` and `B` exchanging encapsulation
keys and ciphertexts in a ping-pong manner. Unlike a plain KEM, a ciphertext
depends not only on the encapsulation key received in the previous round, but
also on the fresh decapsulation key held for the current round: running
encapsulation/decapsulation *ratchets*, producing an updated key for the next
round alongside the shared key.

[SPACES]
- `Par`: public-parameter space, sampled once by `rsetup` and shared as an
  input to every other algorithm.
- `EK`, `DK`: encapsulation- and decapsulation-key spaces. Definition 5.1 lets
  the "fresh" and "updated" ratcheting key spaces `RKP`/`RK̂P` differ; we use a
  single pair of spaces covering both, with `rkeygenAFresh`/`rkeygenAUpdated` (resp.
  `B`) selecting the distribution, exactly as in the paper's own shorthand
  `D_RKeyGen-P`/`D̂_RKeyGen-P`.
- `CT`: ciphertext space.
- `K`: shared-key space.

[ALGORITHMS]
- `rsetup : m Par`.
  `RSetup(1^λ) → par`: samples the public parameter shared by both parties.
- `rkeygenAFresh : Par → m (EK × DK)`, `rkeygenBFresh : Par → m (EK × DK)`.
  `RKeyGen-P(par, ⊥) → (ekP, dkP)`: samples a fresh encapsulation/decapsulation
  key pair for party `P`.
- `rkeygenAUpdated : Par → m (EK × DK)`, `rkeygenBUpdated : Par → m (EK × DK)`.
  `RKeyGen-P(par, updated) → (ekP, dkP)`: samples a key pair for `P` with the
  distribution of an *updated* key, i.e. one as could arise from `rencP`/`rdecP`.
  Used to state correctness/security, and in the setup of some constructions
  (Definition 5.1, footnote 12).
- `rencA : Par → EK → DK → m (CT × K × DK)`.
  `REnc-A(par, ekB, dkA) → (ctB, K, dk̂A)`: encapsulates towards `B`'s
  encapsulation key `ekB` using `A`'s decapsulation key `dkA`, producing a
  ciphertext `ctB` for `B`, the shared key `K`, and `A`'s updated decapsulation
  key `dk̂A`.
- `rdecA : Par → DK → CT → EK → m (K × EK)`.
  `RDec-A(par, dkA, ctA, ekB) → (K, ek̂B)`: decapsulates `ctA` using `A`'s
  decapsulation key `dkA` and `B`'s encapsulation key `ekB`, producing the
  shared key `K` and `B`'s updated encapsulation key `ek̂B`.
- `rencB : Par → EK → DK → m (CT × K × DK)`, `rdecB : Par → DK → CT → EK → m (K × EK)`.
  `REnc-B`, `RDec-B`: as `rencA`, `rdecA`, with the roles of `A` and `B` swapped.

[REFERENCES]

- [TripleRatchet] Dodis, Jost, Katsumata, Prest, Schmidt.
  *Triple Ratchet: A Bandwidth Efficient Hybrid-Secure Signal Protocol.*
  EUROCRYPT 2025, https://eprint.iacr.org/2025/078.pdf

For the non-forward-secure special case (Remark 5.2 of [TripleRatchet]), take
`rkeygenAUpdated`/`rkeygenBUpdated` to coincide with `rkeygenA`/`rkeygenB`, and
have `rencP`/`rdecP` return their input `dkP`/`ekP` unchanged as the "updated" key.
-/

open ENNReal

universe u

/-- A forward-secure ratcheting key encapsulation mechanism (RKEM), as in
Definition 5.1 of [TripleRatchet]. Public-parameter space `Par`, encapsulation-
and decapsulation-key spaces `EK`, `DK`, ciphertext space `CT`, and shared-key
space `K`. -/
-- ANCHOR: RKEMScheme
structure RKEMScheme (m : Type → Type u) [Monad m] (Par EK DK CT K : Type) where
  /-- `RSetup(1^λ) → par`: samples the public parameter shared by both parties. -/
  rsetup : m Par
  /-- `RKeyGen-A(par, ⊥) → (ekA, dkA)`: samples a fresh key pair for `A`. -/
  rkeygenAFresh : Par → m (EK × DK)
  /-- `RKeyGen-A(par, updated) → (ekA, dkA)`: samples an updated-distribution
  key pair for `A`. -/
  rkeygenAUpdated : Par → m (EK × DK)
  /-- `RKeyGen-B(par, ⊥) → (ekB, dkB)`: samples a fresh key pair for `B`. -/
  rkeygenBFresh : Par → m (EK × DK)
  /-- `RKeyGen-B(par, updated) → (ekB, dkB)`: samples an updated-distribution
  key pair for `B`. -/
  rkeygenBUpdated : Par → m (EK × DK)
  /-- `REnc-A(par, ekB, dkA) → (ctB, K, dk̂A)`: encapsulates towards `B`'s
  encapsulation key using `A`'s decapsulation key, producing a ciphertext for
  `B`, the shared key, and `A`'s updated decapsulation key. -/
  rencA : Par → EK → DK → m (CT × K × DK)
  /-- `RDec-A(par, dkA, ctA, ekB) → (K, ek̂B)`: decapsulates using `A`'s
  decapsulation key and `B`'s encapsulation key, producing the shared key and
  `B`'s updated encapsulation key. -/
  rdecA : Par → DK → CT → EK → m (K × EK)
  /-- `REnc-B(par, ekA, dkB) → (ctA, K, dk̂B)`: as `rencA`, with the roles of
  `A` and `B` swapped. -/
  rencB : Par → EK → DK → m (CT × K × DK)
  /-- `RDec-B(par, dkB, ctB, ekA) → (K, ek̂A)`: as `rdecA`, with the roles of
  `A` and `B` swapped. -/
  rdecB : Par → DK → CT → EK → m (K × EK)
-- ANCHOR_END: RKEMScheme
