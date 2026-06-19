/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.CryptoFoundations.KeyEncapMech
import SecureMessaging.LWE.Frodo.Matrix

/-!
# Frodo KEM

This file gives the Frodo key encapsulation mechanism of [ACD19, Appendix C.2]
over the concrete matrix model of `Frodo.MatrixParams`. Key generation samples
the public matrix `A`, a secret `S`, and an error `E`, and publishes
`B = A * S + E`. Encapsulation samples `S'`, `E'`, `Etilde'`, forms the
ciphertext public key `B' = S' * A + E'` and the shared value
`V' = S' * B + Etilde'`, and outputs the hint `hint V'` and key `key V'`.
Decapsulation reconciles `B' * S` against the hint.

The Frodo KEM is the optimization that the LWE/Frodo CKA reuses; the encapsulation
matrices coincide with paper `CKA-S-B`, so KEM correctness is the same
reconciliation fact `rec_sendA_correct`. Security (IND-CPA) is not addressed here.
-/

open OracleSpec OracleComp

namespace Frodo

/-- Frodo public key: the public matrix `A` and `B = A * S + E`. -/
abbrev PublicKey (p : MatrixParams) := Mat p.q p.n p.n × Mat p.q p.n p.nbar

/-- Frodo secret key: the secret matrix `S`. -/
abbrev SecretKey (p : MatrixParams) := Mat p.q p.n p.nbar

/-- Frodo ciphertext: the public key `B'` and a reconciliation hint. -/
abbrev Ciphertext (p : MatrixParams) := Mat p.q p.nbar p.n × p.Hint

/-- Frodo key generation: sample `A`, `S`, `E`, and publish `(A, B)` with
`B = A * S + E`, keeping `S` as the secret key. -/
def keygen (p : MatrixParams) : ProbComp (PublicKey p × SecretKey p) := do
  let A ← p.uniformMat p.n p.n
  let S ← p.chiMat p.n p.nbar
  let E ← p.chiMat p.n p.nbar
  let B := A * S + E
  return ((A, B), S)

/-- Frodo encapsulation: sample `S'`, `E'`, `Etilde'`, form `B' = S' * A + E'`
and `V' = S' * B + Etilde'`, and output the ciphertext `(B', hint V')` and key
`key V'`. -/
def encaps (p : MatrixParams) : PublicKey p → ProbComp (Ciphertext p × p.Key)
  | (A, B) => do
      let S' ← p.chiMat p.nbar p.n
      let E' ← p.chiMat p.nbar p.n
      let Etilde' ← p.chiMat p.nbar p.nbar
      let B' := S' * A + E'
      let V' := S' * B + Etilde'
      return ((B', p.hint V'), p.key V')

/-- Frodo decapsulation: reconcile `B' * S` against the hint. -/
def decaps (p : MatrixParams) (sk : SecretKey p) : Ciphertext p → Option p.Key
  | (B', h) => p.reconcile (B' * sk) h

/-- The Frodo KEM over a `MatrixParams`. -/
def kem (p : MatrixParams) :
    KEMScheme ProbComp p.Key (PublicKey p) (SecretKey p) (Ciphertext p) where
  keygen := keygen p
  encaps := encaps p
  decaps := fun sk c => return decaps p sk c

/-- Correctness of the Frodo KEM.

Honest decapsulation recovers the encapsulated key with probability one. Because
encapsulation reuses the matrices of paper `CKA-S-B`, agreement is exactly the
reconciliation law `rec_sendA_correct`. -/
theorem kem_correct (p : MatrixParams) [DecidableEq p.Key] :
    Pr[= true | (kem p).CorrectExp] = 1 := by
  rw [← probEvent_eq_eq_probOutput, probEvent_eq_one_iff]
  refine ⟨probFailure_eq_zero, ?_⟩
  intro b hb
  simp only [KEMScheme.CorrectExp, kem] at hb
  rw [mem_support_bind_iff] at hb
  obtain ⟨⟨pk, sk⟩, hkey, hb⟩ := hb
  rw [mem_support_bind_iff] at hb
  obtain ⟨⟨c, k⟩, henc, hb⟩ := hb
  rw [mem_support_bind_iff] at hb
  obtain ⟨k', hdec, hb⟩ := hb
  rw [mem_support_pure_iff] at hb
  simp only [keygen, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at hkey
  obtain ⟨A, -, S, -, E, -, hpk, hsk⟩ := hkey
  subst hpk
  simp only [encaps, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at henc
  obtain ⟨S', -, E', -, Etilde', -, hc, hk⟩ := henc
  subst hc
  simp only [decaps, mem_support_pure_iff] at hdec
  have hrec : k' = some k := by
    rw [hdec, hk, hsk]
    exact p.rec_sendA_correct A S E S' E' Etilde'
  subst hb
  simp [hrec]

end Frodo
