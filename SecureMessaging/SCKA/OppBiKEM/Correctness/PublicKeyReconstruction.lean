/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.ErasureCode.Payload
import SecureMessaging.SCKA.OppBiKEM.Correctness.PublicKeyEpochHistory

/-!
# Public-key chunk reconstruction

`RecordedPublicKeyChunks` is an assumed matching-record property of a buffer.
Its preservation along reachable protocol states is not proved here.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

def RecordedPublicKeyChunks
    (msgs : ℕ → Option (Message Sym × ℕ))
    (epoch : ℤ) (chunks : Finset (ℕ × Sym)) : Prop :=
  ∀ chunk ∈ chunks,
    ∃ (n : ℕ) (ρ : Message Sym) (tsnd : ℕ),
      msgs n = some (ρ, tsnd) ∧
      ρ.tRes = epoch ∧
      ρ.bit = some 0 ∧
      ρ.ch = some chunk

private theorem exists_payloadChunks_of_mem_encode {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (chunks : Finset (ℕ × Sym))
    (hchunks : ∀ chunk ∈ chunks, ∃ i : ℕ,
      chunk = ecp.encode payload i) :
    ∃ I : Finset (Fin ecp.ec.N),
      chunks = ErasureCodePayload.payloadChunks ecp payload I ∧
      I.card = chunks.card := by
  classical
  let I : Finset (Fin ecp.ec.N) :=
    chunks.image (fun chunk => ecp.counterIndex chunk.1)
  have hnorm (chunk : ℕ × Sym) (hmem : chunk ∈ chunks) :
      chunk = ecp.encode payload chunk.1 := by
    obtain ⟨i, hi⟩ := hchunks chunk hmem
    rw [hi]
    simp [ErasureCodePayload.encode, ErasureCodePayload.counterIndex]
  have hinj : Set.InjOn
      (fun chunk : ℕ × Sym => ecp.counterIndex chunk.1) chunks := by
    intro a ha b hb heq
    calc
      a = ecp.encode payload a.1 := hnorm a ha
      _ = ecp.encode payload b.1 := by
        simp only [ErasureCodePayload.encode_eq_chunkToNat, heq]
      _ = b := (hnorm b hb).symm
  refine ⟨I, ?_, ?_⟩
  · apply Finset.ext
    intro chunk
    constructor
    · intro hmem
      let j := ecp.counterIndex chunk.1
      have hj : j ∈ I := Finset.mem_image.mpr ⟨chunk, hmem, rfl⟩
      have hbounded :
          (j, ecp.ec.encode (ecp.serialize payload) j) ∈
            ecp.ec.encodeChunks (ecp.serialize payload) I := by
        exact (ErasureCode.mem_encodeChunks _ _ _ _).2 ⟨hj, rfl⟩
      rw [ErasureCodePayload.payloadChunks, Finset.mem_map]
      refine ⟨(j, ecp.ec.encode (ecp.serialize payload) j), hbounded, ?_⟩
      exact (ErasureCodePayload.encode_eq_chunkToNat ecp payload chunk.1).symm.trans
        (hnorm chunk hmem).symm
    · intro hmem
      rw [ErasureCodePayload.payloadChunks, Finset.mem_map] at hmem
      obtain ⟨bounded, hbounded, rfl⟩ := hmem
      obtain ⟨hj, hvalue⟩ :=
        (ErasureCode.mem_encodeChunks _ _ _ bounded).1 hbounded
      obtain ⟨original, horiginal, horiginalIndex⟩ :=
        Finset.mem_image.mp (show bounded.1 ∈ I from hj)
      have hencoded :
          ErasureCode.chunkToNat bounded = ecp.encode payload original.1 := by
        rw [ErasureCodePayload.encode_eq_chunkToNat, horiginalIndex,
          ← hvalue]
      rw [hencoded, ← hnorm original horiginal]
      exact horiginal
  · exact Finset.card_image_of_injOn hinj

theorem publicKeyEpochHistory_buffer_payloadChunks
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (msgs : ℕ → Option (Message Sym × ℕ))
    (st : State PK SK C Sym) (hist : ℤ → Option PK)
    (hs : PublicKeyEpochHistory role kem ecEk ecCt msgs st hist)
    (chunks : Finset (ℕ × Sym))
    (n : ℕ) (ρ : Message Sym) (tsnd : ℕ)
    (hrecord : msgs n = some (ρ, tsnd))
    (hbit : ρ.bit = some 0)
    (hchunks : RecordedPublicKeyChunks msgs ρ.tRes chunks) :
    ∃ (pk : PK) (I : Finset (Fin ecEk.ec.N)) (i : ℕ),
      hist (ρ.tRes + role.offset) = some pk ∧
      chunks = ErasureCodePayload.payloadChunks ecEk pk I ∧
      I.card = chunks.card ∧
      ρ.ch = some (ecEk.encode pk i) := by
  obtain ⟨hmsgs, _⟩ := hs
  obtain ⟨st₀, key?, st₁, _, hprov, _, hhist⟩ :=
    hmsgs n ρ tsnd hrecord
  obtain ⟨pk, hek, hch⟩ := hprov.public_key_chunk hbit
  have hhistpk : hist (ρ.tRes + role.offset) = some pk := hhist pk hek
  have hall : ∀ chunk ∈ chunks, ∃ i : ℕ, chunk = ecEk.encode pk i := by
    intro chunk hmem
    obtain ⟨m, msg, t, hm, hepoch, hbit', hchunk⟩ := hchunks chunk hmem
    obtain ⟨st₀', key?', st₁', _, hprov', _, hhist'⟩ :=
      hmsgs m msg t hm
    obtain ⟨pk', hek', hch'⟩ := hprov'.public_key_chunk hbit'
    have hhistpk' : hist (ρ.tRes + role.offset) = some pk' := by
      simpa only [hepoch] using hhist' pk' hek'
    have hpkeq : pk' = pk := Option.some.inj (hhistpk'.symm.trans hhistpk)
    subst pk'
    exact ⟨st₁'.res.ich, Option.some.inj (hchunk.symm.trans hch')⟩
  obtain ⟨I, hI, hcard⟩ :=
    exists_payloadChunks_of_mem_encode ecEk pk chunks hall
  exact ⟨pk, I, st₁.res.ich, hhistpk, hI, hcard, hch⟩

theorem publicKeyEpochHistory_insertChunkAndDecode
    [DecidableEq Sym]
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (hcorrect : ecEk.ec.Correct)
    (ecCt : ErasureCodePayload C Sym)
    (msgs : ℕ → Option (Message Sym × ℕ))
    (st : State PK SK C Sym) (hist : ℤ → Option PK)
    (hs : PublicKeyEpochHistory role kem ecEk ecCt msgs st hist)
    (chunks : Finset (ℕ × Sym))
    (n : ℕ) (ρ : Message Sym) (tsnd : ℕ)
    (hrecord : msgs n = some (ρ, tsnd))
    (hbit : ρ.bit = some 0)
    (hchunks : RecordedPublicKeyChunks msgs ρ.tRes chunks) :
    ∃ pk : PK,
      hist (ρ.tRes + role.offset) = some pk ∧
      (insertChunkAndDecode ecEk chunks ρ.ch).2 =
        (if ecEk.ec.nchunk ≤
          (insertChunkAndDecode ecEk chunks ρ.ch).1.card
         then some pk else none) := by
  obtain ⟨pk, I, i, hhist, hI, _, hch⟩ :=
    publicKeyEpochHistory_buffer_payloadChunks role kem ecEk ecCt
      msgs st hist hs chunks n ρ tsnd hrecord hbit hchunks
  refine ⟨pk, hhist, ?_⟩
  have hinsert :
      insert (ecEk.encode pk i) chunks =
        ErasureCodePayload.payloadChunks ecEk pk
          (insert (ecEk.counterIndex i) I) := by
    rw [hI, ErasureCodePayload.insert_payloadChunks]
  simp only [hch, insertChunkAndDecode]
  rw [hinsert]
  have hcard :
      (ErasureCodePayload.payloadChunks ecEk pk
        (insert (ecEk.counterIndex i) I)).card =
      (insert (ecEk.counterIndex i) I).card := by
    simp [ErasureCodePayload.payloadChunks]
  rw [hcard]
  by_cases hthreshold :
      ecEk.ec.nchunk ≤ (insert (ecEk.counterIndex i) I).card
  · simp only [if_pos hthreshold]
    exact ErasureCodePayload.decode_payloadChunks ecEk hcorrect pk _ hthreshold
  · simp only [if_neg hthreshold]
    exact ErasureCodePayload.decode_payloadChunks_none ecEk hcorrect pk _
      (Nat.lt_of_not_ge hthreshold)

end oppBiKemCKA
