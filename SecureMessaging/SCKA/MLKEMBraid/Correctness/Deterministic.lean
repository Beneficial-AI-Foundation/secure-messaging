import SecureMessaging.SCKA.MLKEMBraid.Correctness.Provenance

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

private theorem add_honest_chunk_payload
    {M Sym : Type} [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (hcorrect : ecp.ec.Correct)
    (payload : M) (dec : DecoderState M Sym)
    (hdec : dec.ecp = ecp ∧
      ∃ I : Finset (Fin ecp.ec.N),
        dec.chunks = ErasureCodePayload.payloadChunks ecp payload I)
    (i : ℕ) :
    let dec' := dec.addChunk (ecp.encode payload i)
    dec'.ecp = ecp ∧
      ∃ I' : Finset (Fin ecp.ec.N),
        dec'.chunks = ErasureCodePayload.payloadChunks ecp payload I' ∧
        (dec'.decodedPayload = none ∨ dec'.decodedPayload = some payload) := by
  rcases dec with ⟨actualEcp, chunks⟩
  rcases hdec with ⟨hecp, I, hchunks⟩
  change actualEcp = ecp at hecp
  subst actualEcp
  change chunks = ErasureCodePayload.payloadChunks ecp payload I at hchunks
  subst chunks
  have hadd := DecoderState.addChunk_payloadChunks ecp payload I i
  let I' := insert (ErasureCodePayload.counterIndex ecp i) I
  rw [hadd]
  refine ⟨rfl, I', rfl, ?_⟩
  by_cases hcard : ecp.ec.nchunk ≤ I'.card
  · exact Or.inr (DecoderState.decodedPayload_payloadChunks
      ecp hcorrect payload I' hcard)
  · apply Or.inl
    unfold DecoderState.decodedPayload
    exact ErasureCodePayload.decode_payloadChunks_none
      ecp hcorrect payload I' (Nat.lt_of_not_ge hcard)

end MLKEMBraid
