import VersoManual
import VersoBlueprint

open Verso.Genre Manual

@[bib "ACD19"]
def ACD19 : Verso.Genre.Manual.Bibliography.Citable := .inProceedings
  { title := inlines!"The Double Ratchet: Security Notions, Proofs, and Modularization for the Signal Protocol"
  , authors := #[inlines!"Joël Alwen", inlines!"Sandro Coretti", inlines!"Yevgeniy Dodis"]
  , year := 2019
  , booktitle := inlines!"EUROCRYPT 2019"
  , url := some "https://eprint.iacr.org/2018/1037" }

@[bib "TR25"]
def TR25 : Verso.Genre.Manual.Bibliography.Citable := .inProceedings
  { title := inlines!"Triple Ratchet: A Bandwidth-Efficient Hybrid-Secure Signal Protocol"
  , authors := #[inlines!"Yevgeniy Dodis", inlines!"Daniel Jost", inlines!"Shuichi Katsumata", inlines!"Thomas Prest", inlines!"Sebastian Schmidt"]
  , year := 2025
  , booktitle := inlines!"EUROCRYPT 2025"
  , url := some "https://eprint.iacr.org/2025/078" }

@[bib "SCKA25"]
def SCKA25 : Verso.Genre.Manual.Bibliography.Citable := .inProceedings
  { title := inlines!"How to Compare Bandwidth-Constrained Two-Party Secure Messaging Protocols: A Quest for a More Efficient and Secure Post-Quantum Protocol"
  , authors := #[inlines!"Benedikt Auerbach", inlines!"Yevgeniy Dodis", inlines!"Daniel Jost", inlines!"Shuichi Katsumata", inlines!"Sebastian Schmidt"]
  , year := 2025
  , booktitle := inlines!"USENIX Security 2025"
  , url := some "https://eprint.iacr.org/2025/2267" }

@[bib "BN00"]
def BN00 : Verso.Genre.Manual.Bibliography.Citable := .inProceedings
  { title := inlines!"Authenticated Encryption: Relations among Notions and Analysis of the Generic Composition Paradigm"
  , authors := #[inlines!"Mihir Bellare", inlines!"Chanathip Namprempre"]
  , year := 2000
  , booktitle := inlines!"ASIACRYPT 2000"
  , url := some "https://eprint.iacr.org/2000/025" }

@[bib "Rog02"]
def Rog02 : Verso.Genre.Manual.Bibliography.Citable := .inProceedings
  { title := inlines!"Authenticated-Encryption with Associated-Data"
  , authors := #[inlines!"Phillip Rogaway"]
  , year := 2002
  , booktitle := inlines!"CCS 2002"
  , url := some "https://web.cs.ucdavis.edu/~rogaway/papers/ad.pdf" }

@[bib "NIST-GCM"]
def NIST_GCM : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Recommendation for Block Cipher Modes of Operation: Galois/Counter Mode (GCM) and GMAC"
  , authors := #[inlines!"Morris Dworkin"]
  , journal := inlines!"NIST Special Publication"
  , year := 2007
  , month := some (inlines!"November")
  , volume := inlines!"800-38D"
  , number := inlines!""
  , url := some "https://csrc.nist.gov/pubs/sp/800/38/d/final" }

@[bib "RFC5510"]
def RFC5510 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Reed-Solomon Forward Error Correction (FEC) Schemes"
  , authors := #[inlines!"J. Lacan", inlines!"V. Roca", inlines!"J. Peltotalo", inlines!"S. Peltotalo"]
  , journal := inlines!"RFC"
  , year := 2009
  , month := some (inlines!"April")
  , volume := inlines!"5510"
  , number := inlines!""
  , url := some "https://datatracker.ietf.org/doc/rfc5510/" }

@[bib "SPQR-ENC"]
def SPQR_ENC : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Sparse Post Quantum Ratchet: Encoding Layer"
  , authors := #[inlines!"Signal"]
  , journal := inlines!"SparsePostQuantumRatchet"
  , year := 2025
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , url := some "https://github.com/signalapp/SparsePostQuantumRatchet/tree/main/src/encoding" }

@[bib "MLKEM-Braid"]
def MLKEM_Braid : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"The ML-KEM Braid Specification"
  , authors := #[inlines!"Signal"]
  , journal := inlines!"Signal Specifications"
  , year := 2025
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , url := some "https://signal.org/docs/specifications/mlkembraid/" }
