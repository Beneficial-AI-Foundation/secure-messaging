/-
  Symmetric (authenticated) encryption for DYLean.

  DYLean's standard equational theories (`DY/EquationalTheory/`) provide
  concatenation, literals, hashing, signatures, Diffie-Hellman and KDFs,
  but no symmetric encryption.
  LeanDY, on the other hand, has `symenc`/`symdec` built into its fixed symbolic algebra.
  To port LeanDY's SimpleAuth example we therefore add the primitive ourselves,
  locally in the example folder (as DYLean's `Examples/SignedDHKEM/KEM.lean` does for KEMs),
  so the framework itself stays untouched.

  The structure of this file mirrors `DY/EquationalTheory/Sign.lean`:
  1. Constructors: a new symbolic constructor `Enc { key, msg }` and its destructor;
  2. AttackerKnowledge: what the attacker can compute with the new constructor;
  3. Invariants: well-formedness, usage, label and invariant of ciphertexts;
  4. HoareTriples: the specifications used by the `step` tactic;
  5. AttackerKnowledgeTheorem: proof that the attacker capabilities preserve publishability.
-/

module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances
public import DY.Trace.Manipulation -- HoareTriplePure

namespace DY.SymEnc

/--
  The user-facing interface.
  Encryption is deterministic (no encryption nonce), exactly like LeanDY's `symenc`.
  Decryption may fail, hence it returns `Err Bytes` (an `Option` that can be lifted into `Traceful`).
-/
public
class CanSymEnc (Bytes: Type u) where
  symEnc: (key: Bytes) → (msg: Bytes) → Bytes
  symDec: (key: Bytes) → (cipher: Bytes) → Err Bytes

export CanSymEnc (symEnc)
export CanSymEnc (symDec)

section Constructors

namespace Enc

/--
  The symbolic constructor for ciphertexts.
  `Bytes` in DYLean is an "à la carte" inductive type:
  each equational theory contributes one (or several) constructor(s),
  and an instance combines them.
  This structure is the constructor contributed by this theory.
-/
public
structure SubF (Bytes: Type) where
  key: Bytes
  msg: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {key, msg} => sizeOf key + sizeOf msg

-- Generic (boilerplate) representation of the constructor:
-- no data of its own, two recursive arguments (`key` and `msg`).
public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 2 }

  toRepr | {key, msg} => {
    id := ()
    data := ()
    as := #v[key, msg]
  }
  fromRepr
  | {id, data, as} =>
    let key := as[0]
    let msg := as[1]
    { key, msg }
  from_to | {key, msg} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {key, msg} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

-- Length of a ciphertext: length of the plaintext plus a 16-byte authentication tag.
public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun { key := _, msg } rec =>
    rec msg + 16

end Enc

-- Package the constructor so that it can be plugged into a protocol's `Bytes`
-- (this defines `SymEnc.SubF` and `SymEnc.SubF.length`).
#combine into BytesFunctor, BytesLength from
  Enc,

variable [BytesFunctor] [BytesFunctor.Has SubF]

public abbrev Enc.SubF.pack (x: Enc.SubF Bytes) := BytesView.pack x

/--
  Encryption builds the symbolic term `Enc { key, msg }`.
  Decryption is the destructor: it succeeds only on a ciphertext built with the same key.
  This is the symbolic equation `symDec k (symEnc k m) = m`
  (in LeanDY, the same equation is implemented by the normalizer `γ`).
-/
public
instance: CanSymEnc Bytes where
  symEnc key msg :=
    ({key, msg}: Enc.SubF Bytes).pack

  symDec key cipher :=
    match cipher.view? Enc.SubF with
    | some { key := key', msg } =>
      if key = key' then
        some msg
      else
        none
    | none => none

-- Functional correctness: decryption inverts encryption.
public
theorem symDec_symEnc
  (key msg: Bytes)
  : symDec key (symEnc key msg) = some msg
:= by
  simp only [symDec, symEnc]
  grind

-- Conversely, a successful decryption reveals how the ciphertext was built.
public
theorem symEnc_symDec
  (key cipher msg: Bytes)
  : symDec key cipher = some msg →
    cipher = symEnc key msg
:= by
  simp only [symDec, symEnc]
  have := Bytes.pack_view? Enc.SubF cipher
  grind

end Constructors

section AttackerKnowledge

/-
  The Dolev-Yao attacker can encrypt any message it knows with any key it knows,
  and decrypt any ciphertext it knows with any key it knows.
  (In LeanDY these rules are built into the fixed `AttackerKnows` relation;
  in DYLean each equational theory contributes its own rules.)
-/

public
def symEnc.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ key msg,
      out = symEnc key msg ∧
      p key ∧
      p msg

public
def symDec.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ key cipher,
      symDec key cipher = some out ∧
      p key ∧
      p cipher

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  symEnc,
  symDec

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

-- Convenience lemmas, useful to write attacker programs in sanity checks.

public
theorem attacker_knows_symEnc
  (key msg: Bytes) (tr: ExecTrace)
  : key.AttackerKnows tr →
    msg.AttackerKnows tr →
    (symEnc key msg).AttackerKnows tr
:= by
  intro h_key h_msg
  apply Bytes.AttackerKnows.prove symEnc.attackerKnowledge
  simp only [symEnc.attackerKnowledge]
  grind

public
theorem attacker_knows_symDec
  (key cipher: Bytes) (tr: ExecTrace)
  : key.AttackerKnows tr →
    cipher.AttackerKnows tr →
    match symDec key cipher with
    | none => True
    | some msg => msg.AttackerKnows tr
:= by
  intro h_key h_cipher
  split
  · trivial
  apply Bytes.AttackerKnows.prove symDec.attackerKnowledge
  simp only [symDec.attackerKnowledge]
  grind

end AttackerKnowledge

section Invariants

section Definition

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]

/--
  The protocol-specific part of the encryption invariant.
  This plays the role of LeanDY's `CryptoPreds.u_sym_enc_pred`:
  it describes which plaintexts honest participants may encrypt under a key with a given usage.
  Arguments: key usage, key, plaintext, trace.
-/
public
class SymEncPred where
  pred: [BytesWellFormed] → [GetUsage] → [GetLabel] → Usage → Bytes → Bytes → ProofTrace → Prop

/--
  The predicate must be stable when the trace grows
  (DYLean invariants are monotone: once true, always true).
-/
public
class SymEncPredProof [BytesInvariants] [SymEncPred] where
  pred_later:
    [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
    ∀ keyUsg key msg tr1 tr2,
      key.WellFormed tr1 →
      msg.WellFormed tr1 →
      tr1 ≤ tr2 →
      SymEncPred.pred keyUsg key msg tr1 →
      SymEncPred.pred keyUsg key msg tr2

grind_pattern SymEncPredProof.pred_later => tr1 ≤ tr2, SymEncPred.pred keyUsg key msg tr1

public
theorem SymEncPredProof.pred_later_fast
  [BytesInvariants] [SymEncPred] [SymEncPredProof] [BytesInvariantsProofs]
  (keyUsg: Usage) (key msg: Bytes) (tr1 tr2: ProofTrace)
  : key.Invariant tr1 →
    msg.Invariant tr1 →
    tr1 ≤ tr2 →
    SymEncPred.pred keyUsg key msg tr1 →
    SymEncPred.pred keyUsg key msg tr2
:= by grind

grind_pattern [grind_later] SymEncPredProof.pred_later_fast => tr1 ≤ tr2, SymEncPred.pred keyUsg key msg tr1

/--
  What every ciphertext `Enc { key, msg }` occurring in a valid trace satisfies.
  This is where secrecy and authentication of encryption are encoded
  (in the style of DY*'s `aead_enc` invariant).

  - The ciphertext itself is public (its label is `Label.pub`).
  - Its invariant states that it was produced either
    * honestly: the key has a "SymKey" usage, the protocol predicate holds,
      and the plaintext is no more secret than the key (`msg.label` can flow to `key.label`),
      so that publishing the ciphertext does not leak the plaintext; or
    * by the attacker: in which case both the key and the plaintext are public.
-/
public
def Enc.invariants [BytesFunctor.Has SymEnc.SubF] [SymEncPred]: Bytes.PartialInvariants Enc.SubF where
  well_formed := fun {key, msg} rec tr =>
      (rec key) tr ∧
      (rec msg) tr

  usage := fun {key, msg} rec tr =>
    Usage.nothing

  label := fun {key, msg} rec tr =>
    Label.pub

  invariant := fun {key, msg} rec tr =>
      (rec key) tr ∧
      (rec msg) tr ∧
      (
        (
          ∃ keyUsg,
          -- Honest case:
          -- - the key has a symmetric-encryption usage,
          key.HasUsage keyUsg tr ∧
          keyUsg.type = "SymKey" ∧
          -- - the custom (protocol-specific) predicate holds,
          SymEncPred.pred keyUsg key msg tr ∧
          -- - the plaintext is at most as secret as the key.
          (msg.label tr).canFlow (key.label tr) tr.erase
        ) ∨ (
          -- Attacker case: the attacker knows both the key and the plaintext.
          (key.label tr).canFlow Label.pub tr.erase ∧
          (msg.label tr).canFlow Label.pub tr.erase
        )
      )

public
theorem Enc.invariantsProofs [BytesFunctor.Has SymEnc.SubF] [BytesInvariants] [SymEncPred] [SymEncPredProof]: Bytes.PartialInvariantsProofs Enc.invariants where
  invariant_later := by
    intro _ _ _ _ x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, BytesInvariantLaterT]
    grind

end Definition

-- Package the invariants (this defines `SymEnc.invariants` and `SymEnc.invariantsProofs`).
#combine [BytesFunctor.Has SubF] [SymEncPred] into
  BytesInvariants,
  BytesInvariantsProofs [SymEncPredProof]
from
  Enc,

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [SymEncPred]
variable [BytesInvariants] [BytesInvariants.Has invariants]

@[simp]
public
theorem symEnc.WellFormed
  (key msg: Bytes) (tr: ProofTrace)
  : (symEnc key msg).WellFormed tr = (key.WellFormed tr ∧ msg.WellFormed tr)
:= by
  simp [symEnc, Bytes.WellFormed.eq, Enc.invariants]

@[simp]
public
theorem symEnc.label
  (key msg: Bytes) (tr: ProofTrace)
  : (symEnc key msg).label tr = Label.pub
:= by
  simp [symEnc, Bytes.label.eq, Enc.invariants]

/-- Introduction rule: how to prove that a ciphertext satisfies the invariant. -/
public
theorem symEnc.Invariant
  (key msg: Bytes) (keyUsg: Usage) (tr: ProofTrace)
  : (
      key.Invariant tr ∧
      msg.Invariant tr ∧
      key.HasUsage keyUsg tr ∧
      (
        (
          keyUsg.type = "SymKey" ∧
          SymEncPred.pred keyUsg key msg tr ∧
          (msg.label tr).canFlow (key.label tr) tr.erase
        ) ∨ (
          (key.label tr).canFlow Label.pub tr.erase ∧
          (msg.label tr).canFlow Label.pub tr.erase
        )
      )
    ) →
    (symEnc key msg).Invariant tr
:= by
  simp [symEnc, Bytes.Invariant.eq, Enc.invariants]
  grind

/--
  Elimination rule: what we learn from a successful decryption.
  The plaintext satisfies the invariant, it is at most as secret as the key,
  and either the protocol predicate holds (honest encryption)
  or the key is known to the attacker.
-/
public
theorem symDec.Invariant
  (key cipher msg: Bytes) (keyUsg: Usage) (tr: ProofTrace)
  : cipher.Invariant tr →
    key.HasUsage keyUsg tr →
    symDec key cipher = some msg →
    msg.Invariant tr ∧
    (msg.label tr).canFlow (key.label tr) tr.erase ∧
    (
      SymEncPred.pred keyUsg key msg tr ∨
      (key.label tr).canFlow Label.pub tr.erase
    )
:= by
  intro h_cipher h_usg h_dec
  have h_eq := symEnc_symDec key cipher msg h_dec
  subst h_eq
  have := Bytes.HasUsage_inj key keyUsg
  simp [symEnc, Bytes.Invariant.eq, Enc.invariants] at h_cipher
  grind [canFlowTrans]

end Invariants

section HoareTriples

/-
  The `step` tactic works with Hoare triples registered as typeclass instances.
  Both encryption and decryption take the key usage as a *ghost* argument:
  it does not exist at runtime, the proof supplies it with `step with ⟨ usage ⟩`.
-/

variable [BytesFunctor] [BytesFunctor.Has SubF]

public
instance
  (key msg: Bytes)
  : HasGhostArgumentType (symEnc key msg) Usage
where
  dummy := ()

public
instance
  [ExecTraceTypes] [ProofTraceTypes]
  [SymEncPred]
  [BytesInvariants] [BytesInvariants.Has invariants]
  (key msg: Bytes) (keyUsg: Usage)
  : HoareTriplePureGhost
    (symEnc key msg)
    (keyUsg)
    (fun tr =>
      key.Invariant tr ∧
      msg.Invariant tr ∧
      key.HasUsage keyUsg tr ∧
      (
        (
          keyUsg.type = "SymKey" ∧
          SymEncPred.pred keyUsg key msg tr ∧
          (msg.label tr).canFlow (key.label tr) tr.erase
        ) ∨ (
          (key.label tr).canFlow Label.pub tr.erase ∧
          (msg.label tr).canFlow Label.pub tr.erase
        )
      )
    )
    (fun res tr =>
      res.Publishable tr
    )
where
  pf := by
    intro tr h_pre
    have := symEnc.Invariant key msg keyUsg tr h_pre
    simp only [Bytes.Publishable, symEnc.label]
    grind

public
instance
  (key cipher: Bytes)
  : HasGhostArgumentType (symDec key cipher) Usage
where
  dummy := ()

public
instance
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [SymEncPred]
  [BytesInvariants] [BytesInvariants.Has invariants]
  (key cipher: Bytes) (keyUsg: Usage)
  : HoareTripleGhost
    (symDec key cipher)
    (keyUsg)
    (fun tr =>
      cipher.Invariant tr ∧
      key.HasUsage keyUsg tr
    )
    (fun msg tr =>
      msg.Invariant tr ∧
      (msg.label tr).canFlow (key.label tr) tr.erase ∧
      (
        SymEncPred.pred keyUsg key msg tr ∨
        (key.label tr).canFlow Label.pub tr.erase
      )
    )
where
  pf := by
    simp only [hoareTriple, wp, OptionT.run]
    intro tr h_pre _
    split
    · trivial
    rename_i msg h_dec
    exact symDec.Invariant key cipher msg keyUsg tr h_pre.1 h_pre.2 h_dec

end HoareTriples

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [SymEncPred]
variable [BytesInvariants.Has invariants]

-- Every attacker capability maps publishable inputs to publishable outputs.

public
instance: SubAttackerKnowledgeTheorem symEnc.attackerKnowledge where
  pf := by
    simp only [symEnc.attackerKnowledge]
    intro out tr h_tr ⟨key, msg, ⟨ h_out, h_key, h_msg ⟩⟩
    subst h_out
    have := symEnc.Invariant key msg Usage.nothing tr
    simp_all [Bytes.Publishable, Bytes.HasUsage]
    grind

public
instance: SubAttackerKnowledgeTheorem symDec.attackerKnowledge where
  pf := by
    simp only [symDec.attackerKnowledge]
    intro out tr h_tr ⟨key, cipher, ⟨ h_dec, h_key, h_cipher ⟩⟩
    have := symDec.Invariant key cipher out Usage.nothing tr
    simp_all [Bytes.Publishable, Bytes.HasUsage]
    grind [canFlowTrans]

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [BytesFunctor.Has SubF] [SymEncPred] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  symEnc,
  symDec

end AttackerKnowledgeTheorem

end DY.SymEnc
