/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Construction

/-!
# GCM: cipher-call profile

For a message of `n` blocks, one-time GCM calls the block cipher on `n + 2` inputs in three
groups: `0¹²⁸`, whose output is the GHASH key `H`; `J₀`, whose output is the tag mask; and the
`n` counter blocks from `inc₃₂(J₀)`, whose outputs form the GCTR keystream.
`gcmEncrypt_profile` and `gcmDecrypt_profile` rewrite the algorithms as functions
`gcmEncryptSpec` and `gcmDecryptSpec` of these outputs, which is where the security proof
substitutes random values for them. Distinctness of the inputs is in `Security/Counter.lean`.
-/

namespace GCM

/-! ## Foundation lemmas -/

theorem keystream_singleton (b : BitVec 128) : keystream [b] 128 = b := by
  apply BitVec.eq_of_getMsbD_eq
  intro i hi
  simp [keystream, hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]

theorem counterChain_one (icb : BitVec 128) : counterChain icb 1 = [icb] := rfl

/-- On a single block `s`, `GCTR_K(icb, s) = s ⊕ CIPH_K(icb)`. -/
theorem gctr_single_block {K : Type} (ciph : K → BitVec 128 → BitVec 128) (k : K)
    (icb : BitVec 128) (s : BitVec 128) :
    gctr ciph k icb s = s ^^^ ciph k icb := by
  simp only [gctr, Nat.reduceAdd, Nat.reduceDiv, counterChain_one, List.map_cons,
    List.map_nil, keystream_singleton]

/-! ## Encryption profile -/

/-- GCM encryption as a function of its three separated cipher outputs: GHASH key `h`, tag
mask `mask` and keystream blocks `ksBlocks`. -/
def gcmEncryptSpec (h mask : BitVec 128) (ksBlocks : List (BitVec 128))
    {lenA lenP : ℕ} (ad : BitVec lenA) (m : BitVec lenP) :
    BitVec lenP × BitVec 128 :=
  let c := m ^^^ keystream ksBlocks lenP
  (c, ghash h (padBlocks ad ++ padBlocks c ++
        [BitVec.ofNat 64 lenA ++ BitVec.ofNat 64 lenP]) ^^^ mask)

-- ANCHOR: gcmEncrypt_profile
theorem gcmEncrypt_profile {K : Type} (ciph : CIPH K) (k : K) (iv : BitVec 96)
    {lenA lenP : ℕ} (ad : BitVec lenA) (m : BitVec lenP) :
    gcmEncrypt ciph k iv ad m =
      gcmEncryptSpec (ciph.perm k 0) (ciph.perm k (j0 iv))
        ((counterChain (inc32 (j0 iv)) ((lenP + 127) / 128)).map (ciph.perm k)) ad m := by
-- ANCHOR_END: gcmEncrypt_profile
  simp only [gcmEncrypt, gcmEncryptSpec]
  rw [gctr_single_block]
  simp only [gctr]

/-! ## Decryption profile -/

/-- GCM decryption as a function of its three separated cipher outputs, mirroring
`gcmEncryptSpec`. -/
def gcmDecryptSpec (h mask : BitVec 128) (ksBlocks : List (BitVec 128))
    {lenA lenP : ℕ} (ad : BitVec lenA) (ct : BitVec lenP × BitVec 128) :
    Option (BitVec lenP) :=
  if ct.2 = ghash h (padBlocks ad ++ padBlocks ct.1 ++
        [BitVec.ofNat 64 lenA ++ BitVec.ofNat 64 lenP]) ^^^ mask
  then some (ct.1 ^^^ keystream ksBlocks lenP) else none

/-- For supported message and AAD lengths, `gcmDecrypt` is `gcmDecryptSpec` at the cipher
outputs on `0`, `J₀` and the counter chain from `inc₃₂(J₀)`. Without the length hypothesis the
equation is false: at an unsupported length the left side is `none`, since `gcmDecrypt` checks
lengths first, but the right side is `some` whenever the tag verifies, since `gcmDecryptSpec`
checks no lengths. -/
-- ANCHOR: gcmDecrypt_profile
theorem gcmDecrypt_profile {K : Type} (ciph : CIPH K) (k : K) (iv : BitVec 96)
    {lenA lenP : ℕ} (ad : BitVec lenA) (ct : BitVec lenP × BitVec 128)
    (hv : ValidMsgLength lenP ∧ ValidAADLength lenA) :
    gcmDecrypt ciph k iv ad ct =
      gcmDecryptSpec (ciph.perm k 0) (ciph.perm k (j0 iv))
        ((counterChain (inc32 (j0 iv)) ((lenP + 127) / 128)).map (ciph.perm k)) ad ct := by
-- ANCHOR_END: gcmDecrypt_profile
  obtain ⟨c, t⟩ := ct
  simp only [gcmDecrypt, gcmDecryptSpec]
  rw [if_pos hv, gctr_single_block]
  simp only [gctr]

/-! ## Specialization to `gcmOneTimeAEAD` -/

theorem gcmOneTimeAEAD_encrypt_profile {K : Type} (prp : PRPScheme K (BitVec 128))
    (iv : BitVec 96) {L : ℕ} (hL : ValidMsgLength L) (k : K) (ad : SupportedAAD)
    (m : BitVec L) :
    (gcmOneTimeAEAD prp iv L hL).encrypt k ad m =
      gcmEncryptSpec (prp.toBlockCipher.perm k 0) (prp.toBlockCipher.perm k (j0 iv))
        ((counterChain (inc32 (j0 iv)) ((L + 127) / 128)).map (prp.toBlockCipher.perm k))
        ad.1.2 m :=
  gcmEncrypt_profile prp.toBlockCipher k iv ad.1.2 m

theorem gcmOneTimeAEAD_decrypt_profile {K : Type} (prp : PRPScheme K (BitVec 128))
    (iv : BitVec 96) {L : ℕ} (hL : ValidMsgLength L) (k : K) (ad : SupportedAAD)
    (ct : BitVec L × BitVec 128) :
    (gcmOneTimeAEAD prp iv L hL).decrypt k ad ct =
      gcmDecryptSpec (prp.toBlockCipher.perm k 0) (prp.toBlockCipher.perm k (j0 iv))
        ((counterChain (inc32 (j0 iv)) ((L + 127) / 128)).map (prp.toBlockCipher.perm k))
        ad.1.2 ct :=
  gcmDecrypt_profile prp.toBlockCipher k iv ad.1.2 ct ⟨hL, ad.2⟩

end GCM
