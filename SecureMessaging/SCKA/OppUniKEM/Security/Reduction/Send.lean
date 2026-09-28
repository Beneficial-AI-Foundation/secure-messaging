/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Pinned
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Relation

/-!
# Send operations under marked states

**Parameters.** Fix a selected epoch `e`, a complete material value `m`,
and a local state of the sending party. The honest intermediate sampler
uses `m` in epoch `e`; the symbolic sampler uses its public key and ciphertext
and replaces the selected secrets by unavailable markers.

**Statement.** Marking the honest send's result gives the symbolic send's
joint distribution of optional key, message, sending epoch, and successor.

**Proof.** Both algorithms inspect the same public phase fields. A fresh
selected sample is the marked form of the fixed material; each other fresh
sample uses the original sampler in both computations. Deterministic
retransmissions retain the existing material and encode the same chunk.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

set_option maxHeartbeats 800000 in
-- The two KEM instantiations carry different secret-key types through the send equation.
/-- For every A-state `s`, selected epoch `e`, and material value `m`, A's
symbolic send equals its pinned honest send followed by marking the successor.
The optional derived key is `none` in both sends. The auxiliary decapsulation
parameters are arbitrary because sending A uses key generation and encoding. -/
theorem sendA_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (selectedB : Bool)
    (keyS : Option (Option K)) (keyH : Option K) (s : StA onoff Sym) :
    sendA (kem base onoff (decide (s.t = e)) selectedB m.keygen.1.1 m.ciphertext keyS)
      (onOff base onoff (decide (s.t = e)) selectedB m.keygen.1.1 m.ciphertext keyS)
      ecEk (markA e s) =
    (fun out => out.map (fun (_, msg, epoch, next) => (none, msg, epoch, markA e next))) <$>
      sendA (Pinned.kem m (decide (s.t = e)) selectedB keyH)
        (Pinned.onOff m (decide (s.t = e)) selectedB keyH) ecEk s := by
  by_cases he : s.t = e <;> cases hd : s.dkA
  all_goals
    simp only [sendA, markA, hd, Option.map_none, Option.map_some]
    dsimp only [kem, onOff, Pinned.kem, Pinned.onOff]
    simp [keygen, Pinned.keygen, mark, he, Prod.map, monad_norm]

set_option maxHeartbeats 1600000 in
-- Each offline/online phase expands both honest and symbolic state updates.
/-- For every B-state `s`, selected epoch `e`, and material value `m`, B's
symbolic send equals its pinned honest send followed by marking the returned
epoch key and successor. This covers offline, online, combined, and
retransmission phases. -/
theorem sendB_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (selectedA : Bool)
    (keyS : Option (Option K)) (keyH : Option K) (s : StB onoff Sym) :
    sendB (kem base onoff selectedA (decide (s.t = e)) m.keygen.1.1 m.ciphertext keyS)
      (onOff base onoff selectedA (decide (s.t = e)) m.keygen.1.1 m.ciphertext keyS)
      ecCt0 ecCt1 (markB e s) =
    (fun out => out.map (fun (key, msg, epoch, next) =>
      (key.map (fun (t, k) => (t, mark e t k)), msg, epoch, markB e next))) <$>
      sendB (Pinned.kem m selectedA (decide (s.t = e)) keyH)
        (Pinned.onOff m selectedA (decide (s.t = e)) keyH) ecCt0 ecCt1 s := by
  by_cases he : s.t = e <;> cases hct0 : s.ct0 <;> cases hek : s.ekA <;>
    cases hct1 : s.ct1 <;> cases hst : s.stCt <;> cases hack : s.ack.ctRec
  all_goals
    simp only [sendB, markB, hct0, hek, hct1, hst, Option.map_none, Option.map_some]
    dsimp only [kem, onOff, Pinned.kem, Pinned.onOff]
    simp [encapsOff, encapsOn, Pinned.encapsOff, Pinned.encapsOn, Material.ciphertext,
      mark, he, hct0, hek, hct1, hst, hack, Prod.map, monad_norm]

/-- Mark each coin returned by a send in epoch `t`: selected-epoch coins
become unavailable, other coins remain known, and deterministic sends retain
`SendRand.none`. -/
def markCoins {KG OFF ON : Type} (e t : ℕ) :
    SendRand KG OFF ON → SendRand (Option KG) (Option OFF) (Option ON)
  | .none => .none
  | .keygen r => .keygen (mark e t r)
  | .off r => .off (mark e t r)
  | .on r => .on (mark e t r)
  | .offOn r₀ r₁ => .offOn (mark e t r₀) (mark e t r₁)

/-- For every selected epoch, sending epoch, and coin response, revelation
returns the original coins outside the selected epoch. In the selected
epoch, deterministic sends return `SendRand.none` and sampling phases terminate. -/
theorem revealCoins_mark {KG OFF ON : Type} (e t : ℕ) (r : SendRand KG OFF ON) :
    revealCoins (markCoins e t r) =
      if t = e then (match r with | .none => some .none | _ => none) else some r := by
  cases r <;> by_cases h : t = e <;> simp [markCoins, revealCoins, mark, h]

set_option maxHeartbeats 1000000 in
-- Both leakage witnesses expand through different secret and coin types.
/-- For every A-state and selected material, A's symbolic leaking send equals
its pinned honest leaking send followed by marking the successor and coins.
The optional derived key is `none` in both computations. -/
theorem sendArleak_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (selectedB : Bool)
    (keyS : Option (Option K)) (keyH : Option K) (s : StA onoff Sym) :
    sendArleak (kem base onoff (decide (s.t = e)) selectedB m.keygen.1.1 m.ciphertext keyS)
      (onOff base onoff (decide (s.t = e)) selectedB m.keygen.1.1 m.ciphertext keyS)
      ecEk (leakage base onoff leak (decide (s.t = e)) selectedB
        m.keygen.1.1 m.ciphertext keyS) (markA e s) =
    (fun out => out.map (fun (_, msg, epoch, next, coins) =>
      (none, msg, epoch, markA e next, markCoins e s.t coins))) <$>
      sendArleak (Pinned.kem m (decide (s.t = e)) selectedB keyH)
        (Pinned.onOff m (decide (s.t = e)) selectedB keyH) ecEk
        (Pinned.leakage leak m (decide (s.t = e)) selectedB keyH) s := by
  by_cases he : s.t = e <;> cases hd : s.dkA
  all_goals
    simp only [sendArleak, markA, hd, Option.map_none, Option.map_some]
    try dsimp only [leakage, Pinned.leakage]
    simp [keygenLeak, markCoins, mark, he, monad_norm]

set_option maxHeartbeats 2000000 in
-- Each leakage phase expands its output, coin conversion, and state update.
/-- For every B-state and selected material, B's symbolic leaking send equals
its pinned honest leaking send followed by marking the returned epoch key,
successor, and coins. The statement includes combined sampling and retransmission. -/
theorem sendBrleak_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (selectedA : Bool)
    (keyS : Option (Option K)) (keyH : Option K) (s : StB onoff Sym) :
    sendBrleak (kem base onoff selectedA (decide (s.t = e)) m.keygen.1.1 m.ciphertext keyS)
      (onOff base onoff selectedA (decide (s.t = e)) m.keygen.1.1 m.ciphertext keyS)
      ecCt0 ecCt1 (leakage base onoff leak selectedA (decide (s.t = e))
        m.keygen.1.1 m.ciphertext keyS) (markB e s) =
    (fun out => out.map (fun (key, msg, epoch, next, coins) =>
      (key.map (fun (t, k) => (t, mark e t k)), msg, epoch,
        markB e next, markCoins e s.t coins))) <$>
      sendBrleak (Pinned.kem m selectedA (decide (s.t = e)) keyH)
        (Pinned.onOff m selectedA (decide (s.t = e)) keyH) ecCt0 ecCt1
        (Pinned.leakage leak m selectedA (decide (s.t = e)) keyH) s := by
  by_cases he : s.t = e <;> cases hct0 : s.ct0 <;> cases hek : s.ekA <;>
    cases hct1 : s.ct1 <;> cases hst : s.stCt <;> cases hack : s.ack.ctRec
  all_goals
    simp only [sendBrleak, markB, hct0, hek, hct1, hst, Option.map_none, Option.map_some]
    try dsimp only [leakage, Pinned.leakage]
    simp [offLeak, onLeak, Material.ciphertext, markCoins, mark,
      he, hct0, hek, hct1, hst, hack, monad_norm]

end oppUniKemCKA.Security.Embedding
