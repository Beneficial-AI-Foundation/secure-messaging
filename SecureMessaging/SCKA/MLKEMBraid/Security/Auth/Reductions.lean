/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Security.Auth.Games
public import SecureMessaging.SCKA.MLKEMBraid.Security.KDFGame

/-!
# The four reductions of the authenticated security theorem

Each reduction draws an epoch `e ← epochChoice q` (uniform on `1, …, q` when `q > 0`, and `1`
when `q = 0`) and a side uniform in `Bool`: the left side runs the hybrid `H_{e-1}`, the right
side the hybrid `H_e`. The KEM and key-derivation reductions also draw a slot uniform in `Bool`:
the predecessor epoch `e - 1` or the target epoch `e`. Each reduction embeds its challenge at the
chosen epoch, runs the simulation of the security game stopped at the first exposure of `e`, and
complements its output bit on the right side.

This module fixes the names and the types of the four reductions; their bodies are still to be
written.
-/

@[expose] public section

namespace MLKEMBraid.Auth

open Braid

/-- The IND-CPA adversary against `P.kem` built from `A`. It draws the epoch `e`, the side and the
slot, and embeds the challenge public key, ciphertext and key at epoch `e - 1` (predecessor slot)
or `e` (target slot). Before the challenge it presamples the initial key and the joint
output-and-leak samples of every epoch before the embedded one. After the challenge it runs the
stopped simulation and complements its output on the right side. At `e = 1` the predecessor slot
is a dummy with output `false` in both worlds; for `q = 0` the whole reduction is such a dummy. -/
def kemMixReduction (P : Parameters ProbComp) {Root MacKey : Type}
    [SampleableType P.K] [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    [DecidableEq P.K] [DecidableEq P.EpochKey] [DecidableEq P.Mac]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P S irl) (q : ℕ) : P.kem.IND_CPA_Adversary := sorry

/-- The key-derivation distinguisher built from `A`, in the game `Braid.kdfContextExp`. It draws
the epoch `e`, the side and the slot, and announces the label `e - 1` (predecessor slot) or `e`
(target slot); it then receives `kdfOK u` at that label for a uniform shared secret `u`, or a
uniform epoch key. Before announcing the label it presamples the initial key and the joint
output-and-leak samples of every epoch before the label. On receipt it runs the stopped simulation
and complements its output on the right side. At `e = 1` the predecessor slot is a dummy with
output `false` in both worlds; for `q = 0` the whole reduction is such a dummy. -/
def kdfMixReduction (P : Parameters ProbComp) {Root MacKey : Type}
    [SampleableType P.K] [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    [DecidableEq P.K] [DecidableEq P.EpochKey] [DecidableEq P.Mac]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P S irl) (q : ℕ) : Braid.KDFContextAdversary P.EpochKey := sorry

/-- The secret-input distinguisher built from `A`. It draws the epoch `e` and the side. Its
challenge is the update of epoch `e - 1`, with the root `R_{e-2}` known and the update input
hidden; at `e = 1` it is the initialisation `F 1 initRoot ik`, with the initial key `ik` hidden.
In `choose` it presamples the initial key and the joint output-and-leak samples of every epoch
before `e - 1`, and returns the label and the known root. In `guess` it runs the stopped
simulation with the received pair and complements its output on the right side. For `q = 0` it is
a dummy with output `false` in both worlds. -/
def inputMixReduction (P : Parameters ProbComp) {Root MacKey : Type}
    [SampleableType P.K] [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    [DecidableEq P.K] [DecidableEq P.EpochKey] [DecidableEq P.Mac]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P S irl) (q : ℕ) : InputAdversary P Root MacKey := sorry

/-- The secret-root distinguisher built from `A`. It draws the epoch `e` and the side. Its
challenge is the update of epoch `e`, with the root `R_{e-1}` hidden and the update input `I_e`
known. In `choose` it presamples the initial key and the joint output-and-leak samples of every
epoch before `e`, and returns the label `e` and the known input `I_e`. In `guess` it runs the
stopped simulation with the received pair and complements its output on the right side. For
`q = 0` it is a dummy with output `false` in both worlds. -/
def rootMixReduction (P : Parameters ProbComp) {Root MacKey : Type}
    [SampleableType P.K] [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    [DecidableEq P.K] [DecidableEq P.EpochKey] [DecidableEq P.Mac]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P S irl) (q : ℕ) : RootAdversary P Root MacKey := sorry

end MLKEMBraid.Auth
