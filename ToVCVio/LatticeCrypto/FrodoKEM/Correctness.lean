/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Basic
public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Deterministic
public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Sampling
public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.IndepNoise
public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.FailureProbability
public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Numerical
public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.RandomOracle.Correctness
public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.RandomOracle.Numerical

/-!
# FrodoKEM correctness

A decapsulation failure occurs when honest decapsulation returns a different shared secret
from the one that encapsulation produced. In the random-oracle model, a table of uniformly random
answers replaces SHAKE. In this model, the failure probability, averaged over the table, is at
most `2^-138.7`, `2^-199.6` and `2^-252.5` for sizes 640, 976 and 1344. `[CiC25]` gives the
same values (Table 4, §6.2). The bound holds for FrodoKEM and for eFrodoKEM.

The final theorem is `FrodoKEM.ROM.honestFailureProb_tenth_power_le`. The proofs are in the files
under `Correctness/`, and the FrodoKEM chapter of the docs explains each step.

## Scope

The bound is an average over the random table. It does not apply to concrete SHAKE, to one fixed
table, or to many encapsulations with one key.

## References

* `[CiC25]`, Glabush, Longa, Naehrig, Peikert, Stebila and Virdia, *FrodoKEM: A
  CCA-Secure Learning With Errors Key Encapsulation Mechanism*, IACR
  Communications in Cryptology 2:3, <https://cic.iacr.org/p/2/3/25>.
-/
