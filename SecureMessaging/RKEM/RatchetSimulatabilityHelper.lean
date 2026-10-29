/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SecureMessaging.RKEM.Defs
import ToVCVio.OracleComp.Constructions.SampleableType

/-!
# Ratchet Simulatability — Perfect Simulation

Generic lemmas for perfect (`ε = 0`) ratchet simulatability ([TripleRatchet, Def. 5.5]), stated
for an arbitrary RKEM over `ProbComp`, randomness-leak package and simulators.

Each simulatability property is a bit-guessing experiment between a real distribution
`D_{P,0}` and a simulated one `D_{P,1}`. If the two coincide for every public parameter, the
guess is independent of the bit, so every distinguisher has advantage exactly `0`
(`ToVCVio.prEvent_true_bitGuess_eq_half`). A construction proving the six distribution
equalities (three properties, two parties) thus gets `RatchetSimulatable 0` from
`ratchetSimulatable_zero_of_evalDistEq`.

[REFERENCES]

- [TripleRatchet] Dodis, Jost, Katsumata, Prest, Schmidt.
  *Triple Ratchet: A Bandwidth Efficient Hybrid-Secure Signal Protocol.*
  EUROCRYPT 2025, https://eprint.iacr.org/2025/078.pdf
-/

open ToVCVio

namespace RKEMScheme

variable {Par EK DK CT K : Type} (rkem : RKEMScheme ProbComp Par EK DK CT K)
  {leak : rkem.RandLeak} (sim : rkem.RatchetSimulator leak)

/-- If, for both parties, the simulated base-key distribution `D^KeyBaseSim_{P,1}` equals the
real `D^KeyBaseSim_{P,0}`, then `Adv^{KeyBaseSim}` is `0` against every pair of
distinguishers. -/
theorem keyBaseSimAdvantage_eq_zero_of_evalDistEq
    (hA : ∀ par, rkem.keyBaseSimDistA sim par true =ᵈ rkem.keyBaseSimDistA sim par false)
    (hB : ∀ par, rkem.keyBaseSimDistB sim par true =ᵈ rkem.keyBaseSimDistB sim par false)
    (adversaryA adversaryB : KeyBaseSimAdversary Par EK DK) :
    rkem.keyBaseSimAdvantage sim adversaryA adversaryB = 0 := by
  unfold RKEMScheme.keyBaseSimAdvantage RKEMScheme.keyBaseSimAdvantageA
    RKEMScheme.keyBaseSimAdvantageB RKEMScheme.keyBaseSimExpA RKEMScheme.keyBaseSimExpB
  rw [prEvent_true_bitGuess_eq_half _ _ _ hA, prEvent_true_bitGuess_eq_half _ _ _ hB]
  simp

/-- If, for both parties, the simulated updated-key distribution `D^KeyUpdSim_{P,1}` equals the
real `D^KeyUpdSim_{P,0}`, then `Adv^{KeyUpdSim}` is `0` against every pair of
distinguishers. -/
theorem keyUpdSimAdvantage_eq_zero_of_evalDistEq
    (hA : ∀ par, rkem.keyUpdSimDistA sim par true =ᵈ rkem.keyUpdSimDistA sim par false)
    (hB : ∀ par, rkem.keyUpdSimDistB sim par true =ᵈ rkem.keyUpdSimDistB sim par false)
    (adversaryA adversaryB :
      KeyUpdSimAdversary Par EK DK CT K sim.Aux leak.KeygenRand leak.EncRand) :
    rkem.keyUpdSimAdvantage sim adversaryA adversaryB = 0 := by
  unfold RKEMScheme.keyUpdSimAdvantage RKEMScheme.keyUpdSimAdvantageA
    RKEMScheme.keyUpdSimAdvantageB RKEMScheme.keyUpdSimExpA RKEMScheme.keyUpdSimExpB
  rw [prEvent_true_bitGuess_eq_half _ _ _ hA, prEvent_true_bitGuess_eq_half _ _ _ hB]
  simp

/-- If, for both parties, the simulated ciphertext distribution `D^CtxtSim_{P,1}` equals the
real `D^CtxtSim_{P,0}`, then `Adv^{CtxtSim}` is `0` against every pair of distinguishers. -/
theorem ctxtSimAdvantage_eq_zero_of_evalDistEq
    (hA : ∀ par, rkem.ctxtSimDistA sim par true =ᵈ rkem.ctxtSimDistA sim par false)
    (hB : ∀ par, rkem.ctxtSimDistB sim par true =ᵈ rkem.ctxtSimDistB sim par false)
    (adversaryA adversaryB : CtxtSimAdversary Par EK DK CT K sim.Aux leak.KeygenRand) :
    rkem.ctxtSimAdvantage sim adversaryA adversaryB = 0 := by
  unfold RKEMScheme.ctxtSimAdvantage RKEMScheme.ctxtSimAdvantageA
    RKEMScheme.ctxtSimAdvantageB RKEMScheme.ctxtSimExpA RKEMScheme.ctxtSimExpB
  rw [prEvent_true_bitGuess_eq_half _ _ _ hA, prEvent_true_bitGuess_eq_half _ _ _ hB]
  simp

/-- **Perfect ratchet simulatability** (Def. 5.5 with `ε = 0`): if the simulators `sim` make the
real and simulated distributions of base-key, updated-key and ciphertext simulatability coincide,
for both parties and every public parameter, then `rkem` is `0`-ratchet simulatable with respect
to `leak`, witnessed by `sim`. -/
theorem ratchetSimulatable_zero_of_evalDistEq
    (hBaseA : ∀ par,
      rkem.keyBaseSimDistA sim par true =ᵈ rkem.keyBaseSimDistA sim par false)
    (hBaseB : ∀ par,
      rkem.keyBaseSimDistB sim par true =ᵈ rkem.keyBaseSimDistB sim par false)
    (hUpdA : ∀ par,
      rkem.keyUpdSimDistA sim par true =ᵈ rkem.keyUpdSimDistA sim par false)
    (hUpdB : ∀ par,
      rkem.keyUpdSimDistB sim par true =ᵈ rkem.keyUpdSimDistB sim par false)
    (hCtxtA : ∀ par,
      rkem.ctxtSimDistA sim par true =ᵈ rkem.ctxtSimDistA sim par false)
    (hCtxtB : ∀ par,
      rkem.ctxtSimDistB sim par true =ᵈ rkem.ctxtSimDistB sim par false) :
    rkem.RatchetSimulatable (leak := leak) 0 :=
  ⟨sim, fun baseA baseB updA updB ctxtA ctxtB =>
    ⟨(rkem.keyBaseSimAdvantage_eq_zero_of_evalDistEq sim hBaseA hBaseB baseA baseB).le,
      (rkem.keyUpdSimAdvantage_eq_zero_of_evalDistEq sim hUpdA hUpdB updA updB).le,
      (rkem.ctxtSimAdvantage_eq_zero_of_evalDistEq sim hCtxtA hCtxtB ctxtA ctxtB).le⟩⟩

end RKEMScheme
