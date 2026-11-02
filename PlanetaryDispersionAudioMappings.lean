import Mathlib

/-!
# Planetary Dispersion — Audio mapping invariants
Based on Technical Guide, version 1.2 (October 2026), Sections 2.12–2.14.
These are properties of bounded, project-specific audio-control mappings.
They do NOT prove empirical atmospheric attenuation accuracy.
-/

namespace PDMapping

noncomputable section

-- A reusable lower/upper clamp.
def clamp (lo hi value : ℝ) : ℝ :=
  max lo (min hi value)

-- Proof 19: The clamp always returns a value within its bounds.
theorem clamp_bounds (lo hi value : ℝ) (h : lo ≤ hi) :
    lo ≤ clamp lo hi value ∧ clamp lo hi value ≤ hi := by
  constructor
  · exact le_max_left lo (min hi value)
  · exact max_le h (min_le_left hi value)

-- Earth reference value and clamp from Section 2.12.
def brightness (molarMass : ℝ) : ℝ :=
  clamp 0.7 1.3
    (Real.sqrt ((0.02897 : ℝ) / max molarMass 0.000001))

-- Proof 20: Brightness cannot leave [0.7, 1.3],
-- regardless of the molar mass supplied to this mapping.
theorem brightness_bounds (molarMass : ℝ) :
    (0.7 : ℝ) ≤ brightness molarMass ∧
    brightness molarMass ≤ (1.3 : ℝ) := by
  unfold brightness
  exact clamp_bounds 0.7 1.3 _ (by norm_num)

-- Pressure and temperature correction clamps from Section 2.14.
-- 'raw' represents the exponentiated ratio before clamping.

-- Proof 21: Pressure multiplier is bounded by [0.6, 3.0].
theorem pressure_correction_bounds (raw : ℝ) :
    (0.6 : ℝ) ≤ clamp 0.6 3.0 raw ∧
    clamp 0.6 3.0 raw ≤ (3.0 : ℝ) := by
  exact clamp_bounds 0.6 3.0 raw (by norm_num)

-- Proof 22: Temperature multiplier is bounded by [0.8, 1.3].
theorem temperature_correction_bounds (raw : ℝ) :
    (0.8 : ℝ) ≤ clamp 0.8 1.3 raw ∧
    clamp 0.8 1.3 raw ≤ (1.3 : ℝ) := by
  exact clamp_bounds 0.8 1.3 raw (by norm_num)

-- Implement the 0.1 kPa near-vacuum branch as documented.
-- rawPressure and rawTemperature are the (pre-clamp) power-law ratios.
def environmentalMultiplier
    (pressureKPa rawPressure rawTemperature : ℝ) : ℝ :=
  if pressureKPa ≤ 0.1 then 1
  else clamp 0.6 3.0 rawPressure * clamp 0.8 1.3 rawTemperature

-- Proof 23: The near-vacuum branch returns exactly 1.
theorem near_vacuum_returns_one
    (pressureKPa rawPressure rawTemperature : ℝ)
    (hnear : pressureKPa ≤ 0.1) :
    environmentalMultiplier pressureKPa rawPressure rawTemperature = 1 := by
  simp [environmentalMultiplier, hnear]

-- Proof 24: The environmental multiplier is strictly positive.
theorem environmentalMultiplier_positive
    (pressureKPa rawPressure rawTemperature : ℝ) :
    0 < environmentalMultiplier pressureKPa rawPressure rawTemperature := by
  unfold environmentalMultiplier
  split_ifs with hnear
  · norm_num
  · have hp := (pressure_correction_bounds rawPressure).1
    have ht := (temperature_correction_bounds rawTemperature).1
    have hpp : 0 < clamp 0.6 3.0 rawPressure := by linarith
    have htt : 0 < clamp 0.8 1.3 rawTemperature := by linarith
    exact mul_pos hpp htt

-- Band-weighted environmental correction:
-- C_i = Lerp(1, M_env, w_i).
def bandCorrection (environment weight : ℝ) : ℝ :=
  (1 - weight) * 1 + weight * environment

-- Proof 25: A nonnegative environmental multiplier and a
-- band weight in [0,1] yield a nonnegative correction.
theorem bandCorrection_nonnegative (environment weight : ℝ)
    (he : 0 ≤ environment)
    (hw0 : 0 ≤ weight) (hw1 : weight ≤ 1) :
    0 ≤ bandCorrection environment weight := by
  unfold bandCorrection
  have hleft : 0 ≤ 1 - weight := by linarith
  exact add_nonneg (mul_nonneg hleft (by norm_num))
    (mul_nonneg hw0 he)

-- A weighted nine-band gas profile at a selected band index.
-- profiles g band denotes the stored profile value for gas g at band.
def gasBandProfile (profiles : Fin 10 → Fin 9 → ℝ)
    (fractions : Fin 10 → ℝ) (band : Fin 9) : ℝ :=
  ∑ gas : Fin 10, fractions gas * profiles gas band

-- Proof 26: Nonnegative per-gas profiles and mole fractions
-- yield nonnegative band controls.
theorem gasBandProfile_nonnegative
    (profiles : Fin 10 → Fin 9 → ℝ)
    (fractions : Fin 10 → ℝ)
    (band : Fin 9)
    (hf : ∀ gas, 0 ≤ fractions gas)
    (hp : ∀ gas, 0 ≤ profiles gas band) :
    0 ≤ gasBandProfile profiles fractions band := by
  unfold gasBandProfile
  apply Finset.sum_nonneg
  intro gas hmem
  exact mul_nonneg (hf gas) (hp gas)

-- The final absorption control from Section 2.14.
def finalAbsorption (humidityAdjusted current native correction : ℝ) : ℝ :=
  humidityAdjusted * (current / native) * correction

-- Proof 27: Nonnegative inputs and a positive baseline yield
-- a nonnegative final control. This is NOT a dB/m prediction.
theorem finalAbsorption_nonnegative
    (humidityAdjusted current native correction : ℝ)
    (ha : 0 ≤ humidityAdjusted)
    (hc : 0 ≤ current)
    (hn : 0 < native)
    (hk : 0 ≤ correction) :
    0 ≤ finalAbsorption humidityAdjusted current native correction := by
  unfold finalAbsorption
  exact mul_nonneg
    (mul_nonneg ha (div_nonneg hc (le_of_lt hn))) hk

end
end PDMapping
#print axioms PDMapping.environmentalMultiplier_positive
