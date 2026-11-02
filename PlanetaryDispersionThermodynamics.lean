import Mathlib

/-!
# Planetary Dispersion — Thermodynamic checks
Based on Technical Guide, version 1.2 (October 2026), Sections 2.2–2.10.
All values are treated as exact real numbers in these proofs.
Theorems validate the encoded ideal-gas model, not Unreal Engine runtime outputs
or the physical fidelity of extreme planetary atmospheres.
-/

namespace PDVerification

noncomputable section

-- The model's universal gas constant in J/(mol·K).
def gasR : ℝ := 8.314463

-- Ten fixed molar Cp values in J/(mol·K), in documented gas order.
-- 0 CO2, 1 N2, 2 CH4, 3 O2, 4 Ar,
-- 5 H2, 6 He, 7 H2O, 8 NH3, 9 SO2.
def gasCp (i : Fin 10) : ℝ :=
  match i.val with
  | 0 => 37.14
  | 1 => 29.12
  | 2 => 35.69
  | 3 => 29.38
  | 4 => 20.79
  | 5 => 28.84
  | 6 => 20.79
  | 7 => 33.58
  | 8 => 35.70
  | _ => 39.87

-- Proof 8: Each stored Cp constant is in the documented range.
theorem gasCp_bounds (i : Fin 10) :
    (20.79 : ℝ) ≤ gasCp i ∧ gasCp i ≤ (39.87 : ℝ) := by
  fin_cases i <;> norm_num [gasCp]

-- x represents nonnegative mole fractions that add to one.
def cpMix (x : Fin 10 → ℝ) : ℝ :=
  ∑ i : Fin 10, x i * gasCp i

-- Proof 9: A normalized Cp mixture is bounded by its components.
theorem cpMix_bounds (x : Fin 10 → ℝ)
    (hx : ∀ i, 0 ≤ x i)
    (hsum : (∑ i : Fin 10, x i) = 1) :
    (20.79 : ℝ) ≤ cpMix x ∧ cpMix x ≤ (39.87 : ℝ) := by
  have hlo :
      (∑ i : Fin 10, x i * (20.79 : ℝ)) ≤ cpMix x := by
    unfold cpMix
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (gasCp_bounds i).1 (hx i)
  have hhi :
      cpMix x ≤ (∑ i : Fin 10, x i * (39.87 : ℝ)) := by
    unfold cpMix
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (gasCp_bounds i).2 (hx i)
  rw [← Finset.sum_mul, hsum, one_mul] at hlo
  rw [← Finset.sum_mul, hsum, one_mul] at hhi
  exact ⟨hlo, hhi⟩

-- Cp-Cv=R for the ideal-gas model.
def cvMix (cp : ℝ) : ℝ := cp - gasR

-- Proof 10: Every normalized Cp mixture has Cv > 0.0001,
-- so the documented gamma guard takes its normal calculation path.
theorem cvMix_above_guard (x : Fin 10 → ℝ)
    (hx : ∀ i, 0 ≤ x i)
    (hsum : (∑ i : Fin 10, x i) = 1) :
    (0.0001 : ℝ) < cvMix (cpMix x) := by
  have hmin := (cpMix_bounds x hx hsum).1
  unfold cvMix gasR
  linarith

-- Gamma is the Cp/Cv heat-capacity ratio.
def gammaMix (cp : ℝ) : ℝ := cp / cvMix cp

-- Proof 11: For this gas table, gamma is greater than 1.
theorem gammaMix_gt_one (x : Fin 10 → ℝ)
    (hx : ∀ i, 0 ≤ x i)
    (hsum : (∑ i : Fin 10, x i) = 1) :
    1 < gammaMix (cpMix x) := by
  have hv : 0 < cvMix (cpMix x) := by
    have h := cvMix_above_guard x hx hsum
    linarith
  have hr : 0 < gasR := by
    norm_num [gasR]
  unfold gammaMix
  apply (lt_div_iff₀ hv).2
  dsimp [cvMix]
  nlinarith

-- Ideal-gas mass density: rho = P M / (R T).
def density (pressure molarMass temperature : ℝ) : ℝ :=
  pressure * molarMass / (gasR * temperature)

-- Proof 12: Positive pressure, molar mass and absolute temperature
-- yield positive mass density.
theorem density_positive (pressure molarMass temperature : ℝ)
    (hp : 0 < pressure)
    (hm : 0 < molarMass)
    (ht : 0 < temperature) :
    0 < density pressure molarMass temperature := by
  unfold density
  apply div_pos (mul_pos hp hm)
  exact mul_pos (by norm_num [gasR]) ht

-- Ideal-gas sound speed: c = sqrt(gamma R T / M).
def soundSpeed (gamma temperature molarMass : ℝ) : ℝ :=
  Real.sqrt (gamma * gasR * temperature / molarMass)

-- Proof 13: The square of calculated speed equals the sound-speed
-- radicand under the standard positivity assumptions.
theorem soundSpeed_squared (gamma temperature molarMass : ℝ)
    (hg : 0 ≤ gamma)
    (ht : 0 ≤ temperature)
    (hm : 0 < molarMass) :
    soundSpeed gamma temperature molarMass ^ 2 =
      gamma * gasR * temperature / molarMass := by
  unfold soundSpeed
  apply Real.sq_sqrt
  apply div_nonneg
  · exact mul_nonneg
      (mul_nonneg hg (le_of_lt (by norm_num [gasR] : 0 < gasR))) ht
  · exact le_of_lt hm

-- Proof 14: Positive gamma, temperature and molar mass give c > 0.
theorem soundSpeed_positive (gamma temperature molarMass : ℝ)
    (hg : 0 < gamma)
    (ht : 0 < temperature)
    (hm : 0 < molarMass) :
    0 < soundSpeed gamma temperature molarMass := by
  unfold soundSpeed
  apply Real.sqrt_pos.2
  apply div_pos
  · exact mul_pos (mul_pos hg (by norm_num [gasR])) ht
  · exact hm

-- Characteristic acoustic impedance of a propagation medium.
def impedance (rho speed : ℝ) : ℝ := rho * speed

-- Proof 15: Positive density and sound speed give positive impedance.
theorem impedance_positive (rho speed : ℝ)
    (hrho : 0 < rho) (hspeed : 0 < speed) :
    0 < impedance rho speed := by
  exact mul_pos hrho hspeed

-- Proof 16: The impedance reference ratio factors into
-- the density ratio multiplied by the sound-speed ratio.
theorem impedance_ratio_factorization
    (rho speed rhoRef speedRef : ℝ)
    (hr : rhoRef ≠ 0) (hc : speedRef ≠ 0) :
    impedance rho speed / impedance rhoRef speedRef =
      (rho / rhoRef) * (speed / speedRef) := by
  unfold impedance
  have hprod : rhoRef * speedRef ≠ 0 := mul_ne_zero hr hc
  field_simp [hr, hc, hprod]
  <;> ring

-- Travel time in a homogeneous medium: t = distance / speed.
def travelTime (distance speed : ℝ) : ℝ := distance / speed

-- Proof 17: Nonnegative distance and positive speed give
-- a nonnegative modeled propagation time.
theorem travelTime_nonnegative (distance speed : ℝ)
    (hd : 0 ≤ distance) (hc : 0 < speed) :
    0 ≤ travelTime distance speed := by
  exact div_nonneg hd (le_of_lt hc)

-- Proof 18: The widget's pressure and temperature conversions
-- are algebraically consistent with their documented units.
theorem widget_unit_conversion (tempC pressureKPa : ℝ) :
    (tempC + 273.15) - 273.15 = tempC ∧
    (pressureKPa * 1000) / 1000 = pressureKPa := by
  constructor
  · ring
  · ring

end
end PDVerification
#print axioms PDVerification.cpMix_bounds
