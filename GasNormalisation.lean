
import Mathlib

/-!
# Planetary Dispersion: Ten-Gas Normalisation

Formalisation of Technical Guide Section 2.11.

Gas index:
0 = CO2
1 = N2
2 = CH4
3 = O2
4 = Ar
5 = H2
6 = He
7 = H2O
8 = NH3
9 = SO2
-/

-- Sum the amounts of all ten gases.
def pdTotal (amounts : Fin 10 → ℝ) : ℝ :=
  ∑ i : Fin 10, amounts i

-- Apply the documented normalisation rule.
-- Invalid totals return zero.
noncomputable def pdFraction (amounts : Fin 10 → ℝ)
    (i : Fin 10) : ℝ :=
  if pdTotal amounts > (1 / 1000000 : ℝ) then
    amounts i / pdTotal amounts
  else
    0

-- PROOF 1
-- Valid normalised fractions sum to exactly 1.

theorem pd_fractions_sum_to_one
    (amounts : Fin 10 → ℝ)
    (hValid : pdTotal amounts >
      (1 / 1000000 : ℝ)) :
    (∑ i : Fin 10, pdFraction amounts i) = 1 := by
  have hNonzero : pdTotal amounts ≠ 0 := by
    linarith
  simp only [pdFraction, if_pos hValid]
  rw [← Finset.sum_div]
  change pdTotal amounts / pdTotal amounts = 1
  exact div_self hNonzero

-- PROOF 2
-- Nonnegative inputs produce nonnegative fractions.

theorem pd_fractions_nonnegative
    (amounts : Fin 10 → ℝ)
    (hNonnegative : ∀ i, 0 ≤ amounts i)
    (i : Fin 10) :
    0 ≤ pdFraction amounts i := by
  unfold pdFraction
  split_ifs with hValid
  · have hDenom : 0 ≤ pdTotal amounts := by
      linarith
    exact div_nonneg (hNonnegative i) hDenom
  · norm_num

-- PROOF 3
-- An invalid total returns zero for every gas.

theorem pd_invalid_total_returns_zero
    (amounts : Fin 10 → ℝ)
    (hInvalid : pdTotal amounts ≤
      (1 / 1000000 : ℝ))
    (i : Fin 10) :
    pdFraction amounts i = 0 := by
  unfold pdFraction
  split_ifs with hValid
  · linarith
  · rfl

-- STEP 4: Mean molar mass
-- Constants from Planetary Dispersion Technical Guide,
-- Section 2.2, in kg/mol.

def pdMolarMass (i : Fin 10) : ℝ :=
  match i.val with
  | 0 => 0.044010  -- CO2
  | 1 => 0.028014  -- N2
  | 2 => 0.016043  -- CH4
  | 3 => 0.031998  -- O2
  | 4 => 0.039948  -- Ar
  | 5 => 0.002016  -- H2
  | 6 => 0.004003  -- He
  | 7 => 0.018015  -- H2O
  | 8 => 0.017031  -- NH3
  | _ => 0.064063  -- SO2

-- PROOF 4
-- Every gas in the model has positive molar mass.

theorem pd_molar_mass_positive
    (i : Fin 10) :
    0 < pdMolarMass i := by
  fin_cases i <;> norm_num [pdMolarMass]

-- Calculate mixture mean molar mass.

noncomputable def pdMeanMolarMass
    (amounts : Fin 10 → ℝ) : ℝ :=
  ∑ i : Fin 10,
    pdFraction amounts i * pdMolarMass i

-- PROOF 5
-- Nonnegative gas amounts cannot produce
-- a negative mean molar mass.

theorem pd_mean_molar_mass_nonnegative
    (amounts : Fin 10 → ℝ)
    (hNonnegative : ∀ i, 0 ≤ amounts i) :
    0 ≤ pdMeanMolarMass amounts := by
  unfold pdMeanMolarMass
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    (pd_fractions_nonnegative amounts hNonnegative i)
    (le_of_lt (pd_molar_mass_positive i))

-- STEP 6: Mean molar mass bounds
-- Section 2.3 of the Technical Guide

-- PROOF 6
-- Each gas has a molar mass between
-- hydrogen and sulfur dioxide.

theorem pd_molar_mass_bounds
    (i : Fin 10) :
    (0.002016 : ℝ) ≤ pdMolarMass i ∧
    pdMolarMass i ≤ (0.064063 : ℝ) := by
  fin_cases i <;> norm_num [pdMolarMass]

-- PROOF 7
-- Any valid nonnegative mixture has a
-- mean molar mass within these bounds.


-- PROOF 7
-- A valid ten-gas mixture must have a mean
-- molar mass between 0.002016 and 0.064063 kg/mol.

theorem pd_mean_molar_mass_bounds
    (amounts : Fin 10 → ℝ)
    (hNonnegative : ∀ i, 0 ≤ amounts i)
    (hValid : pdTotal amounts >
      (1 / 1000000 : ℝ)) :
    (0.002016 : ℝ) ≤ pdMeanMolarMass amounts ∧
    pdMeanMolarMass amounts ≤ (0.064063 : ℝ) := by

  have hSum :
      (∑ i : Fin 10, pdFraction amounts i) = 1 :=
    pd_fractions_sum_to_one amounts hValid

  have hFrac :
      ∀ i : Fin 10, 0 ≤ pdFraction amounts i :=
    fun i =>
      pd_fractions_nonnegative amounts hNonnegative i

  -- Every weighted gas mass is at least
  -- its fraction multiplied by hydrogen's mass.

  have hLower :
      (∑ i : Fin 10,
        pdFraction amounts i * (0.002016 : ℝ)) ≤
      pdMeanMolarMass amounts := by
    unfold pdMeanMolarMass
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (pd_molar_mass_bounds i).1 (hFrac i)

  -- Every weighted gas mass is at most
  -- its fraction multiplied by SO2's mass.

  have hUpper :
      pdMeanMolarMass amounts ≤
      (∑ i : Fin 10,
        pdFraction amounts i * (0.064063 : ℝ)) := by
    unfold pdMeanMolarMass
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (pd_molar_mass_bounds i).2 (hFrac i)

  -- The fractions sum to 1, so the bounds
  -- reduce to the lightest and heaviest gas.

  rw [← Finset.sum_mul, hSum, one_mul] at hLower
  rw [← Finset.sum_mul, hSum, one_mul] at hUpper

  exact ⟨hLower, hUpper⟩
#print axioms pd_mean_molar_mass_bounds
