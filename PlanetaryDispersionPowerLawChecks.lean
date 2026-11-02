import Mathlib

/-!
# Planetary Dispersion: complete environmental power-law definitions

Technical Guide v1.2, Section 2.14.
These proofs concern mathematical properties of the exact encoded formulas,
not their empirical calibration or correspondence to Unreal Blueprints.
-/

namespace PDPowerLaw

noncomputable section

def clamp (lo hi value : ℝ) : ℝ :=
  max lo (min hi value)

theorem clamp_bounds (lo hi value : ℝ) (h : lo ≤ hi) :
    lo ≤ clamp lo hi value ∧ clamp lo hi value ≤ hi := by
  constructor
  · exact le_max_left lo (min hi value)
  · exact max_le h (min_le_left hi value)

-- rP = 101.325 / max(PkPa, 0.1)
-- MP = clamp(rP ^ 0.25, 0.6, 3.0)
def pressureRaw (pressureKPa : ℝ) : ℝ :=
  (101.325 / max pressureKPa 0.1) ^ (0.25 : ℝ)

def pressureMultiplier (pressureKPa : ℝ) : ℝ :=
  clamp 0.6 3.0 (pressureRaw pressureKPa)

-- TK = TC + 273.15
-- MT = clamp((293.15 / max(TK, 1.0)) ^ 0.15, 0.8, 1.3)
def temperatureRaw (temperatureC : ℝ) : ℝ :=
  (293.15 / max (temperatureC + 273.15) 1.0) ^ (0.15 : ℝ)

def temperatureMultiplier (temperatureC : ℝ) : ℝ :=
  clamp 0.8 1.3 (temperatureRaw temperatureC)

-- Menv = 1 when PkPa <= 0.1; otherwise MP * MT.
def environmentalExact (pressureKPa temperatureC : ℝ) : ℝ :=
  if pressureKPa ≤ 0.1 then 1
  else pressureMultiplier pressureKPa * temperatureMultiplier temperatureC

-- The real-power expressions are strictly positive because their
-- denominators are guarded away from zero.
theorem pressureRaw_positive (pressureKPa : ℝ) :
    0 < pressureRaw pressureKPa := by
  unfold pressureRaw
  have hd : (0 : ℝ) < max pressureKPa 0.1 :=
    lt_of_lt_of_le (by norm_num) (le_max_right pressureKPa 0.1)
  exact Real.rpow_pos_of_pos (div_pos (by norm_num) hd) _

theorem temperatureRaw_positive (temperatureC : ℝ) :
    0 < temperatureRaw temperatureC := by
  unfold temperatureRaw
  have hd : (0 : ℝ) < max (temperatureC + 273.15) 1.0 :=
    lt_of_lt_of_le (by norm_num) (le_max_right (temperatureC + 273.15) 1.0)
  exact Real.rpow_pos_of_pos (div_pos (by norm_num) hd) _

-- The exact near-vacuum branch returns 1 by construction.
theorem near_vacuum_exact (pressureKPa temperatureC : ℝ)
    (h : pressureKPa ≤ 0.1) :
    environmentalExact pressureKPa temperatureC = 1 := by
  simp [environmentalExact, h]

-- The complete documented environmental function remains bounded.
theorem environmentalExact_bounds (pressureKPa temperatureC : ℝ) :
    (0.48 : ℝ) ≤ environmentalExact pressureKPa temperatureC ∧
    environmentalExact pressureKPa temperatureC ≤ (3.9 : ℝ) := by
  unfold environmentalExact
  split_ifs with h
  · constructor <;> norm_num
  · obtain ⟨hpLo, hpHi⟩ :=
      clamp_bounds 0.6 3.0 (pressureRaw pressureKPa) (by norm_num)
    obtain ⟨htLo, htHi⟩ :=
      clamp_bounds 0.8 1.3 (temperatureRaw temperatureC) (by norm_num)
    constructor
    · calc
        (0.48 : ℝ) = 0.6 * 0.8 := by norm_num
        _ ≤ clamp 0.6 3.0 (pressureRaw pressureKPa) *
              clamp 0.8 1.3 (temperatureRaw temperatureC) := by
          exact mul_le_mul hpLo htLo (by norm_num) (by linarith)
    · calc
        clamp 0.6 3.0 (pressureRaw pressureKPa) *
            clamp 0.8 1.3 (temperatureRaw temperatureC) ≤
            (3.0 : ℝ) * 1.3 := by
          exact mul_le_mul hpHi htHi (by linarith) (by norm_num)
        _ = 3.9 := by norm_num

end
end PDPowerLaw

#print axioms PDPowerLaw.environmentalExact_bounds
