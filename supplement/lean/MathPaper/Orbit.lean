import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-! Real floor orbits and signed, zero-indexed carries. -/
namespace MathPaper

noncomputable section

def orbit (a b : ℕ) (ξ : ℝ) (n : ℕ) : ℝ := ξ * ((a : ℝ) / b) ^ n

def floorOrbit (a b : ℕ) (ξ : ℝ) (n : ℕ) : ℤ := ⌊orbit a b ξ n⌋

def fractionOrbit (a b : ℕ) (ξ : ℝ) (n : ℕ) : ℝ :=
  orbit a b ξ n - floorOrbit a b ξ n

def carry (a b : ℕ) (ξ : ℝ) (n : ℕ) : ℤ :=
  (b : ℤ) * floorOrbit a b ξ (n + 1) - (a : ℤ) * floorOrbit a b ξ n

def EventuallyPeriodic {α : Type*} (s : ℕ → α) : Prop :=
  ∃ N L : ℕ, 0 < L ∧ ∀ n, N ≤ n → s (n + L) = s n

def TendsToInfinity (Q : ℕ → ℤ) : Prop :=
  ∀ T : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → T < Q n

theorem fractionOrbit_nonneg (a b : ℕ) (ξ : ℝ) (n : ℕ) :
    0 ≤ fractionOrbit a b ξ n := by
  exact sub_nonneg.mpr (Int.floor_le _)

theorem fractionOrbit_lt_one (a b : ℕ) (ξ : ℝ) (n : ℕ) :
    fractionOrbit a b ξ n < 1 := by
  have h := Int.lt_floor_add_one (orbit a b ξ n)
  unfold fractionOrbit floorOrbit
  linarith

theorem floorOrbit_nonneg (a b : ℕ) (ξ : ℝ) (hξ : 0 ≤ ξ) (n : ℕ) :
    0 ≤ floorOrbit a b ξ n := by
  apply Int.floor_nonneg.mpr
  exact mul_nonneg hξ (pow_nonneg (div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)) n)

theorem orbit_step (a b : ℕ) (hb : 0 < b) (ξ : ℝ) (n : ℕ) :
    (b : ℝ) * orbit a b ξ (n + 1) = (a : ℝ) * orbit a b ξ n := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
  unfold orbit
  rw [pow_succ]
  field_simp

theorem carry_fraction (a b : ℕ) (hb : 0 < b) (ξ : ℝ) (n : ℕ) :
    (carry a b ξ n : ℝ) =
      (a : ℝ) * fractionOrbit a b ξ n - (b : ℝ) * fractionOrbit a b ξ (n + 1) := by
  have h := orbit_step a b hb ξ n
  unfold carry fractionOrbit
  push_cast
  nlinarith

theorem carry_bounds (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (ξ : ℝ) (n : ℕ) :
    1 - (b : ℤ) ≤ carry a b ξ n ∧ carry a b ξ n ≤ (a : ℤ) - 1 := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hn := fractionOrbit_nonneg a b ξ n
  have hn' := fractionOrbit_lt_one a b ξ n
  have hs := fractionOrbit_nonneg a b ξ (n + 1)
  have hs' := fractionOrbit_lt_one a b ξ (n + 1)
  have hc := carry_fraction a b hb ξ n
  have hlow : -(b : ℝ) < (carry a b ξ n : ℝ) := by nlinarith
  have hupp : (carry a b ξ n : ℝ) < (a : ℝ) := by nlinarith
  have hlow' : -(b : ℤ) < carry a b ξ n := by exact_mod_cast hlow
  have hupp' : carry a b ξ n < (a : ℤ) := by exact_mod_cast hupp
  omega

theorem carry_recurrence (a b : ℕ) (ξ : ℝ) (n : ℕ) :
    (b : ℤ) * floorOrbit a b ξ (n + 1) =
      (a : ℤ) * floorOrbit a b ξ n + carry a b ξ n := by
  unfold carry
  ring

theorem floor_orbit_eventually_gt (a b : ℕ) (hab : b < a) (hb : 0 < b)
    (ξ : ℝ) (hξ : 0 < ξ) : TendsToInfinity (floorOrbit a b ξ) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hab' : (b : ℝ) < a := by exact_mod_cast hab
  have hr : (1 : ℝ) < (a : ℝ) / b := (one_lt_div hb').mpr hab'
  intro T
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (((T : ℝ) + 1) / ξ) hr
  refine ⟨N, fun n hn => ?_⟩
  have hp : ((a : ℝ) / b) ^ N ≤ ((a : ℝ) / b) ^ n :=
    pow_le_pow_right₀ (le_of_lt hr) hn
  have hx : (T : ℝ) + 1 < orbit a b ξ n := by
    unfold orbit
    have ht := (div_lt_iff₀ hξ).mp (lt_of_lt_of_le hN hp)
    nlinarith
  have hf := Int.lt_floor_add_one (orbit a b ξ n)
  have hT : (T : ℝ) < (floorOrbit a b ξ n : ℝ) := by
    unfold floorOrbit
    linarith
  exact_mod_cast hT

end
end MathPaper
