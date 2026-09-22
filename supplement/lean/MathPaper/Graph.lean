import MathPaper.Nonperiodic

namespace MathPaper

abbrev State := ℤ × ℤ

def LegalState (M K : ℕ) (v : State) : Prop :=
  0 ≤ v.1 ∧ v.1 < M ∧ Int.gcd v.1 M = 1 ∧ 0 ≤ v.2 ∧ v.2 < K

/-- All arithmetic in E1--E3 is signed integer arithmetic. -/
def Edge (a b M K : ℕ) (u v : State) (e : ℤ) : Prop :=
  1 - (b : ℤ) ≤ e ∧ e ≤ (a : ℤ) - 1 ∧
  (M : ℤ) ∣ (b : ℤ) * v.1 - (a : ℤ) * u.1 - e ∧
  (a : ℤ) * u.2 - (b : ℤ) * (v.2 + 1) < e * K ∧
  e * K < (a : ℤ) * (u.2 + 1) - (b : ℤ) * v.2

noncomputable def orbitState (a b M K : ℕ) (ξ : ℝ) (n : ℕ) : State :=
  (floorOrbit a b ξ n % (M : ℤ), ⌊(K : ℝ) * fractionOrbit a b ξ n⌋)

theorem orbit_edge (a b M K : ℕ) (ha : 0 < a) (hb : 0 < b)
    (ξ : ℝ) (n : ℕ) :
    Edge a b M K (orbitState a b M K ξ n) (orbitState a b M K ξ (n + 1))
      (carry a b ξ n) := by
  obtain ⟨hl, hu⟩ := carry_bounds a b ha hb ξ n
  refine ⟨hl, hu, ?_, ?_, ?_⟩
  · unfold orbitState carry
    dsimp
    refine ⟨(a : ℤ) * (floorOrbit a b ξ n / (M : ℤ)) -
      (b : ℤ) * (floorOrbit a b ξ (n + 1) / (M : ℤ)), ?_⟩
    simp only [Int.emod_def]
    ring
  all_goals
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    have h1 := Int.floor_le ((K : ℝ) * fractionOrbit a b ξ n)
    have h2 := Int.lt_floor_add_one ((K : ℝ) * fractionOrbit a b ξ n)
    have h3 := Int.floor_le ((K : ℝ) * fractionOrbit a b ξ (n + 1))
    have h4 := Int.lt_floor_add_one ((K : ℝ) * fractionOrbit a b ξ (n + 1))
    have hc := congrArg (fun x : ℝ => x * (K : ℝ)) (carry_fraction a b hb ξ n)
    dsimp only at hc
    have h1a := mul_le_mul_of_nonneg_left h1 ha'.le
    have h2a := mul_lt_mul_of_pos_left h2 ha'
    have h3b := mul_le_mul_of_nonneg_left h3 hb'.le
    have h4b := mul_lt_mul_of_pos_left h4 hb'
    unfold orbitState
    dsimp
    first
    | exact_mod_cast (show (a : ℝ) * (⌊(K : ℝ) * fractionOrbit a b ξ n⌋ : ℝ) -
        (b : ℝ) * ((⌊(K : ℝ) * fractionOrbit a b ξ (n + 1)⌋ : ℝ) + 1) <
        (carry a b ξ n : ℝ) * K by nlinarith)
    | exact_mod_cast (show (carry a b ξ n : ℝ) * K <
        (a : ℝ) * ((⌊(K : ℝ) * fractionOrbit a b ξ n⌋ : ℝ) + 1) -
        (b : ℝ) * (⌊(K : ℝ) * fractionOrbit a b ξ (n + 1)⌋ : ℝ) by nlinarith)

def Refine (f : ℕ) (U : Set State) : Set State :=
  {v | ∃ u ∈ U, ∃ i : ℤ, 0 ≤ i ∧ i < f ∧ v = (u.1, (f : ℤ) * u.2 + i)}

theorem floor_refinement_bounds (f : ℕ) (hf : 0 < f) (x : ℝ) :
    (f : ℤ) * ⌊x⌋ ≤ ⌊(f : ℝ) * x⌋ ∧
    ⌊(f : ℝ) * x⌋ < (f : ℤ) * ⌊x⌋ + f := by
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  constructor
  · apply Int.le_floor.mpr
    push_cast
    nlinarith
  · apply Int.floor_lt.mpr
    push_cast
    nlinarith

theorem refined_state_mem (a b M K f : ℕ) (hf : 0 < f) (ξ : ℝ) (n : ℕ)
    (U : Set State) (hU : orbitState a b M K ξ n ∈ U) :
    orbitState a b M (f * K) ξ n ∈ Refine f U := by
  have hbound := floor_refinement_bounds f hf ((K : ℝ) * fractionOrbit a b ξ n)
  refine ⟨orbitState a b M K ξ n, hU,
    ⌊(f : ℝ) * ((K : ℝ) * fractionOrbit a b ξ n)⌋ -
      (f : ℤ) * ⌊(K : ℝ) * fractionOrbit a b ξ n⌋, ?_, ?_, ?_⟩
  · omega
  · omega
  · unfold orbitState
    push_cast
    congr 1
    simp only [mul_assoc]
    ring

end MathPaper
