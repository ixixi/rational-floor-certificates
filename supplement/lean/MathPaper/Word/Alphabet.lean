import MathPaper.Orbit

/-! The carry alphabets forced by coprimality with the modulus (audit-02 §9.1
and §10.1; manuscript Lemmas 23–24). These are the (H𝒞) hypotheses of the
word-labelled finite success theorem for the two bases. -/
namespace MathPaper

theorem odd_of_gcd_even_modulus (Q : ℤ) (M : ℕ) (hM : 2 ∣ M)
    (h : Int.gcd Q M = 1) : Q % 2 = 1 := by
  by_contra hodd
  have h2 : ((2 : ℕ) : ℤ) ∣ Q := Int.dvd_of_emod_eq_zero (by push_cast; omega)
  have h2M : ((2 : ℕ) : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.mpr hM
  have h21 : (2 : ℕ) ∣ 1 := by
    have := Int.dvd_gcd h2 h2M
    rwa [h] at this
  omega

theorem not_five_dvd_of_gcd (Q : ℤ) (M : ℕ) (hM : 5 ∣ M) (h : Int.gcd Q M = 1) :
    Q % 5 ≠ 0 := by
  intro h5
  have h5' : ((5 : ℕ) : ℤ) ∣ Q := Int.dvd_of_emod_eq_zero (by push_cast; omega)
  have h5M : ((5 : ℕ) : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.mpr hM
  have h51 : (5 : ℕ) ∣ 1 := by
    have := Int.dvd_gcd h5' h5M
    rwa [h] at this
  omega

/-- 5/2: an odd `Q_n` forces an odd carry in `[-1, 4]`. Only `Q_n` is used. -/
theorem carry_alphabet_52 (ξ : ℝ) (_hξ : 0 < ξ) (n : ℕ)
    (h1 : Int.gcd (floorOrbit 5 2 ξ n) 40112098026 = 1)
    (_h2 : Int.gcd (floorOrbit 5 2 ξ (n + 1)) 40112098026 = 1) :
    carry 5 2 ξ n ∈ [-1, 1, 3] := by
  have hodd := odd_of_gcd_even_modulus _ _ (by norm_num) h1
  have hb := carry_bounds 5 2 (by norm_num) (by norm_num) ξ n
  have hc : carry 5 2 ξ n = 2 * floorOrbit 5 2 ξ (n + 1) - 5 * floorOrbit 5 2 ξ n := by
    unfold carry; push_cast; ring
  simp only [List.mem_cons, List.mem_nil_iff, or_false]
  push_cast at hb
  omega

/-- 7/5: odd `Q_n`, odd `Q_{n+1}` and `5 ∤ Q_n` force an even nonzero carry in `[-4, 6]`. -/
theorem carry_alphabet_75 (ξ : ℝ) (_hξ : 0 < ξ) (n : ℕ)
    (h1 : Int.gcd (floorOrbit 7 5 ξ n) 4290 = 1)
    (h2 : Int.gcd (floorOrbit 7 5 ξ (n + 1)) 4290 = 1) :
    carry 7 5 ξ n ∈ [-4, -2, 2, 4, 6] := by
  have hodd1 := odd_of_gcd_even_modulus _ _ (by norm_num) h1
  have hodd2 := odd_of_gcd_even_modulus _ _ (by norm_num) h2
  have h5 := not_five_dvd_of_gcd _ _ (by norm_num) h1
  have hb := carry_bounds 7 5 (by norm_num) (by norm_num) ξ n
  have hc : carry 7 5 ξ n = 5 * floorOrbit 7 5 ξ (n + 1) - 7 * floorOrbit 7 5 ξ n := by
    unfold carry; push_cast; ring
  simp only [List.mem_cons, List.mem_nil_iff, or_false]
  push_cast at hb
  omega

end MathPaper
