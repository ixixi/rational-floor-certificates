import MathPaper.MainCertificate

/-! The unconditional statements use the concrete finite certificate.
Their verification requires the complete MainCertificate dependency chain. -/
namespace MathPaper

/-- Every positive real floor orbit for 7/5 has arbitrarily late terms sharing
a nontrivial divisor with 4290. The time index is a positive natural number. -/
theorem floor_seven_fifths_visits (ξ : ℝ) (hξ : 0 < ξ) (N : ℕ) :
    ∃ n : ℕ, max N 1 ≤ n ∧ 1 < Int.gcd ⌊ξ * (7 / 5 : ℝ) ^ n⌋ 4290 := by
  exact finite_success_visits 7 5 4290 (by decide) (by decide) (by decide)
    (by decide) mainFiniteSuccess ξ hξ N

/-- Every positive real floor orbit for 7/5 has arbitrarily late composite
terms, with two positive integer factors strictly greater than one. -/
theorem floor_seven_fifths_composite (ξ : ℝ) (hξ : 0 < ξ) (N : ℕ) :
    ∃ n : ℕ, max N 1 ≤ n ∧ Composite ⌊ξ * (7 / 5 : ℝ) ^ n⌋ := by
  exact finite_success_composite 7 5 4290 (by decide) (by decide) (by decide)
    (by decide) mainFiniteSuccess ξ hξ N

end MathPaper
