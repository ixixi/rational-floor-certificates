import MathPaper.Graph

namespace MathPaper

/-- Exact signed-integer target-cell bounds, including negative numerators. -/
theorem edge_interval_iff (a b j e K k : ℤ) (hb : 0 < b) :
    (0 ≤ k ∧ k < K ∧ a * j - b * (k + 1) < e * K ∧
      e * K < a * (j + 1) - b * k) ↔
    (max 0 ((a * j - e * K) / b) ≤ k ∧
      k ≤ min (K - 1) ((a * (j + 1) - e * K - 1) / b)) := by
  rw [max_le_iff, le_min_iff, Int.ediv_le_iff_le_mul hb, Int.le_ediv_iff_mul_le hb]
  constructor
  · rintro ⟨h0, hK, hlo, hhi⟩
    exact ⟨⟨h0, by nlinarith⟩, ⟨by omega, by nlinarith⟩⟩
  · rintro ⟨⟨h0, hlo⟩, ⟨hK, hhi⟩⟩
    exact ⟨h0, by omega, by nlinarith, by nlinarith⟩

/-- All congruence solutions for the main modulus. This never divides by 5
modulo 4290; the reduced modulus is 858 and all five lifts are retained. -/
theorem main_congruence_candidate (q z e : ℤ) (hz0 : 0 ≤ z) (hz : z < 4290)
    (hdiv : (4290 : ℤ) ∣ 5 * z - 7 * q - e) :
    ∃ t : ℕ, t < 5 ∧ z = ((7 * q + e) / 5) % 858 + 858 * (t : ℤ) := by
  obtain ⟨k, hk⟩ := hdiv
  have hquot : (7 * q + e) / 5 = z - 858 * k := by omega
  have hmod : z % 858 = ((7 * q + e) / 5) % 858 := by omega
  refine ⟨(z / 858).toNat, ?_, ?_⟩ <;> omega

/-- There are at most three target cells for a given source cell and carry. -/
theorem main_cell_candidate (j k e K : ℤ)
    (hlo : 7 * j - 5 * (k + 1) < e * K)
    (hhi : e * K < 7 * (j + 1) - 5 * k) :
    ∃ t : ℕ, t < 3 ∧ k = (7 * j - e * K) / 5 + (t : ℤ) := by
  have ht0 : 0 ≤ k - (7 * j - e * K) / 5 := by omega
  have ht3 : k - (7 * j - e * K) / 5 < 3 := by omega
  refine ⟨(k - (7 * j - e * K) / 5).toNat, ?_, ?_⟩ <;> omega

/-- Restrict the eleven possible carry values to three representatives of the
necessary congruence modulo 5. Candidates still need E1 to be checked. -/
theorem main_carry_candidate (q z e : ℤ) (he0 : -4 ≤ e) (he1 : e ≤ 6)
    (hdiv : (4290 : ℤ) ∣ 5 * z - 7 * q - e) :
    ∃ t : ℕ, t < 3 ∧ e = -4 + (4 - 7 * q) % 5 + 5 * (t : ℤ) := by
  obtain ⟨k, hk⟩ := hdiv
  have hmod : (e + 4) % 5 = (4 - 7 * q) % 5 := by omega
  refine ⟨((e + 4) / 5).toNat, ?_, ?_⟩ <;> omega

end MathPaper
