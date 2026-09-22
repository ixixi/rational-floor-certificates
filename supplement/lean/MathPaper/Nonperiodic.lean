import MathPaper.Orbit

namespace MathPaper

/-- An integral sequence cannot follow a reduced nonintegral ratio indefinitely
unless it is zero. No positivity assumption on the sequence is made. -/
theorem homogeneous_integer_sequence_zero (a b : ℕ) (hb : 2 ≤ b)
    (hab : Nat.Coprime a b) (D : ℕ → ℤ)
    (hD : ∀ n, (b : ℤ) * D (n + 1) = (a : ℤ) * D n) : D 0 = 0 := by
  have hp : ∀ n, (b : ℤ) ^ n * D n = (a : ℤ) ^ n * D 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        (b : ℤ) ^ (n + 1) * D (n + 1) = (b : ℤ) ^ n * ((b : ℤ) * D (n + 1)) := by ring
        _ = (b : ℤ) ^ n * ((a : ℤ) * D n) := by rw [hD]
        _ = (a : ℤ) * ((b : ℤ) ^ n * D n) := by ring
        _ = (a : ℤ) ^ (n + 1) * D 0 := by rw [ih]; ring
  have hd : ∀ n, b ^ n ∣ (D 0).natAbs := by
    intro n
    have hd' : (b : ℤ) ^ n ∣ (a : ℤ) ^ n * D 0 := ⟨D n, (hp n).symm⟩
    have hd'' : b ^ n ∣ a ^ n * (D 0).natAbs := by
      have := Int.natCast_dvd.mp (show ((b ^ n : ℕ) : ℤ) ∣ (a : ℤ) ^ n * D 0 by
        simpa using hd')
      simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] using this
    exact (hab.symm.pow n n).dvd_of_dvd_mul_left hd''
  by_contra hn
  have hpos : 0 < (D 0).natAbs := Int.natAbs_pos.mpr hn
  obtain ⟨n, hlt⟩ := pow_unbounded_of_one_lt (D 0).natAbs (show 1 < b by omega)
  exact (not_lt_of_ge (Nat.le_of_dvd hpos (hd n))) hlt

/-- The carry obstruction in a form independent of floors and real numbers. -/
theorem carry_not_eventually_periodic (a b : ℕ) (hb : 2 ≤ b)
    (hab : Nat.Coprime a b) (Q : ℕ → ℤ) (c : ℕ → ℤ)
    (hrec : ∀ n, (b : ℤ) * Q (n + 1) = (a : ℤ) * Q n + c n)
    (hgrow : TendsToInfinity Q) : ¬ EventuallyPeriodic c := by
  rintro ⟨N, L, hL, hper⟩
  have hshift : ∀ m, N ≤ m → Q (m + L) = Q m := by
    intro m hm
    have hz := homogeneous_integer_sequence_zero a b hb hab
      (fun k => Q (m + k + L) - Q (m + k)) (by
        intro k
        dsimp only
        have h1 := hrec (m + k + L)
        have h2 := hrec (m + k)
        have hc := hper (m + k) (by omega)
        have hi : m + (k + 1) + L = m + k + L + 1 := by omega
        have hj : m + (k + 1) = m + k + 1 := by omega
        rw [hi, hj]
        rw [hc] at h1
        linear_combination h1 - h2)
    simpa using sub_eq_zero.mp hz
  have hconst : ∀ k, Q (N + k * L) = Q N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show N + (k + 1) * L = (N + k * L) + L by ring]
      rw [hshift (N + k * L) (by omega), ih]
  obtain ⟨M, hM⟩ := hgrow (Q N)
  have hbound : M ≤ N + M * L := by nlinarith
  have hc := hM (N + M * L) hbound
  rw [hconst] at hc
  exact (lt_irrefl _ hc)

theorem floor_carry_not_eventually_periodic (a b : ℕ) (hab : b < a)
    (hb : 2 ≤ b) (hcop : Nat.Coprime a b) (ξ : ℝ) (hξ : 0 < ξ) :
    ¬ EventuallyPeriodic (carry a b ξ) :=
  carry_not_eventually_periodic a b hb hcop (floorOrbit a b ξ) (carry a b ξ)
    (carry_recurrence a b ξ) (floor_orbit_eventually_gt a b hab (by omega) ξ hξ)

end MathPaper
