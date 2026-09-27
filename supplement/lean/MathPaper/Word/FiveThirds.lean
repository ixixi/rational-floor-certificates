import MathPaper.Word.ExecSound
import MathPaper.Word.Alphabet

/-! The 5/3 theorem (5/3 addition, manuscript Theorem 1(iii)) and its
corollary. The finite computation is the two-direction pipeline
`WordExec.wordPipelineBidir`, executed inside Lean and accepted through the
compiler (`native_decide`; in Lean 4.29.1 this asserts the native evaluation by
the generated axiom `five_thirds_ok._native.native_decide.ax_1_1`). The module
`WordExec` is precompiled, so the evaluation runs compiled code. The soundness
theorem `WordExec.wordPipelineBidir_sound`, the in-direction contraction theory
and the word-labelled theory are kernel-checked. -/
namespace MathPaper

theorem not_three_dvd_of_gcd (Q : ℤ) (M : ℕ) (hM : 3 ∣ M) (h : Int.gcd Q M = 1) :
    Q % 3 ≠ 0 := by
  intro h3
  have h3' : ((3 : ℕ) : ℤ) ∣ Q := Int.dvd_of_emod_eq_zero (by push_cast; omega)
  have h3M : ((3 : ℕ) : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.mpr hM
  have h31 : (3 : ℕ) ∣ 1 := by
    have := Int.dvd_gcd h3' h3M
    rwa [h] at this
  omega

/-- 5/3: odd `Q_n`, odd `Q_{n+1}` and `3 ∤ Q_n` force a carry in `{-2, 2, 4}`.
No condition modulo 5 is used. -/
theorem carry_alphabet_53 (ξ : ℝ) (_hξ : 0 < ξ) (n : ℕ)
    (h1 : Int.gcd (floorOrbit 5 3 ξ n) 1484147626962 = 1)
    (h2 : Int.gcd (floorOrbit 5 3 ξ (n + 1)) 1484147626962 = 1) :
    carry 5 3 ξ n ∈ [-2, 2, 4] := by
  have hodd1 := odd_of_gcd_even_modulus _ _ (by norm_num) h1
  have hodd2 := odd_of_gcd_even_modulus _ _ (by norm_num) h2
  have h3 := not_three_dvd_of_gcd _ _ (by norm_num) h1
  have hb := carry_bounds 5 3 (by norm_num) (by norm_num) ξ n
  have hc : carry 5 3 ξ n = 3 * floorOrbit 5 3 ξ (n + 1) - 5 * floorOrbit 5 3 ξ n := by
    unfold carry; push_cast; ring
  simp only [List.mem_cons, List.mem_nil_iff, or_false]
  push_cast at hb
  omega

/-- The 5/3 word-labelled certificate: `K = 3`, alphabet `{-2, 2, 4}`, nine
auxiliary primes, in-direction and out-direction contraction. Accepted by
native evaluation of the Lean pipeline. -/
theorem five_thirds_ok :
    WordExec.wordPipelineBidir 5 3 3 [-2, 2, 4] [7, 11, 13, 17, 19, 23, 29, 31, 37] = true := by
  native_decide

theorem five_thirds_success :
    WordFiniteSuccessB 5 3 3 [-2, 2, 4] [7, 11, 13, 17, 19, 23, 29, 31, 37] :=
  WordExec.wordPipelineBidir_sound _ _ _ _ _ five_thirds_ok

/-- Every positive real floor orbit for 5/3 has arbitrarily late terms sharing a
nontrivial divisor with `1484147626962 = 2·3·7·11·13·17·19·23·29·31·37`. -/
theorem floor_five_thirds_visits (ξ : ℝ) (hξ : 0 < ξ) (N : ℕ) :
    ∃ n : ℕ, max N 1 ≤ n ∧ 1 < Int.gcd ⌊ξ * (5 / 3 : ℝ) ^ n⌋ 1484147626962 :=
  word_finite_success_visits_B 5 3 3 1484147626962 [-2, 2, 4]
    [7, 11, 13, 17, 19, 23, 29, 31, 37]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    carry_alphabet_53 five_thirds_success ξ hξ N

/-- Every positive real floor orbit for 5/3 has arbitrarily late composite terms. -/
theorem floor_five_thirds_composite (ξ : ℝ) (hξ : 0 < ξ) (N : ℕ) :
    ∃ n : ℕ, max N 1 ≤ n ∧ Composite ⌊ξ * (5 / 3 : ℝ) ^ n⌋ :=
  word_finite_success_composite_B 5 3 3 1484147626962 [-2, 2, 4]
    [7, 11, 13, 17, 19, 23, 29, 31, 37]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    carry_alphabet_53 five_thirds_success ξ hξ N

end MathPaper
