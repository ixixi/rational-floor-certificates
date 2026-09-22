import MathPaper.Word.Pipeline.Main
import MathPaper.Word.Alphabet

/-! Theorem T52 (manuscript Theorem 1(ii)) and its corollary. The finite
computation is executed inside Lean by `wordPipeline` and accepted through the
compiler (`native_decide`; in Lean 4.29.1 this asserts the native evaluation by
the generated axiom `five_halves_ok._native.native_decide.ax_1_1`, the
successor of `Lean.ofReduceBool`); its soundness theorem `wordPipeline_sound`
and the word-labelled theory are kernel-checked. -/
namespace MathPaper

open Pipe

/-- The 5/2 word-labelled certificate: `K = 4`, alphabet `{-1, 1, 3}`, nine
auxiliary primes. Accepted by native evaluation of the Lean pipeline. -/
theorem five_halves_ok :
    wordPipeline 5 2 4 [-1, 1, 3] [3, 7, 11, 13, 17, 19, 23, 29, 31] = true := by
  native_decide

theorem five_halves_success :
    WordFiniteSuccess 5 2 4 [-1, 1, 3] [3, 7, 11, 13, 17, 19, 23, 29, 31] :=
  wordPipeline_sound _ _ _ _ _ five_halves_ok

/-- Every positive real floor orbit for 5/2 has arbitrarily late terms sharing a
nontrivial divisor with `40112098026 = 2·3·7·11·13·17·19·23·29·31`. -/
theorem floor_five_halves_visits (ξ : ℝ) (hξ : 0 < ξ) (N : ℕ) :
    ∃ n : ℕ, max N 1 ≤ n ∧ 1 < Int.gcd ⌊ξ * (5 / 2 : ℝ) ^ n⌋ 40112098026 :=
  word_finite_success_visits 5 2 4 40112098026 [-1, 1, 3] [3, 7, 11, 13, 17, 19, 23, 29, 31]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    carry_alphabet_52 five_halves_success ξ hξ N

/-- Every positive real floor orbit for 5/2 has arbitrarily late composite terms. -/
theorem floor_five_halves_composite (ξ : ℝ) (hξ : 0 < ξ) (N : ℕ) :
    ∃ n : ℕ, max N 1 ≤ n ∧ Composite ⌊ξ * (5 / 2 : ℝ) ^ n⌋ :=
  word_finite_success_composite 5 2 4 40112098026 [-1, 1, 3] [3, 7, 11, 13, 17, 19, 23, 29, 31]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    carry_alphabet_52 five_halves_success ξ hξ N

end MathPaper
