import MathPaper.Word.Pipeline.Main
import MathPaper.Word.Alphabet

/-! Cross application T75-X: the 7/5 theorem (modulus 4290) re-proved by the
word-labelled method with `K = 2048`, alphabet `{-4, -2, 2, 4, 6}` and primes
3, 11, 13. This is an alternative proof of `floor_seven_fifths_visits`. -/
namespace MathPaper

open Pipe

theorem seven_fifths_ok :
    wordPipeline 7 5 2048 [-4, -2, 2, 4, 6] [3, 11, 13] = true := by
  native_decide

theorem seven_fifths_success_word :
    WordFiniteSuccess 7 5 2048 [-4, -2, 2, 4, 6] [3, 11, 13] :=
  wordPipeline_sound _ _ _ _ _ seven_fifths_ok

theorem floor_seven_fifths_visits_word (ξ : ℝ) (hξ : 0 < ξ) (N : ℕ) :
    ∃ n : ℕ, max N 1 ≤ n ∧ 1 < Int.gcd ⌊ξ * (7 / 5 : ℝ) ^ n⌋ 4290 :=
  word_finite_success_visits 7 5 2048 4290 [-4, -2, 2, 4, 6] [3, 11, 13]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    carry_alphabet_75 seven_fifths_success_word ξ hξ N

end MathPaper
