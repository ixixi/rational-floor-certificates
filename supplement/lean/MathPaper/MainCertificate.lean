import MathPaper.Finite.Verify0_15
import MathPaper.Finite.Verify1_03
import MathPaper.Finite.Verify2_01
import MathPaper.Finite.Verify3_01
import MathPaper.Finite.Refinement0
import MathPaper.Finite.Refinement1
import MathPaper.Finite.Refinement2
import MathPaper.Finite.Boundary

namespace MathPaper

open Finite

/-- Four stages of the concrete, kernel-checked rank/phase certificate.
The input generator and the external SCC implementations are not trusted by this term. -/
noncomputable def mainFiniteSuccess : FiniteSuccess 7 5 4290 where
  last := 3
  factor := 4
  factor_pos := by decide
  cells := fun t => 32 * 4 ^ t
  cells_pos := by intro t; positivity
  cells_step := by intro t; simp [Nat.pow_succ]; ring
  states := fun t => match t with
    | 0 => states data0 32
    | 1 => states data1 128
    | 2 => states data2 512
    | _ => states data3 2048
  retained := fun t => match t with
    | 0 => retained data0 32
    | 1 => retained data1 128
    | 2 => retained data2 512
    | _ => retained data3 2048
  cert := fun t => match t with
    | 0 => certificate data0 32
    | 1 => certificate data1 128
    | 2 => certificate data2 512
    | _ => certificate data3 2048
  initial := initial_sound data0 initial_checked
  valid := by
    intro t ht
    interval_cases t
    · exact checked_stage_fast data0 32 data0_checked
    · exact checked_stage_fast data1 128 data1_checked
    · exact checked_stage_fast data2 512 data2_checked
    · exact checked_stage_fast data3 2048 data3_checked
  refine_sub := by
    intro t ht
    interval_cases t
    · exact refine_sound data0 data1 32 refinement0_checked
    · exact refine_sound data1 data2 128 refinement1_checked
    · exact refine_sound data2 data3 512 refinement2_checked
  final_empty := empty_sound data3 2048 final_checked

#print axioms mainFiniteSuccess

end MathPaper
