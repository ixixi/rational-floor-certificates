import MathPaper.Word.Pipeline.Data

/-! The concrete lift (verified function): every output edge, every start
residue `1 ≤ q < p`, forward iteration along the word. Vertices `(u, q)` are
renamed by an arbitrary map `ρ`; soundness does not need injectivity. -/
namespace MathPaper.Pipe

def liftArr (a p binv : ℕ) (W : WTable) (gout : Array PEdge) (ρ : ℕ × ℕ → ℕ) : Array PEdge :=
  gout.flatMap fun pe =>
    let w := (wordOf W pe.wid).toList
    (Array.range p).filterMap fun q =>
      if q = 0 then none else
      match runWord a p binv w q with
      | none => none
      | some q' => some ⟨ρ (pe.src, q), pe.wid, ρ (pe.dst, q')⟩

theorem liftArr_sound (a p binv : ℕ) (W : WTable) (gout : Array PEdge) (ρ : ℕ × ℕ → ℕ) :
    (Lift a p binv (sem W gout)).map ρ ⊆ sem W (liftArr a p binv W gout ρ) := by
  rintro e' ⟨x, ⟨e, ⟨pe, hpe, rfl⟩, q, hq, hx⟩, rfl⟩
  unfold liftEdge at hx
  split at hx
  · exact absurd hx (by simp)
  · rename_i hq0
    split at hx
    · exact absurd hx (by simp)
    · rename_i q' hrun
      simp only [Option.some.injEq] at hx
      subst hx
      refine ⟨⟨ρ (pe.src, q), pe.wid, ρ (pe.dst, q')⟩, ?_, rfl⟩
      unfold liftArr
      rw [Array.mem_flatMap]
      refine ⟨pe, hpe, ?_⟩
      rw [Array.mem_filterMap]
      refine ⟨q, Array.mem_range.mpr hq, ?_⟩
      simp only [deref] at hrun
      simp [hq0, hrun]

/-- The dense renaming used by the pipeline: `(u, q) ↦ newId u * (p - 1) + (q - 1)`. -/
def renameLift (newId : Array ℕ) (p : ℕ) : ℕ × ℕ → ℕ :=
  fun x => newId.getD x.1 0 * (p - 1) + (x.2 - 1)

end MathPaper.Pipe
