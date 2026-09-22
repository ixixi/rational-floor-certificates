import MathPaper.Word.Pipeline.Data

/-! The initial cell graph, enumerated by the strict inequalities (E3) over all
`(j, c, k)` (audit-02 (S52-1)); one-letter words `#[c]` indexed by the alphabet
position. -/
namespace MathPaper.Pipe

def initialWords (alphabet : List ℤ) : WTable := (alphabet.map fun c => #[c]).toArray

def cellEdge (a b K : ℕ) (j : ℕ) (c : ℤ) (k : ℕ) : Bool :=
  decide ((a : ℤ) * j - b * ((k : ℤ) + 1) < c * K ∧ c * K < a * ((j : ℤ) + 1) - b * k)

def initialEdges (a b K : ℕ) (alphabet : List ℤ) : Array PEdge :=
  (Array.range K).flatMap fun j =>
    (Array.range alphabet.length).flatMap fun ci =>
      let c := alphabet.getD ci 0
      (Array.range K).filterMap fun k =>
        if cellEdge a b K j c k then some ⟨j, ci, k⟩ else none

def initialStage (a b K : ℕ) (alphabet : List ℤ) : CStage :=
  ⟨K, initialWords alphabet, initialEdges a b K alphabet⟩

theorem initialWords_getD (alphabet : List ℤ) (ci : ℕ) (h : ci < alphabet.length) :
    wordOf (initialWords alphabet) ci = #[alphabet.getD ci 0] := by
  unfold wordOf initialWords
  rw [getD_eq_getElem _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem initialStage_sound (a b K : ℕ) (alphabet : List ℤ) :
    InitialGraph a b K alphabet ⊆ (initialStage a b K alphabet).sem := by
  rintro e ⟨j, k, c, hc, hj, hk, hlo, hhi, rfl⟩
  obtain ⟨ci, hci, rfl⟩ := List.mem_iff_getElem.mp hc
  have hcd : alphabet[ci] = alphabet.getD ci 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hci]
  refine ⟨⟨j, ci, k⟩, ?_, ?_⟩
  · unfold initialStage initialEdges
    simp only
    rw [Array.mem_flatMap]
    refine ⟨j, Array.mem_range.mpr hj, ?_⟩
    rw [Array.mem_flatMap]
    refine ⟨ci, Array.mem_range.mpr hci, ?_⟩
    rw [Array.mem_filterMap]
    refine ⟨k, Array.mem_range.mpr hk, ?_⟩
    have : cellEdge a b K j (alphabet.getD ci 0) k = true := by
      unfold cellEdge
      rw [← hcd]
      exact decide_eq_true ⟨hlo, hhi⟩
    simp only [List.getD_eq_getElem?_getD] at this
    simp [this]
  · simp [deref, initialStage, initialWords_getD alphabet ci hci, List.getElem?_eq_getElem hci]

end MathPaper.Pipe
