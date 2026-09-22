import MathPaper.Word.Chain

/-! Concrete data of the executable pipeline. Vertices are natural-number
indices, words live in a shared table and edges refer to word ids. The
semantics `sem` interprets a concrete edge array as an abstract word graph. -/
namespace MathPaper.Pipe

structure PEdge where
  src : ℕ
  wid : ℕ
  dst : ℕ
  deriving Inhabited, DecidableEq, Hashable

abbrev WTable := Array (Array ℤ)

def wordOf (W : WTable) (wid : ℕ) : Array ℤ := W.getD wid #[]

def deref (W : WTable) (pe : PEdge) : WEdge ℕ := ⟨pe.src, (wordOf W pe.wid).toList, pe.dst⟩

def sem (W : WTable) (edges : Array PEdge) : WGraph ℕ := {e | ∃ pe ∈ edges, e = deref W pe}

theorem mem_sem (W : WTable) (edges : Array PEdge) (pe : PEdge) (h : pe ∈ edges) :
    deref W pe ∈ sem W edges := ⟨pe, h, rfl⟩

structure CStage where
  n : ℕ
  W : WTable
  edges : Array PEdge

def CStage.sem (S : CStage) : WGraph ℕ := Pipe.sem S.W S.edges

/-- Tail-recursive bounded conjunction with explicit fuel (kernel-friendly). -/
def allIdx.go (n : ℕ) (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => true
  | fuel + 1, i => if i < n then (f i && allIdx.go n f fuel (i + 1)) else true

def allIdx (n : ℕ) (f : ℕ → Bool) : Bool := allIdx.go n f n 0

theorem allIdx.go_spec (n : ℕ) (f : ℕ → Bool) :
    ∀ fuel i, allIdx.go n f fuel i = true →
      ∀ j, i ≤ j → j < n → j < i + fuel → f j = true := by
  intro fuel
  induction fuel with
  | zero => intro i _ j _ _ h; omega
  | succ fuel ih =>
    intro i h j hij hjn hjf
    simp only [allIdx.go] at h
    split at h
    · simp only [Bool.and_eq_true] at h
      by_cases hji : j = i
      · subst hji; exact h.1
      · exact ih (i + 1) h.2 j (by omega) hjn (by omega)
    · omega

theorem allIdx_spec {n : ℕ} {f : ℕ → Bool} (h : allIdx n f = true) {i : ℕ} (hi : i < n) :
    f i = true :=
  allIdx.go_spec n f n 0 h i (Nat.zero_le i) hi (by omega)

theorem toList_getD (xs : Array ℤ) (i : ℕ) : xs.toList.getD i 0 = xs.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]

theorem getD_eq_getElem {α : Type*} (xs : Array α) (i : ℕ) (d : α) (h : i < xs.size) :
    xs.getD i d = xs[i] := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]

theorem mem_of_getElem? {α : Type*} (xs : Array α) (i : ℕ) (a : α) (h : xs[i]? = some a) :
    a ∈ xs := by
  rw [Array.getElem?_eq_some_iff] at h
  obtain ⟨hi, rfl⟩ := h
  exact Array.getElem_mem hi

end MathPaper.Pipe
