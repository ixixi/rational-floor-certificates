import MathPaper.Orbit

/-! Word-labelled graphs and coverings of a carry sequence (audit-02 §2, W1).
A covering is an infinite walk whose concatenated output equals the carry
tail from a start time. Vertex types are arbitrary; finiteness is never used
directly (the rank argument replaces it). -/
namespace MathPaper

structure WEdge (V : Type*) where
  src : V
  word : List ℤ
  dst : V

abbrev WGraph (V : Type*) := Set (WEdge V)

/-- The walk `v`, words `w`, macro times `t`. Every word is nonempty, so the
output is an infinite word whose letter at time `t i + k` is `(w i)[k]`. -/
structure Covering {V : Type*} (G : WGraph V) (c : ℕ → ℤ) (n₀ : ℕ) where
  v : ℕ → V
  w : ℕ → List ℤ
  t : ℕ → ℕ
  t_zero : t 0 = n₀
  edge : ∀ i, (⟨v i, w i, v (i + 1)⟩ : WEdge V) ∈ G
  nonempty : ∀ i, w i ≠ []
  t_succ : ∀ i, t (i + 1) = t i + (w i).length
  output : ∀ i k, k < (w i).length → (w i).getD k 0 = c (t i + k)

def Covers {V : Type*} (G : WGraph V) (c : ℕ → ℤ) (n₀ : ℕ) : Prop :=
  Nonempty (Covering G c n₀)

namespace Covering

variable {V : Type*} {G : WGraph V} {c : ℕ → ℤ} {n₀ : ℕ}

theorem length_pos (C : Covering G c n₀) (i : ℕ) : 0 < (C.w i).length :=
  List.length_pos_of_ne_nil (C.nonempty i)

theorem t_add (C : Covering G c n₀) (i k : ℕ) : C.t i + k ≤ C.t (i + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := C.t_succ (i + k)
    have hl := C.length_pos (i + k)
    rw [show i + (k + 1) = i + k + 1 by omega, h]
    omega

theorem t_mono (C : Covering G c n₀) {i j : ℕ} (h : i ≤ j) : C.t i ≤ C.t j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have := C.t_add i k
  omega

theorem le_t (C : Covering G c n₀) (i : ℕ) : n₀ + i ≤ C.t i := by
  have := C.t_add 0 i
  rw [C.t_zero] at this
  simpa using this

/-- Restart the walk at index `N`. -/
def shift (C : Covering G c n₀) (N : ℕ) : Covering G c (C.t N) where
  v := fun i => C.v (N + i)
  w := fun i => C.w (N + i)
  t := fun i => C.t (N + i)
  t_zero := by simp
  edge := fun i => by simpa only [Nat.add_assoc] using C.edge (N + i)
  nonempty := fun i => C.nonempty (N + i)
  t_succ := fun i => by simpa only [Nat.add_assoc] using C.t_succ (N + i)
  output := fun i k hk => C.output (N + i) k hk

/-- Concatenation of the words `w i, …, w (i+len-1)`. -/
def concatFrom (w : ℕ → List ℤ) : ℕ → ℕ → List ℤ
  | _, 0 => []
  | i, len + 1 => w i ++ concatFrom w (i + 1) len

theorem concatFrom_zero (w : ℕ → List ℤ) (i : ℕ) : concatFrom w i 0 = [] := rfl

theorem concatFrom_succ (w : ℕ → List ℤ) (i len : ℕ) :
    concatFrom w i (len + 1) = w i ++ concatFrom w (i + 1) len := rfl

theorem concatFrom_one (w : ℕ → List ℤ) (i : ℕ) : concatFrom w i 1 = w i := by
  simp [concatFrom]

theorem t_concatFrom (C : Covering G c n₀) (i len : ℕ) :
    C.t (i + len) = C.t i + (concatFrom C.w i len).length := by
  induction len generalizing i with
  | zero => simp [concatFrom]
  | succ len ih =>
    rw [concatFrom_succ, List.length_append, show i + (len + 1) = (i + 1) + len by omega,
      ih (i + 1), C.t_succ i]
    omega

theorem concatFrom_ne_nil (C : Covering G c n₀) (i len : ℕ) (h : 0 < len) :
    concatFrom C.w i len ≠ [] := by
  obtain ⟨len, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h)
  rw [concatFrom_succ]
  intro hnil
  exact C.nonempty i (List.append_eq_nil_iff.mp hnil).1

theorem getD_append_lt (l₁ l₂ : List ℤ) (k : ℕ) (h : k < l₁.length) :
    (l₁ ++ l₂).getD k 0 = l₁.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_ge (l₁ l₂ : List ℤ) (k : ℕ) (h : l₁.length ≤ k) :
    (l₁ ++ l₂).getD k 0 = l₂.getD (k - l₁.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem output_concatFrom (C : Covering G c n₀) (i len k : ℕ)
    (hk : k < (concatFrom C.w i len).length) :
    (concatFrom C.w i len).getD k 0 = c (C.t i + k) := by
  induction len generalizing i k with
  | zero => simp [concatFrom] at hk
  | succ len ih =>
    rw [concatFrom_succ] at hk ⊢
    by_cases hlt : k < (C.w i).length
    · rw [getD_append_lt _ _ _ hlt]
      exact C.output i k hlt
    · push Not at hlt
      rw [getD_append_ge _ _ _ hlt]
      rw [List.length_append] at hk
      rw [ih (i + 1) (k - (C.w i).length) (by omega), C.t_succ i]
      congr 1
      omega

end Covering

namespace Covers

variable {V V' : Type*} {G G' : WGraph V} {c : ℕ → ℤ} {n₀ : ℕ}

theorem mono (h : G ⊆ G') (hc : Covers G c n₀) : Covers G' c n₀ := by
  obtain ⟨C⟩ := hc
  exact ⟨⟨C.v, C.w, C.t, C.t_zero, fun i => h (C.edge i), C.nonempty, C.t_succ, C.output⟩⟩

theorem not_empty (hc : Covers (∅ : WGraph V) c n₀) : False := by
  obtain ⟨C⟩ := hc
  exact C.edge 0

end Covers

/-- Image of a graph under an arbitrary vertex map. Injectivity is not needed:
merging vertices only adds walks (outer approximation). -/
def WGraph.map {V V' : Type*} (ρ : V → V') (G : WGraph V) : WGraph V' :=
  {e' | ∃ e ∈ G, e' = ⟨ρ e.src, e.word, ρ e.dst⟩}

theorem WGraph.mem_map {V V' : Type*} (ρ : V → V') (G : WGraph V) (e : WEdge V) (he : e ∈ G) :
    (⟨ρ e.src, e.word, ρ e.dst⟩ : WEdge V') ∈ G.map ρ := ⟨e, he, rfl⟩

theorem Covers.map {V V' : Type*} {G : WGraph V} {c : ℕ → ℤ} {n₀ : ℕ} (ρ : V → V')
    (hc : Covers G c n₀) : Covers (G.map ρ) c n₀ := by
  obtain ⟨C⟩ := hc
  exact ⟨⟨fun i => ρ (C.v i), C.w, C.t, C.t_zero, fun i => WGraph.mem_map ρ G _ (C.edge i),
    C.nonempty, C.t_succ, C.output⟩⟩

end MathPaper
