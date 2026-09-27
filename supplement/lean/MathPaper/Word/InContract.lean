import MathPaper.Word.Cert

/-! In-degree-one contraction for word-labelled graphs, stated in the original
direction (5/3 addition). It is the in-direction counterpart of `ContractOK`:
macro vertices are the vertices of in-degree at least two of the retained part;
every other retained vertex records its backward chain `(w', b)`, the word read
from the previous macro vertex `b` up to it. The recorded chain lengths are
bounded by `bound`. Along a forward walk that avoids macro vertices the chain
length increases strictly, so such a walk cannot stay away from macro vertices
for longer than `bound + 1` steps. Neither strongly connected components nor
finiteness of the graph is used. -/
namespace MathPaper

structure WordCertIn (V : Type*) where
  base : WordCert V
  chainIn : V → Option (List ℤ × V)
  bound : ℕ

namespace WordCertIn

variable {V : Type*} (C : WordCertIn V)

/-- Backward contraction data: an edge into a macro vertex closes a macro edge
of `Gout` starting at the previous macro vertex; an edge into a non-macro vertex
extends the recorded backward chain. -/
def ContractInOK (Gout : WGraph V) (e : WEdge V) : Prop :=
  if C.base.isMacro e.dst = true then
    (C.base.isMacro e.src = true ∧ e ∈ Gout) ∨
    (C.base.isMacro e.src = false ∧ ∃ w'' b, C.chainIn e.src = some (w'', b) ∧
      (⟨b, w'' ++ e.word, e.dst⟩ : WEdge V) ∈ Gout)
  else
    ∃ w' b, C.chainIn e.dst = some (w', b) ∧ w'.length ≤ C.bound ∧
      ((C.base.isMacro e.src = true ∧ w' = e.word ∧ b = e.src) ∨
       (C.base.isMacro e.src = false ∧ ∃ w'', C.chainIn e.src = some (w'', b) ∧
         w' = w'' ++ e.word))

def EdgeConditionIn (Gout : WGraph V) (e : WEdge V) : Prop :=
  if C.base.owner e.src = C.base.owner e.dst then
    (if C.base.retained (C.base.owner e.src) = true then C.ContractInOK Gout e
     else C.base.PhaseOK e)
  else C.base.rank (C.base.owner e.dst) < C.base.rank (C.base.owner e.src)

end WordCertIn

theorem Covering.concatFrom_succ_right (w : ℕ → List ℤ) (i len : ℕ) :
    Covering.concatFrom w i (len + 1) = Covering.concatFrom w i len ++ w (i + len) := by
  induction len generalizing i with
  | zero => simp [Covering.concatFrom]
  | succ len ih =>
    rw [Covering.concatFrom_succ, ih (i + 1), Covering.concatFrom_succ, List.append_assoc,
      show i + 1 + len = i + (len + 1) by omega]

section ContractIn

variable {V : Type*} {G : WGraph V} {c : ℕ → ℤ} {n₀ : ℕ}

/-- The chain recorded at a non-macro vertex of the walk. -/
theorem chainIn_step (C : WordCertIn V) (Gout : WGraph V) (Cov : Covering G c n₀)
    (h : ∀ i, C.ContractInOK Gout ⟨Cov.v i, Cov.w i, Cov.v (i + 1)⟩) (i : ℕ)
    (hm : C.base.isMacro (Cov.v (i + 1)) = false) :
    ∃ w' b, C.chainIn (Cov.v (i + 1)) = some (w', b) ∧ w'.length ≤ C.bound ∧
      ((C.base.isMacro (Cov.v i) = true ∧ w' = Cov.w i ∧ b = Cov.v i) ∨
       (C.base.isMacro (Cov.v i) = false ∧ ∃ w'', C.chainIn (Cov.v i) = some (w'', b) ∧
         w' = w'' ++ Cov.w i)) := by
  have hi := h i
  simp only [WordCertIn.ContractInOK, hm, Bool.false_eq_true, ↓reduceIte] at hi
  exact hi

/-- Macro vertices recur: a walk avoiding them would lengthen its recorded
backward chain forever, beyond the bound. -/
theorem macroIn_recurrent (C : WordCertIn V) (Gout : WGraph V) (Cov : Covering G c n₀)
    (h : ∀ i, C.ContractInOK Gout ⟨Cov.v i, Cov.w i, Cov.v (i + 1)⟩) (N : ℕ) :
    ∃ i, N ≤ i ∧ C.base.isMacro (Cov.v i) = true := by
  by_contra hno
  push Not at hno
  have hno' : ∀ i, N ≤ i → C.base.isMacro (Cov.v i) = false := fun i hi => by
    simpa using hno i hi
  let len : ℕ → ℕ := fun i => ((C.chainIn (Cov.v i)).map (fun x => x.1.length)).getD 0
  have hinc : ∀ i, N ≤ i → len i < len (i + 1) ∧ len (i + 1) ≤ C.bound := by
    intro i hi
    obtain ⟨w', b, hc, hb, hcase⟩ := chainIn_step C Gout Cov h i (hno' (i + 1) (by omega))
    rcases hcase with ⟨hm, _, _⟩ | ⟨_, w'', hc'', hw⟩
    · rw [hno' i hi] at hm
      exact absurd hm Bool.false_ne_true
    · have h1 := Cov.length_pos i
      simp only [len, hc, hc'', Option.map_some, Option.getD_some, hw, List.length_append]
      rw [hw, List.length_append] at hb
      omega
  have hgrow : ∀ k, len N + k ≤ len (N + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := (hinc (N + k) (by omega)).1
      rw [show N + (k + 1) = N + k + 1 by omega]
      omega
  have h1 := hgrow (C.bound + 1)
  have h2 := (hinc (N + C.bound) (by omega)).2
  rw [show N + C.bound + 1 = N + (C.bound + 1) by omega] at h2
  omega

/-- Between a macro visit at `i` and the next macro visit, the recorded chains
are exactly the words read since `i`. -/
theorem chainIn_realized (C : WordCertIn V) (Gout : WGraph V) (Cov : Covering G c n₀)
    (h : ∀ i, C.ContractInOK Gout ⟨Cov.v i, Cov.w i, Cov.v (i + 1)⟩) (i : ℕ)
    (hi : C.base.isMacro (Cov.v i) = true) :
    ∀ k, (∀ m, i < m → m ≤ i + (k + 1) → C.base.isMacro (Cov.v m) = false) →
      C.chainIn (Cov.v (i + (k + 1))) = some (Covering.concatFrom Cov.w i (k + 1), Cov.v i) := by
  intro k
  induction k with
  | zero =>
    intro hnm
    obtain ⟨w', b, hc, _, hcase⟩ := chainIn_step C Gout Cov h i (hnm (i + 1) (by omega) (by omega))
    rcases hcase with ⟨_, hw, hb⟩ | ⟨hm, _, _, _⟩
    · rw [hc, hw, hb, Covering.concatFrom_one]
    · rw [hi] at hm
      exact absurd hm (by simp)
  | succ k ih =>
    intro hnm
    have hprev := ih (fun m hm1 hm2 => hnm m hm1 (by omega))
    obtain ⟨w', b, hc, _, hcase⟩ := chainIn_step C Gout Cov h (i + (k + 1))
      (hnm (i + (k + 1) + 1) (by omega) (by omega))
    rcases hcase with ⟨hm, _, _⟩ | ⟨_, w'', hc'', hw⟩
    · rw [hnm (i + (k + 1)) (by omega) (by omega)] at hm
      exact absurd hm Bool.false_ne_true
    · rw [hprev] at hc''
      obtain ⟨rfl, rfl⟩ := Option.some_injective _ hc'' |> Prod.mk.inj
      rw [show i + (k + 1 + 1) = i + (k + 1) + 1 by omega, hc, hw,
        Covering.concatFrom_succ_right Cov.w i (k + 1)]

/-- From a macro vertex the walk reaches the next macro vertex through an edge of `Gout`. -/
theorem macroIn_step (C : WordCertIn V) (Gout : WGraph V) (Cov : Covering G c n₀)
    (h : ∀ i, C.ContractInOK Gout ⟨Cov.v i, Cov.w i, Cov.v (i + 1)⟩)
    (i : ℕ) (hi : C.base.isMacro (Cov.v i) = true) :
    ∃ j, i < j ∧ C.base.isMacro (Cov.v j) = true ∧
      (⟨Cov.v i, Covering.concatFrom Cov.w i (j - i), Cov.v j⟩ : WEdge V) ∈ Gout := by
  classical
  have hex : ∃ j, i + 1 ≤ j ∧ C.base.isMacro (Cov.v j) = true :=
    macroIn_recurrent C Gout Cov h (i + 1)
  let j := Nat.find hex
  have hj : i + 1 ≤ j ∧ C.base.isMacro (Cov.v j) = true := Nat.find_spec hex
  have hmin : ∀ m, i < m → m < j → C.base.isMacro (Cov.v m) = false := by
    intro m hm1 hm2
    have := Nat.find_min hex hm2
    push Not at this
    simpa using this (by omega)
  refine ⟨j, by omega, hj.2, ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hj.1
  have hedge := h (i + k)
  rw [show i + k + 1 = j by omega] at hedge
  simp only [WordCertIn.ContractInOK, hj.2, ↓reduceIte] at hedge
  cases k with
  | zero =>
    rcases hedge with ⟨_, hmem⟩ | ⟨hm, _⟩
    · rw [show j - i = 1 by omega, Covering.concatFrom_one]
      simpa using hmem
    · simp only [Nat.add_zero] at hm
      rw [hi] at hm
      exact absurd hm (by simp)
  | succ k =>
    have hnm : C.base.isMacro (Cov.v (i + (k + 1))) = false := hmin _ (by omega) (by omega)
    rcases hedge with ⟨hm, _⟩ | ⟨_, w'', b, hc, hmem⟩
    · rw [hnm] at hm
      exact absurd hm Bool.false_ne_true
    · have hreal := chainIn_realized C Gout Cov h i hi k
        (fun m hm1 hm2 => hmin m hm1 (by omega))
      rw [hreal] at hc
      obtain ⟨rfl, rfl⟩ := Option.some_injective _ hc |> Prod.mk.inj
      rw [show j - i = (k + 1) + 1 by omega, Covering.concatFrom_succ_right,
        show i + (k + 1) = i + (k + 1) by rfl]
      rw [show j = i + (k + 1) + 1 by omega] at hmem ⊢
      exact hmem

/-- Tail preservation under in-degree-one contraction. -/
theorem contractIn_tail (C : WordCertIn V) (Gout : WGraph V) (Cov : Covering G c n₀)
    (h : ∀ i, C.ContractInOK Gout ⟨Cov.v i, Cov.w i, Cov.v (i + 1)⟩) :
    ∃ n₁, n₀ ≤ n₁ ∧ Covers Gout c n₁ := by
  classical
  obtain ⟨i₀, -, hi₀⟩ := macroIn_recurrent C Gout Cov h 0
  have hB := macroIn_step C Gout Cov h
  let nxt : ℕ → ℕ := fun i =>
    if hi : C.base.isMacro (Cov.v i) = true then Classical.choose (hB i hi) else i + 1
  have hnxt : ∀ i, C.base.isMacro (Cov.v i) = true → i < nxt i ∧
      C.base.isMacro (Cov.v (nxt i)) = true ∧
      (⟨Cov.v i, Covering.concatFrom Cov.w i (nxt i - i), Cov.v (nxt i)⟩ : WEdge V) ∈ Gout := by
    intro i hi
    have hspec := Classical.choose_spec (hB i hi)
    simp only [nxt, dif_pos hi]
    exact hspec
  let idx : ℕ → ℕ := fun m => nxt^[m] i₀
  have hidx : ∀ m, C.base.isMacro (Cov.v (idx m)) = true := by
    intro m
    induction m with
    | zero => exact hi₀
    | succ m ih =>
      show C.base.isMacro (Cov.v (nxt^[m + 1] i₀)) = true
      rw [Function.iterate_succ_apply']
      exact (hnxt _ ih).2.1
  have hidx_succ : ∀ m, idx (m + 1) = nxt (idx m) := fun m => Function.iterate_succ_apply' _ _ _
  have hlt : ∀ m, idx m < idx (m + 1) := fun m => by rw [hidx_succ]; exact (hnxt _ (hidx m)).1
  refine ⟨Cov.t i₀, by have := Cov.le_t i₀; omega, ⟨⟨fun m => Cov.v (idx m),
    fun m => Covering.concatFrom Cov.w (idx m) (idx (m + 1) - idx m),
    fun m => Cov.t (idx m), rfl, ?_, ?_, ?_, ?_⟩⟩⟩
  · intro m
    have := (hnxt _ (hidx m)).2.2
    rw [← hidx_succ] at this
    exact this
  · intro m
    exact Cov.concatFrom_ne_nil _ _ (by have := hlt m; omega)
  · intro m
    have := Cov.t_concatFrom (idx m) (idx (m + 1) - idx m)
    rw [show idx m + (idx (m + 1) - idx m) = idx (m + 1) by have := hlt m; omega] at this
    exact this
  · intro m k hk
    exact Cov.output_concatFrom _ _ _ hk

end ContractIn

section StageIn

variable {V : Type*}

/-- Tail preservation for one in-direction stage: removal of certified blocks
plus in-degree-one contraction. -/
theorem WordCertIn.stage_tail (C : WordCertIn V) (Gin Gout : WGraph V)
    (hcheck : ∀ e ∈ Gin, C.EdgeConditionIn Gout e) (c : ℕ → ℤ)
    (hnonper : ¬ EventuallyPeriodic c) (n₀ : ℕ) (hcov : Covers Gin c n₀) :
    ∃ n₁, n₀ ≤ n₁ ∧ Covers Gout c n₁ := by
  obtain ⟨Cov⟩ := hcov
  let R : RankCertificate V :=
    ⟨C.base.owner, C.base.rank, fun _ => false, fun _ => 0, fun _ => 0, fun _ _ => 0⟩
  have hstep : ∀ n, R.owner (Cov.v n) ≠ R.owner (Cov.v (n + 1)) →
      R.rank (R.owner (Cov.v (n + 1))) < R.rank (R.owner (Cov.v n)) := by
    intro n hne
    have h := hcheck _ (Cov.edge n)
    simp only [WordCertIn.EdgeConditionIn] at h
    rw [if_neg hne] at h
    exact h
  obtain ⟨N, hN⟩ := rank_eventually_constant R Cov.v hstep
  let Cov' := Cov.shift N
  have ho : ∀ i, C.base.owner (Cov'.v i) = C.base.owner (Cov.v N) := fun i => hN (N + i) (by omega)
  have hsame : ∀ i, C.base.owner (Cov'.v i) = C.base.owner (Cov'.v (i + 1)) := fun i => by
    rw [ho i, ho (i + 1)]
  have hedge : ∀ i, C.EdgeConditionIn Gout ⟨Cov'.v i, Cov'.w i, Cov'.v (i + 1)⟩ :=
    fun i => hcheck _ (Cov'.edge i)
  have hN₀ : n₀ ≤ Cov.t N := by have := Cov.le_t N; omega
  by_cases hret : C.base.retained (C.base.owner (Cov.v N)) = true
  · have hcon : ∀ i, C.ContractInOK Gout ⟨Cov'.v i, Cov'.w i, Cov'.v (i + 1)⟩ := by
      intro i
      have h := hedge i
      simp only [WordCertIn.EdgeConditionIn] at h
      rw [if_pos (hsame i)] at h
      rw [ho i, if_pos hret] at h
      exact h
    obtain ⟨n₁, hn₁, hc⟩ := contractIn_tail C Gout Cov' hcon
    exact ⟨n₁, le_trans hN₀ hn₁, hc⟩
  · exfalso
    apply hnonper
    have hph : ∀ i, C.base.PhaseOK ⟨Cov'.v i, Cov'.w i, Cov'.v (i + 1)⟩ := by
      intro i
      have h := hedge i
      simp only [WordCertIn.EdgeConditionIn] at h
      rw [if_pos (hsame i)] at h
      rw [ho i, if_neg hret] at h
      exact h
    exact phase_output_periodic C.base Cov' (C.base.owner (Cov.v N)) ho hph

end StageIn

end MathPaper
