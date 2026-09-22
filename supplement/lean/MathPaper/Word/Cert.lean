import MathPaper.Word.Graph
import MathPaper.Certificate

/-! Stage certificates for word-labelled graphs (audit-02 §3–§4, W2–W3) in the
rank/phase style of the first version: blocks are not required to be SCCs.
A block is either uncertified (`retained = true`; its internal edges are
contracted onto macro vertices) or certified by the weighted phase test.
`stage_tail` is the tail-preservation statement `R` + `W3-d` combined. -/
namespace MathPaper

structure WordCert (V : Type*) where
  owner : V → ℕ
  rank : ℕ → ℕ
  retained : ℕ → Bool
  period : ℕ → ℕ
  phase : V → ℕ
  label : ℕ → ℕ → ℤ
  isMacro : V → Bool
  chain : V → Option (List ℤ × V)

namespace WordCert

variable {V : Type*} (C : WordCert V)

/-- (PHASE-W) for every letter, plus the phase increment along the edge. -/
def PhaseOK (e : WEdge V) : Prop :=
  0 < C.period (C.owner e.src) ∧ C.phase e.src < C.period (C.owner e.src) ∧
  C.phase e.dst = (C.phase e.src + e.word.length) % C.period (C.owner e.src) ∧
  ∀ k, k < e.word.length →
    e.word.getD k 0 = C.label (C.owner e.src) ((C.phase e.src + k) % C.period (C.owner e.src))

/-- Contraction data: from a macro vertex the deterministic chain through
non-macro vertices yields an edge of `Gout`; at a non-macro vertex the
recorded chain is consistent with the unique continuation. -/
def ContractOK (Gout : WGraph V) (e : WEdge V) : Prop :=
  if C.isMacro e.src = true then
    (C.isMacro e.dst = true ∧ e ∈ Gout) ∨
    (C.isMacro e.dst = false ∧ ∃ w'' b, C.chain e.dst = some (w'', b) ∧
      (⟨e.src, e.word ++ w'', b⟩ : WEdge V) ∈ Gout)
  else
    ∃ w' b, C.chain e.src = some (w', b) ∧
      ((C.isMacro e.dst = true ∧ w' = e.word ∧ b = e.dst) ∨
       (C.isMacro e.dst = false ∧ ∃ w'', C.chain e.dst = some (w'', b) ∧ w' = e.word ++ w''))

def EdgeCondition (Gout : WGraph V) (e : WEdge V) : Prop :=
  if C.owner e.src = C.owner e.dst then
    (if C.retained (C.owner e.src) = true then C.ContractOK Gout e else C.PhaseOK e)
  else C.rank (C.owner e.dst) < C.rank (C.owner e.src)

end WordCert

section Phase

variable {V : Type*} {G : WGraph V} {c : ℕ → ℤ} {n₀ : ℕ}

/-- Every time is inside exactly one word of the walk. -/
theorem Covering.time_decomp (Cov : Covering G c n₀) (T : ℕ) :
    ∃ i k, k < (Cov.w i).length ∧ Cov.t 0 + T = Cov.t i + k := by
  induction T with
  | zero => exact ⟨0, 0, Cov.length_pos 0, by simp⟩
  | succ T ih =>
    obtain ⟨i, k, hk, hT⟩ := ih
    by_cases hlt : k + 1 < (Cov.w i).length
    · exact ⟨i, k + 1, hlt, by omega⟩
    · refine ⟨i + 1, 0, Cov.length_pos (i + 1), ?_⟩
      have := Cov.t_succ i
      omega

/-- A walk whose edges all satisfy the phase test inside one block has purely
periodic output of period `d` (audit-02 命題 W2). -/
theorem phase_output_periodic (C : WordCert V) (Cov : Covering G c n₀) (o : ℕ)
    (ho : ∀ i, C.owner (Cov.v i) = o)
    (hph : ∀ i, C.PhaseOK ⟨Cov.v i, Cov.w i, Cov.v (i + 1)⟩) :
    EventuallyPeriodic c := by
  have hd : 0 < C.period o := by
    have := (hph 0).1
    simpa [ho] using this
  have hstep : ∀ i, C.phase (Cov.v (i + 1)) =
      (C.phase (Cov.v i) + (Cov.w i).length) % C.period o := by
    intro i
    have := (hph i).2.2.1
    simpa [ho] using this
  have hlab : ∀ i k, k < (Cov.w i).length →
      (Cov.w i).getD k 0 = C.label o ((C.phase (Cov.v i) + k) % C.period o) := by
    intro i k hk
    have := (hph i).2.2.2 k hk
    simpa [ho] using this
  have hph0 : C.phase (Cov.v 0) < C.period o := by
    have := (hph 0).2.1
    simpa [ho] using this
  have hphase : ∀ i, C.phase (Cov.v i) =
      (C.phase (Cov.v 0) + (Cov.t i - Cov.t 0)) % C.period o := by
    intro i
    induction i with
    | zero => simp [Nat.mod_eq_of_lt hph0]
    | succ i ih =>
      rw [hstep i, ih, Nat.mod_add_mod, Cov.t_succ i]
      congr 1
      have := Cov.t_mono (Nat.zero_le i)
      omega
  have hout : ∀ T, c (Cov.t 0 + T) = C.label o ((C.phase (Cov.v 0) + T) % C.period o) := by
    intro T
    obtain ⟨i, k, hk, hT⟩ := Cov.time_decomp T
    rw [hT, ← Cov.output i k hk, hlab i k hk, hphase i, Nat.mod_add_mod]
    congr 2
    have := Cov.t_mono (Nat.zero_le i)
    omega
  refine ⟨Cov.t 0, C.period o, hd, fun n hn => ?_⟩
  obtain ⟨T, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_assoc, hout (T + C.period o), hout T, ← Nat.add_assoc, Nat.add_mod_right]

end Phase

section Contract

variable {V : Type*} {G : WGraph V} {c : ℕ → ℤ} {n₀ : ℕ}

/-- The recorded chain of a non-macro vertex is realized by the walk (W3-c/W3-d). -/
theorem chain_realized (C : WordCert V) (Gout : WGraph V) (Cov : Covering G c n₀)
    (h : ∀ i, C.ContractOK Gout ⟨Cov.v i, Cov.w i, Cov.v (i + 1)⟩) :
    ∀ n (w' : List ℤ) (k : ℕ) (b : V), w'.length ≤ n → C.isMacro (Cov.v k) = false →
      C.chain (Cov.v k) = some (w', b) →
      ∃ j, k < j ∧ C.isMacro (Cov.v j) = true ∧ Cov.v j = b ∧
        Covering.concatFrom Cov.w k (j - k) = w' := by
  intro n
  induction n with
  | zero =>
    intro w' k b hn hk hc
    have hw : w' = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hn)
    subst hw
    have hk' := h k
    simp only [WordCert.ContractOK, hk, Bool.false_eq_true, ↓reduceIte] at hk'
    obtain ⟨w₀, b₀, hc₀, hcase⟩ := hk'
    rw [hc] at hc₀
    obtain ⟨rfl, rfl⟩ := Option.some_injective _ hc₀ |> Prod.mk.inj
    rcases hcase with ⟨_, hw, _⟩ | ⟨_, w'', _, hw⟩
    · exact absurd hw.symm (Cov.nonempty k)
    · exact absurd (List.append_eq_nil_iff.mp hw.symm).1 (Cov.nonempty k)
  | succ n ih =>
    intro w' k b hn hk hc
    have hk' := h k
    simp only [WordCert.ContractOK, hk, Bool.false_eq_true, ↓reduceIte] at hk'
    obtain ⟨w₀, b₀, hc₀, hcase⟩ := hk'
    rw [hc] at hc₀
    obtain ⟨rfl, rfl⟩ := Option.some_injective _ hc₀ |> Prod.mk.inj
    rcases hcase with ⟨hm, hw, hb⟩ | ⟨hm, w'', hc'', hw⟩
    · refine ⟨k + 1, by omega, hm, hb.symm, ?_⟩
      rw [show k + 1 - k = 1 by omega, Covering.concatFrom_one, hw]
    · have hlen : w''.length ≤ n := by
        have h1 := Cov.length_pos k
        have h2 : w'.length = (Cov.w k).length + w''.length := by
          rw [hw, List.length_append]
        omega
      obtain ⟨j, hj, hmj, hbj, hcj⟩ := ih w'' (k + 1) b hlen hm hc''
      refine ⟨j, by omega, hmj, hbj, ?_⟩
      rw [show j - k = (j - (k + 1)) + 1 by omega, Covering.concatFrom_succ, hcj, hw]

/-- Some macro vertex is visited (W3-c): otherwise chain lengths decrease forever. -/
theorem macro_visited (C : WordCert V) (Gout : WGraph V) (Cov : Covering G c n₀)
    (h : ∀ i, C.ContractOK Gout ⟨Cov.v i, Cov.w i, Cov.v (i + 1)⟩) :
    ∃ i, C.isMacro (Cov.v i) = true := by
  by_contra hno
  push Not at hno
  have hno' : ∀ i, C.isMacro (Cov.v i) = false := fun i => by simpa using hno i
  let len : ℕ → ℕ := fun i => ((C.chain (Cov.v i)).map (fun x => x.1.length)).getD 0
  have hdec : ∀ i, len (i + 1) < len i := by
    intro i
    have hi := h i
    simp only [WordCert.ContractOK, hno' i, Bool.false_eq_true, ↓reduceIte] at hi
    obtain ⟨w', b, hc, hcase⟩ := hi
    rcases hcase with ⟨hm, _, _⟩ | ⟨_, w'', hc'', hw⟩
    · rw [hno' (i + 1)] at hm
      exact absurd hm Bool.false_ne_true
    · have h1 := Cov.length_pos i
      simp only [len, hc, hc'', Option.map_some, Option.getD_some, hw, List.length_append]
      omega
  have hbound : ∀ i, len i + i ≤ len 0 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => have := hdec i; omega
  have := hbound (len 0 + 1)
  omega

/-- From a macro vertex the walk reaches the next macro vertex through an edge of `Gout`. -/
theorem macro_step (C : WordCert V) (Gout : WGraph V) (Cov : Covering G c n₀)
    (h : ∀ i, C.ContractOK Gout ⟨Cov.v i, Cov.w i, Cov.v (i + 1)⟩)
    (i : ℕ) (hi : C.isMacro (Cov.v i) = true) :
    ∃ j, i < j ∧ C.isMacro (Cov.v j) = true ∧
      (⟨Cov.v i, Covering.concatFrom Cov.w i (j - i), Cov.v j⟩ : WEdge V) ∈ Gout := by
  have hi' := h i
  simp only [WordCert.ContractOK, hi, ↓reduceIte] at hi'
  rcases hi' with ⟨hm, hmem⟩ | ⟨hm, w'', b, hc, hmem⟩
  · refine ⟨i + 1, by omega, hm, ?_⟩
    rw [show i + 1 - i = 1 by omega, Covering.concatFrom_one]
    exact hmem
  · obtain ⟨j, hj, hmj, hbj, hcj⟩ :=
      chain_realized C Gout Cov h w''.length w'' (i + 1) b le_rfl hm hc
    refine ⟨j, by omega, hmj, ?_⟩
    rw [show j - i = (j - (i + 1)) + 1 by omega, Covering.concatFrom_succ, hcj, hbj]
    exact hmem

/-- Tail preservation under contraction (audit-02 系 W3-d). -/
theorem contract_tail (C : WordCert V) (Gout : WGraph V) (Cov : Covering G c n₀)
    (h : ∀ i, C.ContractOK Gout ⟨Cov.v i, Cov.w i, Cov.v (i + 1)⟩) :
    ∃ n₁, n₀ ≤ n₁ ∧ Covers Gout c n₁ := by
  classical
  obtain ⟨i₀, hi₀⟩ := macro_visited C Gout Cov h
  have hB := macro_step C Gout Cov h
  let nxt : ℕ → ℕ := fun i =>
    if hi : C.isMacro (Cov.v i) = true then Classical.choose (hB i hi) else i + 1
  have hnxt : ∀ i, C.isMacro (Cov.v i) = true → i < nxt i ∧ C.isMacro (Cov.v (nxt i)) = true ∧
      (⟨Cov.v i, Covering.concatFrom Cov.w i (nxt i - i), Cov.v (nxt i)⟩ : WEdge V) ∈ Gout := by
    intro i hi
    have hspec := Classical.choose_spec (hB i hi)
    simp only [nxt, dif_pos hi]
    exact hspec
  let idx : ℕ → ℕ := fun m => nxt^[m] i₀
  have hidx : ∀ m, C.isMacro (Cov.v (idx m)) = true := by
    intro m
    induction m with
    | zero => exact hi₀
    | succ m ih =>
      show C.isMacro (Cov.v (nxt^[m + 1] i₀)) = true
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

end Contract

section Stage

variable {V : Type*}

/-- Ranks stabilize, so the walk stays in one block (reuses the first-version lemma). -/
theorem WordCert.owner_eventually_constant (C : WordCert V) (Gin Gout : WGraph V)
    (hcheck : ∀ e ∈ Gin, C.EdgeCondition Gout e) {c : ℕ → ℤ} {n₀ : ℕ}
    (Cov : Covering Gin c n₀) :
    ∃ N, ∀ n, N ≤ n → C.owner (Cov.v n) = C.owner (Cov.v N) := by
  let R : RankCertificate V :=
    ⟨C.owner, C.rank, fun _ => false, fun _ => 0, fun _ => 0, fun _ _ => 0⟩
  have hstep : ∀ n, R.owner (Cov.v n) ≠ R.owner (Cov.v (n + 1)) →
      R.rank (R.owner (Cov.v (n + 1))) < R.rank (R.owner (Cov.v n)) := by
    intro n hne
    have h := hcheck _ (Cov.edge n)
    simp only [WordCert.EdgeCondition] at h
    rw [if_neg hne] at h
    exact h
  exact rank_eventually_constant R Cov.v hstep

/-- Tail preservation for one stage: removal of certified blocks plus contraction
(audit-02 命題 R と系 W3-d). The output graph is covered from a later time. -/
theorem WordCert.stage_tail (C : WordCert V) (Gin Gout : WGraph V)
    (hcheck : ∀ e ∈ Gin, C.EdgeCondition Gout e) (c : ℕ → ℤ)
    (hnonper : ¬ EventuallyPeriodic c) (n₀ : ℕ) (hcov : Covers Gin c n₀) :
    ∃ n₁, n₀ ≤ n₁ ∧ Covers Gout c n₁ := by
  obtain ⟨Cov⟩ := hcov
  obtain ⟨N, hN⟩ := C.owner_eventually_constant Gin Gout hcheck Cov
  let Cov' := Cov.shift N
  have ho : ∀ i, C.owner (Cov'.v i) = C.owner (Cov.v N) := fun i => hN (N + i) (by omega)
  have hsame : ∀ i, C.owner (Cov'.v i) = C.owner (Cov'.v (i + 1)) := fun i => by
    rw [ho i, ho (i + 1)]
  have hedge : ∀ i, C.EdgeCondition Gout ⟨Cov'.v i, Cov'.w i, Cov'.v (i + 1)⟩ :=
    fun i => hcheck _ (Cov'.edge i)
  have hN₀ : n₀ ≤ Cov.t N := by have := Cov.le_t N; omega
  by_cases hret : C.retained (C.owner (Cov.v N)) = true
  · have hcon : ∀ i, C.ContractOK Gout ⟨Cov'.v i, Cov'.w i, Cov'.v (i + 1)⟩ := by
      intro i
      have h := hedge i
      simp only [WordCert.EdgeCondition] at h
      rw [if_pos (hsame i)] at h
      rw [ho i, if_pos hret] at h
      exact h
    obtain ⟨n₁, hn₁, hc⟩ := contract_tail C Gout Cov' hcon
    exact ⟨n₁, le_trans hN₀ hn₁, hc⟩
  · exfalso
    apply hnonper
    have hph : ∀ i, C.PhaseOK ⟨Cov'.v i, Cov'.w i, Cov'.v (i + 1)⟩ := by
      intro i
      have h := hedge i
      simp only [WordCert.EdgeCondition] at h
      rw [if_pos (hsame i)] at h
      rw [ho i, if_neg hret] at h
      exact h
    exact phase_output_periodic C Cov' (C.owner (Cov.v N)) ho hph

end Stage

end MathPaper
