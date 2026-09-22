import MathPaper.Word.Pipeline.Data

/-! The verified stage checker. `CheckData` is produced by an untrusted
computation (SCC, BFS, contraction); only `checkStage_sound` matters for the
proof: acceptance implies `EdgeCondition` for every edge of the semantic input
graph, with the certificate `certOf D` and the semantic output graph. -/
namespace MathPaper.Pipe

structure CheckData where
  W' : WTable
  owner : Array ℕ
  rank : Array ℕ
  retained : Array Bool
  period : Array ℕ
  phase : Array ℕ
  labels : Array (Array ℤ)
  isMacro : Array Bool
  chainTab : Array (Option (ℕ × ℕ))
  gout : Array PEdge
  goutIdx : Array (Option ℕ)
  newId : Array ℕ
  nout : ℕ

/-- The abstract certificate read off the arrays (total functions, defaults for
missing entries; a wrong default only makes the check fail). -/
def certOf (D : CheckData) : WordCert ℕ where
  owner := fun v => D.owner.getD v 0
  rank := fun o => D.rank.getD o 0
  retained := fun o => D.retained.getD o false
  period := fun o => D.period.getD o 0
  phase := fun v => D.phase.getD v 0
  label := fun o i => (D.labels.getD o #[]).getD i 0
  isMacro := fun v => D.isMacro.getD v false
  chain := fun v => (D.chainTab.getD v none).map (fun x => ((wordOf D.W' x.1).toList, x.2))

def phaseCheck (W : WTable) (D : CheckData) (pe : PEdge) : Bool :=
  let w := wordOf W pe.wid
  let o := D.owner.getD pe.src 0
  let d := D.period.getD o 0
  let ph := D.phase.getD pe.src 0
  let lab := D.labels.getD o #[]
  decide (0 < d) && decide (ph < d) && decide (D.phase.getD pe.dst 0 = (ph + w.size) % d) &&
    allIdx w.size (fun i => decide (w.getD i 0 = lab.getD ((ph + i) % d) 0))

theorem phaseCheck_sound (W : WTable) (D : CheckData) (pe : PEdge)
    (h : phaseCheck W D pe = true) : (certOf D).PhaseOK (deref W pe) := by
  simp only [phaseCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, ?_, ?_⟩
  · simpa [certOf, deref] using h3
  · intro k hk
    simp only [deref, Array.length_toList] at hk
    have := allIdx_spec h4 hk
    simp only [decide_eq_true_eq] at this
    simpa [certOf, deref, toList_getD] using this

def contractCheck (W : WTable) (D : CheckData) (k : ℕ) (pe : PEdge) : Bool :=
  let w := wordOf W pe.wid
  if D.isMacro.getD pe.src false then
    let target : Option (Array ℤ × ℕ) :=
      if D.isMacro.getD pe.dst false then some (w, pe.dst)
      else match D.chainTab.getD pe.dst none with
        | none => none
        | some (wid'', b) => some (w ++ wordOf D.W' wid'', b)
    match target, D.goutIdx.getD k none with
    | some (wexp, b), some idx =>
      match D.gout[idx]? with
      | some ge => decide (ge.src = pe.src) && decide (ge.dst = b) &&
          decide (wordOf D.W' ge.wid = wexp)
      | none => false
    | _, _ => false
  else
    match D.chainTab.getD pe.src none with
    | none => false
    | some (wid', b) =>
      let w' := wordOf D.W' wid'
      if D.isMacro.getD pe.dst false then decide (w' = w) && decide (b = pe.dst)
      else match D.chainTab.getD pe.dst none with
        | none => false
        | some (wid'', b') => decide (b' = b) && decide (w' = w ++ wordOf D.W' wid'')

theorem gout_mem (D : CheckData) (idx : ℕ) (ge : PEdge) (h : D.gout[idx]? = some ge) :
    deref D.W' ge ∈ sem D.W' D.gout :=
  mem_sem _ _ _ (mem_of_getElem? _ _ _ h)

theorem contractCheck_sound (W : WTable) (D : CheckData) (k : ℕ) (pe : PEdge)
    (h : contractCheck W D k pe = true) :
    (certOf D).ContractOK (sem D.W' D.gout) (deref W pe) := by
  unfold WordCert.ContractOK
  simp only [certOf, deref]
  unfold contractCheck at h
  by_cases hms : D.isMacro.getD pe.src false = true
  · rw [if_pos hms] at h
    rw [if_pos hms]
    by_cases hmd : D.isMacro.getD pe.dst false = true
    · rw [if_pos hmd] at h
      left
      refine ⟨hmd, ?_⟩
      cases hidx : D.goutIdx.getD k none with
      | none => simp [hidx] at h
      | some idx =>
        simp only [hidx] at h
        cases hge : D.gout[idx]? with
        | none => simp [hge] at h
        | some ge =>
          simp only [hge, Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨hs, hd⟩, hw⟩ := h
          have := gout_mem D idx ge hge
          simp only [deref] at this
          rw [hs, hd, hw] at this
          exact this
    · rw [if_neg hmd] at h
      right
      refine ⟨by simpa using hmd, ?_⟩
      cases hct : D.chainTab.getD pe.dst none with
      | none => simp [hct] at h
      | some x =>
        obtain ⟨wid'', b⟩ := x
        simp only [hct] at h
        cases hidx : D.goutIdx.getD k none with
        | none => simp [hidx] at h
        | some idx =>
          simp only [hidx] at h
          cases hge : D.gout[idx]? with
          | none => simp [hge] at h
          | some ge =>
            simp only [hge, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨hs, hd⟩, hw⟩ := h
            refine ⟨(wordOf D.W' wid'').toList, b, by simp, ?_⟩
            have := gout_mem D idx ge hge
            simp only [deref] at this
            rw [hs, hd, hw, Array.toList_append] at this
            exact this
  · rw [if_neg hms] at h
    rw [if_neg hms]
    cases hct : D.chainTab.getD pe.src none with
    | none => simp [hct] at h
    | some x =>
      obtain ⟨wid', b⟩ := x
      simp only [hct] at h
      refine ⟨(wordOf D.W' wid').toList, b, by simp, ?_⟩
      by_cases hmd : D.isMacro.getD pe.dst false = true
      · rw [if_pos hmd] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        left
        exact ⟨hmd, by rw [h.1], h.2⟩
      · rw [if_neg hmd] at h
        right
        refine ⟨by simpa using hmd, ?_⟩
        cases hct' : D.chainTab.getD pe.dst none with
        | none => simp [hct'] at h
        | some y =>
          obtain ⟨wid'', b'⟩ := y
          simp only [hct', Bool.and_eq_true, decide_eq_true_eq] at h
          refine ⟨(wordOf D.W' wid'').toList, by simp [h.1], ?_⟩
          rw [h.2, Array.toList_append]

def edgeCheck (W : WTable) (D : CheckData) (k : ℕ) (pe : PEdge) : Bool :=
  let o := D.owner.getD pe.src 0
  let o' := D.owner.getD pe.dst 0
  if o = o' then
    (if D.retained.getD o false then contractCheck W D k pe else phaseCheck W D pe)
  else decide (D.rank.getD o' 0 < D.rank.getD o 0)

theorem edgeCheck_sound (W : WTable) (D : CheckData) (k : ℕ) (pe : PEdge)
    (h : edgeCheck W D k pe = true) :
    (certOf D).EdgeCondition (sem D.W' D.gout) (deref W pe) := by
  unfold WordCert.EdgeCondition
  unfold edgeCheck at h
  simp only [certOf, deref]
  by_cases ho : D.owner.getD pe.src 0 = D.owner.getD pe.dst 0
  · rw [if_pos ho] at h
    rw [if_pos ho]
    by_cases hr : D.retained.getD (D.owner.getD pe.src 0) false = true
    · rw [if_pos hr] at h
      rw [if_pos hr]
      exact contractCheck_sound W D k pe h
    · rw [if_neg hr] at h
      rw [if_neg hr]
      exact phaseCheck_sound W D pe h
  · rw [if_neg ho] at h
    rw [if_neg ho]
    simpa using h

def checkStage (S : CStage) (D : CheckData) : Bool :=
  allIdx S.edges.size (fun k => edgeCheck S.W D k (S.edges.getD k default))

theorem checkStage_sound (S : CStage) (D : CheckData) (h : checkStage S D = true) :
    ∀ e ∈ S.sem, (certOf D).EdgeCondition (sem D.W' D.gout) e := by
  rintro e ⟨pe, hpe, rfl⟩
  obtain ⟨k, hk, hke⟩ := Array.mem_iff_getElem.mp hpe
  have hc := allIdx_spec h hk
  rw [getD_eq_getElem _ _ _ hk, hke] at hc
  exact edgeCheck_sound S.W D k pe hc

end MathPaper.Pipe
