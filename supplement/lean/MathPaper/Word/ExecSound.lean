import WordExec
import MathPaper.Word.Bidir

/-! Soundness of the executable pipeline `WordExec` (5/3 addition). The proofs
follow those of `MathPaper.Word.Pipeline` for the copied definitions, together
with the in-direction checker and the stage passes. They are checked by the
kernel; only the finite evaluation of `WordExec.wordPipelineBidir` is accepted
by `native_decide`. -/
namespace WordExec

open MathPaper

theorem stepRes_eq (a p binv q : Nat) (c : Int) : stepRes a p binv q c = MathPaper.stepRes a p binv q c := rfl

theorem runWord_eq (a p binv : Nat) : ∀ (w : List Int) (q : Nat), runWord a p binv w q = MathPaper.runWord a p binv w q
  | [], q => rfl
  | c :: w, q => by
    simp only [runWord, MathPaper.runWord, stepRes_eq]
    split <;> simp [runWord_eq a p binv w]

def deref (W : WTable) (pe : PEdge) : WEdge ℕ := ⟨pe.src, (wordOf W pe.wid).toList, pe.dst⟩

def sem (W : WTable) (edges : Array PEdge) : WGraph ℕ := {e | ∃ pe ∈ edges, e = deref W pe}

theorem mem_sem (W : WTable) (edges : Array PEdge) (pe : PEdge) (h : pe ∈ edges) :
    deref W pe ∈ sem W edges := ⟨pe, h, rfl⟩

def CStage.sem (S : CStage) : WGraph ℕ := WordExec.sem S.W S.edges

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

def certOf (D : CheckData) : WordCert ℕ where
  owner := fun v => D.owner.getD v 0
  rank := fun o => D.rank.getD o 0
  retained := fun o => D.retained.getD o false
  period := fun o => D.period.getD o 0
  phase := fun v => D.phase.getD v 0
  label := fun o i => (D.labels.getD o #[]).getD i 0
  isMacro := fun v => D.isMacro.getD v false
  chain := fun v => (D.chainTab.getD v none).map (fun x => ((wordOf D.W' x.1).toList, x.2))

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

theorem checkStage_sound (S : CStage) (D : CheckData) (h : checkStage S D = true) :
    ∀ e ∈ S.sem, (certOf D).EdgeCondition (sem D.W' D.gout) e := by
  rintro e ⟨pe, hpe, rfl⟩
  obtain ⟨k, hk, hke⟩ := Array.mem_iff_getElem.mp hpe
  have hc := allIdx_spec h hk
  rw [getD_eq_getElem _ _ _ hk, hke] at hc
  exact edgeCheck_sound S.W D k pe hc

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
      simp [hq0, runWord_eq, hrun]

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

theorem sem_empty (W : WTable) (gout : Array PEdge) (h : gout.isEmpty = true) :
    sem W gout = ∅ := by
  rw [Array.isEmpty_iff] at h
  subst h
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro e ⟨pe, hpe, _⟩
  simp at hpe

def certInOf (D : CheckDataIn) : WordCertIn ℕ where
  base := certOf D.toCheckData
  chainIn := fun v => (D.chainIn.getD v none).map (fun x => ((wordOf D.W' x.1).toList, x.2))
  bound := D.bound

theorem goutIn_mem (D : CheckDataIn) (idx : ℕ) (ge : PEdge) (h : D.gout[idx]? = some ge) :
    deref D.W' ge ∈ sem D.W' D.gout :=
  mem_sem _ _ _ (mem_of_getElem? _ _ _ h)

theorem contractInCheck_sound (W : WTable) (D : CheckDataIn) (k : ℕ) (pe : PEdge)
    (h : contractInCheck W D k pe = true) :
    (certInOf D).ContractInOK (sem D.W' D.gout) (deref W pe) := by
  unfold WordCertIn.ContractInOK
  simp only [certInOf, certOf, CheckDataIn.toCheckData, deref]
  unfold contractInCheck at h
  by_cases hmd : D.isMacro.getD pe.dst false = true
  · rw [if_pos hmd] at h
    rw [if_pos hmd]
    by_cases hms : D.isMacro.getD pe.src false = true
    · rw [if_pos hms] at h
      left
      refine ⟨hms, ?_⟩
      cases hidx : D.goutIdx.getD k none with
      | none => simp [hidx] at h
      | some idx =>
        simp only [hidx] at h
        cases hge : D.gout[idx]? with
        | none => simp [hge] at h
        | some ge =>
          simp only [hge, Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨hs, hd⟩, hw⟩ := h
          have := goutIn_mem D idx ge hge
          simp only [deref] at this
          rw [hs, hd, hw] at this
          exact this
    · rw [if_neg hms] at h
      right
      refine ⟨by simpa using hms, ?_⟩
      cases hct : D.chainIn.getD pe.src none with
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
            have := goutIn_mem D idx ge hge
            simp only [deref] at this
            rw [hs, hd, hw, Array.toList_append] at this
            exact this
  · rw [if_neg hmd] at h
    rw [if_neg hmd]
    cases hct : D.chainIn.getD pe.dst none with
    | none => simp [hct] at h
    | some x =>
      obtain ⟨wid', b⟩ := x
      simp only [hct, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hbound, h⟩ := h
      refine ⟨(wordOf D.W' wid').toList, b, by simp, by simpa using hbound, ?_⟩
      by_cases hms : D.isMacro.getD pe.src false = true
      · rw [if_pos hms] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        left
        exact ⟨hms, by rw [h.1], h.2⟩
      · rw [if_neg hms] at h
        right
        refine ⟨by simpa using hms, ?_⟩
        cases hct' : D.chainIn.getD pe.src none with
        | none => simp [hct'] at h
        | some y =>
          obtain ⟨wid'', b'⟩ := y
          simp only [hct', Bool.and_eq_true, decide_eq_true_eq] at h
          refine ⟨(wordOf D.W' wid'').toList, by simp [h.1], ?_⟩
          rw [h.2, Array.toList_append]

theorem edgeCheckIn_sound (W : WTable) (D : CheckDataIn) (k : ℕ) (pe : PEdge)
    (h : edgeCheckIn W D k pe = true) :
    (certInOf D).EdgeConditionIn (sem D.W' D.gout) (deref W pe) := by
  unfold WordCertIn.EdgeConditionIn
  unfold edgeCheckIn at h
  have hbase : (certInOf D).base = certOf D.toCheckData := rfl
  rw [hbase]
  simp only [certOf, CheckDataIn.toCheckData, deref]
  by_cases ho : D.owner.getD pe.src 0 = D.owner.getD pe.dst 0
  · rw [if_pos ho] at h
    rw [if_pos ho]
    by_cases hr : D.retained.getD (D.owner.getD pe.src 0) false = true
    · rw [if_pos hr] at h
      rw [if_pos hr]
      exact contractInCheck_sound W D k pe h
    · rw [if_neg hr] at h
      rw [if_neg hr]
      have := phaseCheck_sound W D.toCheckData pe h
      simpa [certOf, CheckDataIn.toCheckData, deref] using this
  · rw [if_neg ho] at h
    rw [if_neg ho]
    simpa using h

theorem checkStageIn_sound (S : CStage) (D : CheckDataIn) (h : checkStageIn S D = true) :
    ∀ e ∈ S.sem, (certInOf D).EdgeConditionIn (sem D.W' D.gout) e := by
  rintro e ⟨pe, hpe, rfl⟩
  obtain ⟨k, hk, hke⟩ := Array.mem_iff_getElem.mp hpe
  have hc := allIdx_spec h hk
  rw [getD_eq_getElem _ _ _ hk, hke] at hc
  exact edgeCheckIn_sound S.W D k pe hc

theorem compactStage_sem (n : ℕ) (W : WTable) (g : Array PEdge) :
    (sem W g).map (compactRename n g) ⊆ (compactStage n W g).sem := by
  rintro e ⟨e0, ⟨pe, hpe, rfl⟩, rfl⟩
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hpe
  refine ⟨⟨compactRename n g g[k].src, k, compactRename n g g[k].dst⟩, ?_, ?_⟩
  · unfold compactStage
    simp only [Array.mem_map, Array.mem_range]
    exact ⟨k, hk, by simp [getD_eq_getElem _ _ _ hk, compactRename]⟩
  · simp [deref, compactStage, wordOf, Array.getD_eq_getD_getElem?, hk]

theorem outPass_sound (S : CStage) (h : (outPass S).2.1 = true) {Gout : WGraph ℕ}
    (rest : StageReduce (outPass S).1.sem Gout) : StageReduce S.sem Gout :=
  StageReduce.out (certOf (runStageOut S)) (checkStage_sound S _ h)
    (StageReduce.rename _ (compactStage_sem _ _ _) rest)

theorem inPass_sound (S : CStage) (h : (inPass S).2.1 = true) {Gout : WGraph ℕ}
    (rest : StageReduce (inPass S).1.sem Gout) : StageReduce S.sem Gout :=
  StageReduce.inn (certInOf (runStageIn S)) (checkStageIn_sound S _ h)
    (StageReduce.rename _ (compactStage_sem _ _ _) rest)

theorem reduceLoop_sound : ∀ (fuel : ℕ) (S : CStage) (nv : ℕ),
    (reduceLoop fuel S nv).2 = true → StageReduce S.sem (reduceLoop fuel S nv).1.sem
  | 0, S, nv, _ => by simp only [reduceLoop]; exact StageReduce.done
  | fuel + 1, S, nv, h => by
    unfold reduceLoop at h ⊢
    by_cases he : S.edges.isEmpty = true
    · simp only [he, ↓reduceIte]
      exact StageReduce.done
    · simp only [he, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hok : ((inPass S).2.1 && (outPass (inPass S).1).2.1) = true
      · simp only [hok, ↓reduceIte] at h ⊢
        simp only [Bool.and_eq_true] at hok
        apply inPass_sound S hok.1
        apply outPass_sound _ hok.2
        by_cases hnv : (outPass (inPass S).1).2.2 = nv
        · simp only [hnv, ↓reduceIte]
          exact StageReduce.done
        · simp only [hnv, ↓reduceIte] at h ⊢
          exact reduceLoop_sound fuel _ _ h
      · simp only [hok, Bool.false_eq_true, ↓reduceIte] at h

theorem reduceStage_sound (rounds : ℕ) (S : CStage) (h : (reduceStage rounds S).2 = true) :
    StageReduce S.sem (reduceStage rounds S).1.sem := by
  unfold reduceStage at h ⊢
  by_cases hok : (outPass S).2.1 = true
  · simp only [hok, ↓reduceIte] at h ⊢
    exact outPass_sound S hok (reduceLoop_sound _ _ _ h)
  · simp only [hok, Bool.false_eq_true, ↓reduceIte] at h

theorem goB_sound (a b rounds : ℕ) :
    ∀ (ps : List ℕ) (S : CStage), goB a b rounds S ps = true → WordChainB a b S.sem ps
  | [], S, h => by
    simp only [goB, Bool.and_eq_true] at h
    exact WordChainB.nil _ (reduceStage_sound rounds S h.1) (sem_empty _ _ h.2)
  | p :: ps, S, h => by
    simp only [goB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hred, hp⟩, hinv⟩, hrest⟩ := h
    exact WordChainB.cons _ (findInv b p) (renameLift (denseIds _ (reduceStage rounds S).1.edges).1 p)
      _ (reduceStage_sound rounds S hred) hp hinv
      (liftArr_sound a p (findInv b p) _ _ _) (goB_sound a b rounds ps _ hrest)

theorem wordPipelineBidir_sound (a b K : ℕ) (alphabet : List ℤ) (primes : List ℕ)
    (h : wordPipelineBidir a b K alphabet primes = true) :
    WordFiniteSuccessB a b K alphabet primes :=
  ⟨(initialStage a b K alphabet).sem, initialStage_sound a b K alphabet, goB_sound a b 10 primes _ h⟩

end WordExec
