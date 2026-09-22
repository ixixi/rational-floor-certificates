import MathPaper.Word.Pipeline.Compute
import MathPaper.Word.Pipeline.LiftArr
import MathPaper.Word.Pipeline.Initial

/-! The executable pipeline `wordPipeline` and its soundness theorem. Every
stage: untrusted `runStage`, verified `checkStage`, verified `liftArr` with the
dense renaming; the last stage must have an empty output. -/
namespace MathPaper.Pipe

/-- Modular inverse of `b` modulo `p` by search (untrusted; re-checked). -/
def findInv (b p : ℕ) : ℕ := ((List.range p).find? fun x => (b * x) % p == 1).getD 0

def liftStage (D : CheckData) (a p binv : ℕ) : CStage :=
  ⟨D.nout * (p - 1), D.W', liftArr a p binv D.W' D.gout (renameLift D.newId p)⟩

def go (a b : ℕ) : CStage → List ℕ → Bool
  | S, [] =>
    let D := (runStage S).1
    checkStage S D && D.gout.isEmpty
  | S, p :: ps =>
    let D := (runStage S).1
    let binv := findInv b p
    checkStage S D && decide (1 < p) && decide (((b : ℤ) * binv) % (p : ℤ) = 1) &&
      go a b (liftStage D a p binv) ps

def wordPipeline (a b K : ℕ) (alphabet : List ℤ) (primes : List ℕ) : Bool :=
  go a b (initialStage a b K alphabet) primes

theorem sem_empty (W : WTable) (gout : Array PEdge) (h : gout.isEmpty = true) :
    sem W gout = ∅ := by
  rw [Array.isEmpty_iff] at h
  subst h
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro e ⟨pe, hpe, _⟩
  simp at hpe

theorem go_sound (a b : ℕ) :
    ∀ (ps : List ℕ) (S : CStage), go a b S ps = true → WordChain a b S.sem ps
  | [], S, h => by
    simp only [go, Bool.and_eq_true] at h
    exact WordChain.nil (certOf (runStage S).1) _ (checkStage_sound S _ h.1) (sem_empty _ _ h.2)
  | p :: ps, S, h => by
    simp only [go, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hcheck, hp⟩, hinv⟩, hrest⟩ := h
    exact WordChain.cons (certOf (runStage S).1) _ (findInv b p)
      (renameLift (runStage S).1.newId p) _ (checkStage_sound S _ hcheck) hp hinv
      (liftArr_sound a p (findInv b p) _ _ _) (go_sound a b ps _ hrest)

/-- Soundness of the executable pipeline (kernel-checked). -/
theorem wordPipeline_sound (a b K : ℕ) (alphabet : List ℤ) (primes : List ℕ)
    (h : wordPipeline a b K alphabet primes = true) :
    WordFiniteSuccess a b K alphabet primes :=
  ⟨(initialStage a b K alphabet).sem, initialStage_sound a b K alphabet, go_sound a b primes _ h⟩

/-- Diagnostics only (not used by any proof): per-stage statistics and check results. -/
def runStats (a b : ℕ) : CStage → List ℕ → List (StageStats × Bool × ℕ)
  | S, [] =>
    let (D, st) := runStage S
    [(st, checkStage S D && D.gout.isEmpty, S.n)]
  | S, p :: ps =>
    let (D, st) := runStage S
    let binv := findInv b p
    let ok := checkStage S D && decide (1 < p) && decide (((b : ℤ) * binv) % (p : ℤ) = 1)
    (st, ok, S.n) :: runStats a b (liftStage D a p binv) ps

def wordPipelineStats (a b K : ℕ) (alphabet : List ℤ) (primes : List ℕ) :
    List (StageStats × Bool × ℕ) :=
  runStats a b (initialStage a b K alphabet) primes

end MathPaper.Pipe
