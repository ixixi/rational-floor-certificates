import MathPaper.Graph

namespace MathPaper

/-- A rank certificate does not need to assert that blocks are SCCs. -/
structure RankCertificate (V : Type*) where
  owner : V → ℕ
  rank : ℕ → ℕ
  retained : ℕ → Bool
  period : ℕ → ℕ
  phase : V → ℕ
  label : ℕ → ℕ → ℤ

def RankCertificate.EdgeCondition {V : Type*} (C : RankCertificate V)
    (u v : V) (e : ℤ) : Prop :=
  if C.owner u = C.owner v then
    C.retained (C.owner u) = true ∨
      (0 < C.period (C.owner u) ∧ C.phase u < C.period (C.owner u) ∧
        C.phase v = (C.phase u + 1) % C.period (C.owner u) ∧
        e = C.label (C.owner u) (C.phase u))
  else C.rank (C.owner v) < C.rank (C.owner u)

theorem rank_eventually_constant {V : Type*} (C : RankCertificate V) (v : ℕ → V)
    (hstep : ∀ n, C.owner (v n) ≠ C.owner (v (n + 1)) →
      C.rank (C.owner (v (n + 1))) < C.rank (C.owner (v n))) :
    ∃ N, ∀ n, N ≤ n → C.owner (v n) = C.owner (v N) := by
  classical
  let r := fun n => C.rank (C.owner (v n))
  have hex : ∃ k, ∃ n, r n = k := ⟨r 0, 0, rfl⟩
  obtain ⟨N, hN⟩ := Nat.find_spec hex
  have hmin : ∀ n, Nat.find hex ≤ r n := fun n => Nat.find_min' hex ⟨n, rfl⟩
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction k with
  | zero => simp
  | succ k ih =>
    have heq : C.owner (v (N + k)) = C.owner (v (N + k + 1)) := by
      by_contra hne
      have hlt := hstep (N + k) hne
      rw [ih] at hlt
      have hge := hmin (N + k + 1)
      change r N = Nat.find hex at hN
      change r (N + k + 1) < r N at hlt
      omega
    simpa only [Nat.add_assoc] using heq.symm.trans ih

theorem phase_labels_periodic (d : ℕ) (phase : ℕ → ℕ) (label : ℕ → ℤ)
    (c : ℕ → ℤ) (hphase : ∀ n, phase (n + 1) = (phase n + 1) % d)
    (hbound : phase 0 < d) (hlabel : ∀ n, c n = label (phase n)) :
    ∀ n, c (n + d) = c n := by
  have hp : ∀ n, phase n = (phase 0 + n) % d := by
    intro n
    induction n with
    | zero => simp [Nat.mod_eq_of_lt hbound]
    | succ n ih =>
      rw [hphase, ih]
      rw [Nat.mod_add_mod, Nat.add_assoc]
  intro n
  rw [hlabel, hlabel, hp (n + d), hp n]
  congr 1
  simp [← Nat.add_assoc]

/-- Every infinite walk with nonperiodic labels eventually stays in retained blocks.
An unretained block of period zero has no allowable internal edge. -/
theorem rank_certificate_retained_tail {V : Type*} (C : RankCertificate V)
    (v : ℕ → V) (c : ℕ → ℤ)
    (hedge : ∀ n, C.EdgeCondition (v n) (v (n + 1)) (c n))
    (hnonper : ¬ EventuallyPeriodic c) :
    ∃ N, ∀ n, N ≤ n → C.retained (C.owner (v n)) = true := by
  have hrank : ∀ n, C.owner (v n) ≠ C.owner (v (n + 1)) →
      C.rank (C.owner (v (n + 1))) < C.rank (C.owner (v n)) := by
    intro n hne
    simpa [RankCertificate.EdgeCondition, hne] using hedge n
  obtain ⟨N, hN⟩ := rank_eventually_constant C v hrank
  by_cases hret : C.retained (C.owner (v N)) = true
  · exact ⟨N, fun n hn => by rw [hN n hn]; exact hret⟩
  have hlocal : ∀ k,
      0 < C.period (C.owner (v N)) ∧
      C.phase (v (N + k)) < C.period (C.owner (v N)) ∧
      C.phase (v (N + (k + 1))) =
        (C.phase (v (N + k)) + 1) % C.period (C.owner (v N)) ∧
      c (N + k) = C.label (C.owner (v N)) (C.phase (v (N + k))) := by
    intro k
    have h := hedge (N + k)
    have hu := hN (N + k) (by omega)
    have hv := hN (N + k + 1) (by omega)
    simp [RankCertificate.EdgeCondition, hu, hv, hret] at h
    simpa only [Nat.add_assoc] using h
  have hp := phase_labels_periodic (C.period (C.owner (v N)))
    (fun k => C.phase (v (N + k))) (C.label (C.owner (v N)))
    (fun k => c (N + k)) (fun k => (hlocal k).2.2.1)
    (by simpa using (hlocal 0).2.1) (fun k => (hlocal k).2.2.2)
  apply False.elim
  apply hnonper
  refine ⟨N, C.period (C.owner (v N)), (hlocal 0).1, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa only [Nat.add_assoc] using hp k

end MathPaper
