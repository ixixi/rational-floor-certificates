import MathPaper.Certificate

namespace MathPaper

theorem gcd_emod (q m : ℤ) : Int.gcd (q % m) m = Int.gcd q m := by
  apply Nat.dvd_antisymm
  · apply Int.dvd_gcd
    · have h1 := Int.gcd_dvd_left (q % m) m
      have h2 := (Int.gcd_dvd_right (q % m) m).trans (Int.dvd_emod_sub_self (x := q))
      have h := dvd_sub h1 h2
      simpa using h
    · exact Int.gcd_dvd_right (q % m) m
  · apply Int.dvd_gcd
    · have h1 := Int.gcd_dvd_left q m
      have h2 := (Int.gcd_dvd_right q m).trans (Int.dvd_emod_sub_self (x := q))
      have h := dvd_add h2 h1
      simpa using h
    · exact Int.gcd_dvd_right q m

theorem orbit_state_legal (a b M K : ℕ) (hM : 0 < M) (hK : 0 < K)
    (ξ : ℝ) (n : ℕ) (hgcd : Int.gcd (floorOrbit a b ξ n) M = 1) :
    LegalState M K (orbitState a b M K ξ n) := by
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have ht0 := fractionOrbit_nonneg a b ξ n
  have ht1 := fractionOrbit_lt_one a b ξ n
  refine ⟨Int.emod_nonneg _ (ne_of_gt hM'), Int.emod_lt_of_pos _ hM', ?_, ?_, ?_⟩
  · exact (gcd_emod _ _).trans hgcd
  · apply Int.floor_nonneg.mpr
    exact mul_nonneg hK'.le ht0
  · apply Int.floor_lt.mpr
    exact_mod_cast (show (K : ℝ) * fractionOrbit a b ξ n < K by nlinarith)

theorem not_eventuallyPeriodic_shift (c : ℕ → ℤ) (h : ¬ EventuallyPeriodic c) (N : ℕ) :
    ¬ EventuallyPeriodic (fun k => c (N + k)) := by
  rintro ⟨M, L, hL, hper⟩
  apply h
  refine ⟨N + M, L, hL, ?_⟩
  intro n hn
  have hnk : N ≤ n := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnk
  have hk : M ≤ k := by omega
  simpa only [Nat.add_assoc] using hper k hk

def StageValid (a b M K : ℕ) (W U : Set State) (C : RankCertificate State) : Prop :=
  (∀ u ∈ W, ∀ v ∈ W, ∀ e, Edge a b M K u v e → C.EdgeCondition u v e) ∧
  (∀ u ∈ W, C.retained (C.owner u) = true → u ∈ U)

theorem certified_orbit_retained_tail (a b M K : ℕ) (ha : 0 < a) (hb : 0 < b)
    (ξ : ℝ) (hnonper : ¬ EventuallyPeriodic (carry a b ξ))
    (W U : Set State) (C : RankCertificate State) (hC : StageValid a b M K W U C)
    (N : ℕ) (hW : ∀ n, N ≤ n → orbitState a b M K ξ n ∈ W) :
    ∃ N', N ≤ N' ∧ ∀ n, N' ≤ n → orbitState a b M K ξ n ∈ U := by
  obtain ⟨N', hN'⟩ := rank_certificate_retained_tail C
    (fun k => orbitState a b M K ξ (N + k)) (fun k => carry a b ξ (N + k))
    (by
      intro k
      apply hC.1 _ (hW _ (by omega)) _ (hW _ (by omega))
      simpa only [Nat.add_assoc] using orbit_edge a b M K ha hb ξ (N + k))
    (not_eventuallyPeriodic_shift _ hnonper N)
  refine ⟨N + N', by omega, ?_⟩
  intro n hn
  apply hC.2 _ (hW _ (by omega))
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show N ≤ n by omega)
  exact hN' k (by omega)

/-- A finite successful chain is a sufficient condition, not a claim of general termination. -/
structure FiniteSuccess (a b M : ℕ) where
  last : ℕ
  factor : ℕ
  factor_pos : 0 < factor
  cells : ℕ → ℕ
  cells_pos : ∀ t, 0 < cells t
  cells_step : ∀ t, cells (t + 1) = factor * cells t
  states : ℕ → Set State
  retained : ℕ → Set State
  cert : ℕ → RankCertificate State
  initial : ∀ u, LegalState M (cells 0) u → u ∈ states 0
  valid : ∀ t, t ≤ last → StageValid a b M (cells t) (states t) (retained t) (cert t)
  refine_sub : ∀ t, t < last → Refine factor (retained t) ⊆ states (t + 1)
  final_empty : retained last = ∅

theorem finite_success_visits (a b M : ℕ) (hab : b < a) (hb : 2 ≤ b)
    (hcop : Nat.Coprime a b) (hM : 0 < M) (S : FiniteSuccess a b M)
    (ξ : ℝ) (hξ : 0 < ξ) (N : ℕ) :
    ∃ n, max N 1 ≤ n ∧ 1 < Int.gcd (floorOrbit a b ξ n) M := by
  by_contra hnot
  push Not at hnot
  have hgcd : ∀ n, max N 1 ≤ n → Int.gcd (floorOrbit a b ξ n) M = 1 := by
    intro n hn
    have hlo := Int.gcd_pos_of_ne_zero_right (floorOrbit a b ξ n)
      (show (M : ℤ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hM)
    have hhi := hnot n hn
    omega
  have hnonper := floor_carry_not_eventually_periodic a b hab hb hcop ξ hξ
  have htail : ∀ t, t ≤ S.last → ∃ J, ∀ n, J ≤ n →
      orbitState a b M (S.cells t) ξ n ∈ S.states t := by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨max N 1, fun n hn => S.initial _
        (orbit_state_legal a b M (S.cells 0) hM (S.cells_pos 0) ξ n (hgcd n hn))⟩
    | succ t ih =>
      intro ht
      obtain ⟨J, hJ⟩ := ih (by omega)
      obtain ⟨J', _, hJ'⟩ := certified_orbit_retained_tail a b M (S.cells t)
        (by omega) (by omega) ξ hnonper _ _ _ (S.valid t (by omega)) J hJ
      refine ⟨J', fun n hn => ?_⟩
      rw [S.cells_step]
      exact S.refine_sub t (by omega) (refined_state_mem a b M (S.cells t)
        S.factor S.factor_pos ξ n _ (hJ' n hn))
  obtain ⟨J, hJ⟩ := htail S.last le_rfl
  obtain ⟨J', _, hJ'⟩ := certified_orbit_retained_tail a b M (S.cells S.last)
    (by omega) (by omega) ξ hnonper _ _ _ (S.valid S.last le_rfl) J hJ
  have hbad := hJ' J' le_rfl
  rw [S.final_empty] at hbad
  exact hbad

def Composite (q : ℤ) : Prop := ∃ u v : ℤ, 1 < u ∧ 1 < v ∧ q = u * v

theorem composite_of_gcd_gt_one (q : ℤ) (M : ℕ) (hM : 0 < M)
    (hq : (M : ℤ) < q) (hg : 1 < Int.gcd q M) : Composite q := by
  let d : ℤ := Int.gcd q M
  have hd : 1 < d := by dsimp [d]; exact_mod_cast hg
  have hdM : d ≤ M := Int.gcd_le_right q (by exact_mod_cast hM)
  obtain ⟨v, hv⟩ := Int.gcd_dvd_left q M
  refine ⟨d, v, hd, ?_, hv⟩
  change q = d * v at hv
  nlinarith

theorem finite_success_composite (a b M : ℕ) (hab : b < a) (hb : 2 ≤ b)
    (hcop : Nat.Coprime a b) (hM : 0 < M) (S : FiniteSuccess a b M)
    (ξ : ℝ) (hξ : 0 < ξ) (N : ℕ) :
    ∃ n, max N 1 ≤ n ∧ Composite (floorOrbit a b ξ n) := by
  obtain ⟨J, hJ⟩ := floor_orbit_eventually_gt a b hab (by omega) ξ hξ M
  obtain ⟨n, hn, hg⟩ := finite_success_visits a b M hab hb hcop hM S ξ hξ (max N J)
  exact ⟨n, by omega, composite_of_gcd_gt_one _ M hM (hJ n (by omega)) hg⟩

end MathPaper
