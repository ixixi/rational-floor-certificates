import MathPaper.Word.Cert
import MathPaper.Word.Lift
import MathPaper.Success

/-! The word-labelled finite success theorem (audit-02 §6, W5). A `WordChain`
records one checked stage per auxiliary prime, the lift into the next stage and
the empty final output. No SCC identification, no finiteness of the graphs and
no injectivity of vertex renamings is assumed. -/
namespace MathPaper

inductive WordChain (a b : ℕ) : WGraph ℕ → List ℕ → Prop
  | nil {G : WGraph ℕ} (C : WordCert ℕ) (Gout : WGraph ℕ)
      (hcheck : ∀ e ∈ G, C.EdgeCondition Gout e) (hempty : Gout = ∅) :
      WordChain a b G []
  | cons {G : WGraph ℕ} {p : ℕ} {ps : List ℕ} (C : WordCert ℕ) (Gout : WGraph ℕ)
      (binv : ℕ) (ρ : ℕ × ℕ → ℕ) (G' : WGraph ℕ)
      (hcheck : ∀ e ∈ G, C.EdgeCondition Gout e) (hp : 1 < p)
      (hinv : ((b : ℤ) * binv) % p = 1)
      (hlift : (Lift a p binv Gout).map ρ ⊆ G') (rest : WordChain a b G' ps) :
      WordChain a b G (p :: ps)

/-- Finite induction over the stages (audit-02 命題 W5 の証明の帰納部分). -/
theorem wordChain_no_covering (a b : ℕ) (Q c : ℕ → ℤ)
    (hrec : ∀ n, (b : ℤ) * Q (n + 1) = a * Q n + c n)
    (hnonper : ¬ EventuallyPeriodic c) {G : WGraph ℕ} {ps : List ℕ}
    (h : WordChain a b G ps) :
    ∀ n₀, (∀ p ∈ ps, 1 < p → ∀ n, n₀ ≤ n → ¬ ((p : ℤ) ∣ Q n)) → Covers G c n₀ → False := by
  induction h with
  | nil C Gout hcheck hempty =>
    intro n₀ _ hcov
    obtain ⟨n₁, _, hc⟩ := C.stage_tail _ Gout hcheck c hnonper n₀ hcov
    rw [hempty] at hc
    exact Covers.not_empty hc
  | cons C Gout binv ρ G' hcheck hp hinv hlift _ ih =>
    intro n₀ havoid hcov
    obtain ⟨n₁, hn₁, hc⟩ := C.stage_tail _ Gout hcheck c hnonper n₀ hcov
    have hl := lift_tail a b _ binv Q c hp hinv hrec Gout n₁ hc
      (fun n hn => havoid _ (List.mem_cons_self) hp n (le_trans hn₁ hn))
    exact ih n₁ (fun p hp' hp1 n hn => havoid p (List.mem_cons_of_mem _ hp') hp1 n
      (le_trans hn₁ hn)) (Covers.mono hlift (hl.map ρ))

/-- Initial cell graph `G₀ⁱⁿ`: cells `0 ≤ j < K`, one-letter words, strict (E3). -/
def InitialGraph (a b K : ℕ) (alphabet : List ℤ) : WGraph ℕ :=
  {e | ∃ j k : ℕ, ∃ c ∈ alphabet, j < K ∧ k < K ∧
    (a : ℤ) * j - b * ((k : ℤ) + 1) < c * K ∧ c * K < a * ((j : ℤ) + 1) - b * k ∧
    e = ⟨j, [c], k⟩}

/-- The true orbit covers the initial graph as soon as its carries lie in the
alphabet (audit-02 §6, first step; `orbit_edge` with `M = 1`). -/
theorem initial_covering (a b K : ℕ) (ha : 0 < a) (hb : 0 < b) (hK : 0 < K)
    (alphabet : List ℤ) (ξ : ℝ) (n₀ : ℕ)
    (halpha : ∀ n, n₀ ≤ n → carry a b ξ n ∈ alphabet) :
    Covers (InitialGraph a b K alphabet) (carry a b ξ) n₀ := by
  have hlegal : ∀ n, LegalState 1 K (orbitState a b 1 K ξ n) := fun n =>
    orbit_state_legal a b 1 K (by omega) hK ξ n (by simp)
  have hcell : ∀ n, (((orbitState a b 1 K ξ n).2.toNat : ℕ) : ℤ) = (orbitState a b 1 K ξ n).2 :=
    fun n => Int.toNat_of_nonneg (hlegal n).2.2.2.1
  refine ⟨⟨fun i => (orbitState a b 1 K ξ (n₀ + i)).2.toNat, fun i => [carry a b ξ (n₀ + i)],
    fun i => n₀ + i, by simp, ?_, fun i => by simp, fun i => by simp; omega, ?_⟩⟩
  · intro i
    have he := orbit_edge a b 1 K ha hb ξ (n₀ + i)
    have hl := hlegal (n₀ + i)
    have hl' := hlegal (n₀ + i + 1)
    refine ⟨(orbitState a b 1 K ξ (n₀ + i)).2.toNat, (orbitState a b 1 K ξ (n₀ + i + 1)).2.toNat,
      carry a b ξ (n₀ + i), halpha _ (by omega), ?_, ?_, ?_, ?_, ?_⟩
    · have := hl.2.2.2.2
      have h0 := hl.2.2.2.1
      omega
    · have := hl'.2.2.2.2
      have h0 := hl'.2.2.2.1
      omega
    · rw [hcell, hcell]
      exact he.2.2.2.1
    · rw [hcell, hcell]
      exact he.2.2.2.2
    · rfl
  · intro i k hk
    simp at hk
    subst hk
    simp

/-- The finite success structure: an initial graph containing all strict-(E3)
cell edges and a checked chain of stages ending in the empty graph. -/
def WordFiniteSuccess (a b K : ℕ) (alphabet : List ℤ) (primes : List ℕ) : Prop :=
  ∃ G : WGraph ℕ, InitialGraph a b K alphabet ⊆ G ∧ WordChain a b G primes

/-- Word-labelled finite success theorem (audit-02 命題 W5, (VISIT-W)). The
hypothesis `halpha` is (H𝒞): coprimality of consecutive terms with `M` forces
the carry into the alphabet. Each auxiliary prime must divide `M`. -/
theorem word_finite_success_visits (a b K M : ℕ) (alphabet : List ℤ) (primes : List ℕ)
    (hab : b < a) (hb : 2 ≤ b) (hcop : Nat.Coprime a b) (hK : 0 < K) (hM : 0 < M)
    (hdvd : ∀ p ∈ primes, p ∣ M)
    (halpha : ∀ ξ : ℝ, 0 < ξ → ∀ n, Int.gcd (floorOrbit a b ξ n) M = 1 →
      Int.gcd (floorOrbit a b ξ (n + 1)) M = 1 → carry a b ξ n ∈ alphabet)
    (S : WordFiniteSuccess a b K alphabet primes) (ξ : ℝ) (hξ : 0 < ξ) (N : ℕ) :
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
  obtain ⟨G, hsub, hchain⟩ := S
  have hcov : Covers G (carry a b ξ) (max N 1) :=
    Covers.mono hsub (initial_covering a b K (by omega) (by omega) hK alphabet ξ (max N 1)
      (fun n hn => halpha ξ hξ n (hgcd n hn) (hgcd (n + 1) (by omega))))
  refine wordChain_no_covering a b (floorOrbit a b ξ) (carry a b ξ) (carry_recurrence a b ξ)
    hnonper hchain (max N 1) ?_ hcov
  intro p hp hp1 n hn hpQ
  have hpM : (p : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.mpr (hdvd p hp)
  have h1 : p ∣ Int.gcd (floorOrbit a b ξ n) M := Int.dvd_gcd hpQ hpM
  rw [hgcd n hn] at h1
  have := Nat.le_of_dvd Nat.one_pos h1
  omega

theorem word_finite_success_composite (a b K M : ℕ) (alphabet : List ℤ) (primes : List ℕ)
    (hab : b < a) (hb : 2 ≤ b) (hcop : Nat.Coprime a b) (hK : 0 < K) (hM : 0 < M)
    (hdvd : ∀ p ∈ primes, p ∣ M)
    (halpha : ∀ ξ : ℝ, 0 < ξ → ∀ n, Int.gcd (floorOrbit a b ξ n) M = 1 →
      Int.gcd (floorOrbit a b ξ (n + 1)) M = 1 → carry a b ξ n ∈ alphabet)
    (S : WordFiniteSuccess a b K alphabet primes) (ξ : ℝ) (hξ : 0 < ξ) (N : ℕ) :
    ∃ n, max N 1 ≤ n ∧ Composite (floorOrbit a b ξ n) := by
  obtain ⟨J, hJ⟩ := floor_orbit_eventually_gt a b hab (by omega) ξ hξ M
  obtain ⟨n, hn, hg⟩ := word_finite_success_visits a b K M alphabet primes hab hb hcop hK hM
    hdvd halpha S ξ hξ (max N J)
  exact ⟨n, by omega, composite_of_gcd_gt_one _ M hM (hJ n (by omega)) hg⟩

end MathPaper
