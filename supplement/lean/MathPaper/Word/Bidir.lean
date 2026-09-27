import MathPaper.Word.Chain
import MathPaper.Word.InContract

/-! The word-labelled finite success theorem with several checked passes per
stage (5/3 addition). Inside one stage, any finite sequence of out-direction
passes (removal and out-degree-one contraction, `WordCert`) and in-direction
passes (removal and in-degree-one contraction, `WordCertIn`) preserves a tail
of every non-eventually-periodic covering. `WordChainB` replaces the single
certificate per stage of `WordChain` by such a sequence; the original
`WordChain` and its theorems are unchanged. -/
namespace MathPaper

/-- A checked finite sequence of passes from `G` to `Gout`. -/
inductive StageReduce : WGraph ℕ → WGraph ℕ → Prop
  | done {G : WGraph ℕ} : StageReduce G G
  | out {G Gmid Gout : WGraph ℕ} (C : WordCert ℕ)
      (hcheck : ∀ e ∈ G, C.EdgeCondition Gmid e) (rest : StageReduce Gmid Gout) :
      StageReduce G Gout
  | inn {G Gmid Gout : WGraph ℕ} (C : WordCertIn ℕ)
      (hcheck : ∀ e ∈ G, C.EdgeConditionIn Gmid e) (rest : StageReduce Gmid Gout) :
      StageReduce G Gout
  | sub {G G' Gout : WGraph ℕ} (h : G ⊆ G') (rest : StageReduce G' Gout) : StageReduce G Gout
  | rename {G G' Gout : WGraph ℕ} (ρ : ℕ → ℕ) (h : G.map ρ ⊆ G') (rest : StageReduce G' Gout) :
      StageReduce G Gout

theorem StageReduce.tail {G Gout : WGraph ℕ} (h : StageReduce G Gout) (c : ℕ → ℤ)
    (hnonper : ¬ EventuallyPeriodic c) :
    ∀ n₀, Covers G c n₀ → ∃ n₁, n₀ ≤ n₁ ∧ Covers Gout c n₁ := by
  induction h with
  | done => exact fun n₀ hc => ⟨n₀, le_rfl, hc⟩
  | out C hcheck _ ih =>
    intro n₀ hc
    obtain ⟨n₁, hn₁, hc₁⟩ := C.stage_tail _ _ hcheck c hnonper n₀ hc
    obtain ⟨n₂, hn₂, hc₂⟩ := ih n₁ hc₁
    exact ⟨n₂, le_trans hn₁ hn₂, hc₂⟩
  | inn C hcheck _ ih =>
    intro n₀ hc
    obtain ⟨n₁, hn₁, hc₁⟩ := C.stage_tail _ _ hcheck c hnonper n₀ hc
    obtain ⟨n₂, hn₂, hc₂⟩ := ih n₁ hc₁
    exact ⟨n₂, le_trans hn₁ hn₂, hc₂⟩
  | sub h _ ih => exact fun n₀ hc => ih n₀ (Covers.mono h hc)
  | rename ρ h _ ih => exact fun n₀ hc => ih n₀ (Covers.mono h (hc.map ρ))

inductive WordChainB (a b : ℕ) : WGraph ℕ → List ℕ → Prop
  | nil {G : WGraph ℕ} (Gout : WGraph ℕ) (hred : StageReduce G Gout) (hempty : Gout = ∅) :
      WordChainB a b G []
  | cons {G : WGraph ℕ} {p : ℕ} {ps : List ℕ} (Gout : WGraph ℕ)
      (binv : ℕ) (ρ : ℕ × ℕ → ℕ) (G' : WGraph ℕ)
      (hred : StageReduce G Gout) (hp : 1 < p)
      (hinv : ((b : ℤ) * binv) % p = 1)
      (hlift : (Lift a p binv Gout).map ρ ⊆ G') (rest : WordChainB a b G' ps) :
      WordChainB a b G (p :: ps)

theorem wordChainB_no_covering (a b : ℕ) (Q c : ℕ → ℤ)
    (hrec : ∀ n, (b : ℤ) * Q (n + 1) = a * Q n + c n)
    (hnonper : ¬ EventuallyPeriodic c) {G : WGraph ℕ} {ps : List ℕ}
    (h : WordChainB a b G ps) :
    ∀ n₀, (∀ p ∈ ps, 1 < p → ∀ n, n₀ ≤ n → ¬ ((p : ℤ) ∣ Q n)) → Covers G c n₀ → False := by
  induction h with
  | nil Gout hred hempty =>
    intro n₀ _ hcov
    obtain ⟨n₁, _, hc⟩ := hred.tail c hnonper n₀ hcov
    rw [hempty] at hc
    exact Covers.not_empty hc
  | cons Gout binv ρ G' hred hp hinv hlift _ ih =>
    intro n₀ havoid hcov
    obtain ⟨n₁, hn₁, hc⟩ := hred.tail c hnonper n₀ hcov
    have hl := lift_tail a b _ binv Q c hp hinv hrec Gout n₁ hc
      (fun n hn => havoid _ (List.mem_cons_self) hp n (le_trans hn₁ hn))
    exact ih n₁ (fun p hp' hp1 n hn => havoid p (List.mem_cons_of_mem _ hp') hp1 n
      (le_trans hn₁ hn)) (Covers.mono hlift (hl.map ρ))

/-- The finite success structure with several checked passes per stage. -/
def WordFiniteSuccessB (a b K : ℕ) (alphabet : List ℤ) (primes : List ℕ) : Prop :=
  ∃ G : WGraph ℕ, InitialGraph a b K alphabet ⊆ G ∧ WordChainB a b G primes

theorem word_finite_success_visits_B (a b K M : ℕ) (alphabet : List ℤ) (primes : List ℕ)
    (hab : b < a) (hb : 2 ≤ b) (hcop : Nat.Coprime a b) (hK : 0 < K) (hM : 0 < M)
    (hdvd : ∀ p ∈ primes, p ∣ M)
    (halpha : ∀ ξ : ℝ, 0 < ξ → ∀ n, Int.gcd (floorOrbit a b ξ n) M = 1 →
      Int.gcd (floorOrbit a b ξ (n + 1)) M = 1 → carry a b ξ n ∈ alphabet)
    (S : WordFiniteSuccessB a b K alphabet primes) (ξ : ℝ) (hξ : 0 < ξ) (N : ℕ) :
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
  refine wordChainB_no_covering a b (floorOrbit a b ξ) (carry a b ξ) (carry_recurrence a b ξ)
    hnonper hchain (max N 1) ?_ hcov
  intro p hp hp1 n hn hpQ
  have hpM : (p : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.mpr (hdvd p hp)
  have h1 : p ∣ Int.gcd (floorOrbit a b ξ n) M := Int.dvd_gcd hpQ hpM
  rw [hgcd n hn] at h1
  have := Nat.le_of_dvd Nat.one_pos h1
  omega

theorem word_finite_success_composite_B (a b K M : ℕ) (alphabet : List ℤ) (primes : List ℕ)
    (hab : b < a) (hb : 2 ≤ b) (hcop : Nat.Coprime a b) (hK : 0 < K) (hM : 0 < M)
    (hdvd : ∀ p ∈ primes, p ∣ M)
    (halpha : ∀ ξ : ℝ, 0 < ξ → ∀ n, Int.gcd (floorOrbit a b ξ n) M = 1 →
      Int.gcd (floorOrbit a b ξ (n + 1)) M = 1 → carry a b ξ n ∈ alphabet)
    (S : WordFiniteSuccessB a b K alphabet primes) (ξ : ℝ) (hξ : 0 < ξ) (N : ℕ) :
    ∃ n, max N 1 ≤ n ∧ Composite (floorOrbit a b ξ n) := by
  obtain ⟨J, hJ⟩ := floor_orbit_eventually_gt a b hab (by omega) ξ hξ M
  obtain ⟨n, hn, hg⟩ := word_finite_success_visits_B a b K M alphabet primes hab hb hcop hK hM
    hdvd halpha S ξ hξ (max N J)
  exact ⟨n, by omega, composite_of_gcd_gt_one _ M hM (hJ n (by omega)) hg⟩

end MathPaper
