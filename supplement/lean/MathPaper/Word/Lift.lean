import MathPaper.Word.Graph

/-! Lifting a word graph by an auxiliary prime (audit-02 §5, W4). Only the
forward iteration `q ↦ binv (a q + c) mod p` is used; the root formula is not
needed for soundness. The parameter `binv` is any inverse of `b` modulo `p`. -/
namespace MathPaper

def stepRes (a p binv : ℕ) (q : ℕ) (c : ℤ) : ℕ :=
  (((binv : ℤ) * ((a : ℤ) * (q : ℤ) + c)) % (p : ℤ)).toNat

/-- Iterate along a word; fail as soon as a residue vanishes. -/
def runWord (a p binv : ℕ) : List ℤ → ℕ → Option ℕ
  | [], q => some q
  | c :: w, q =>
    let q' := stepRes a p binv q c
    if q' = 0 then none else runWord a p binv w q'

def liftEdge {V : Type*} (a p binv : ℕ) (e : WEdge V) (q : ℕ) : Option (WEdge (V × ℕ)) :=
  if q = 0 then none else
  match runWord a p binv e.word q with
  | none => none
  | some q' => some ⟨(e.src, q), e.word, (e.dst, q')⟩

/-- All start residues `1 ≤ q < p`; intermediate and final residues nonzero. -/
def Lift {V : Type*} (a p binv : ℕ) (G : WGraph V) : WGraph (V × ℕ) :=
  {e' | ∃ e ∈ G, ∃ q, q < p ∧ liftEdge a p binv e q = some e'}

theorem liftEdge_some {V : Type*} (a p binv : ℕ) (e : WEdge V) (q q' : ℕ) (hq : q ≠ 0)
    (hrun : runWord a p binv e.word q = some q') :
    liftEdge a p binv e q = some ⟨(e.src, q), e.word, (e.dst, q')⟩ := by
  simp [liftEdge, hq, hrun]

section Orbit

variable (a b p binv : ℕ) (Q c : ℕ → ℤ)

theorem step_orbit (hp : 0 < p) (hinv : ((b : ℤ) * binv) % p = 1)
    (hrec : ∀ n, (b : ℤ) * Q (n + 1) = a * Q n + c n) (n : ℕ) :
    stepRes a p binv (Q n % p).toNat (c n) = (Q (n + 1) % p).toNat := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hx : (((Q n % p).toNat : ℕ) : ℤ) = Q n % p :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hp'))
  unfold stepRes
  rw [hx]
  congr 1
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  apply Int.emod_eq_zero_of_dvd
  have h1 := Int.mul_ediv_add_emod (Q n) p
  have h2 := Int.mul_ediv_add_emod ((b : ℤ) * binv) p
  rw [hinv] at h2
  have h3 := hrec n
  refine ⟨((b : ℤ) * binv / p) * Q (n + 1) - (binv : ℤ) * a * (Q n / p), ?_⟩
  linear_combination (binv : ℤ) * a * h1 - Q (n + 1) * h2 - (binv : ℤ) * h3

theorem runWord_orbit (hp : 0 < p) (hinv : ((b : ℤ) * binv) % p = 1)
    (hrec : ∀ n, (b : ℤ) * Q (n + 1) = a * Q n + c n) :
    ∀ (w : List ℤ) (n : ℕ), (∀ k, k < w.length → w.getD k 0 = c (n + k)) →
      (∀ k, k ≤ w.length → ¬ ((p : ℤ) ∣ Q (n + k))) →
      runWord a p binv w (Q n % p).toNat = some (Q (n + w.length) % p).toNat := by
  intro w
  induction w with
  | nil => intro n _ _; simp [runWord]
  | cons c₀ w ih =>
    intro n hw havoid
    have hc₀ : c₀ = c n := by
      have := hw 0 (by simp)
      simpa using this
    have hstep := step_orbit a b p binv Q c hp hinv hrec n
    rw [hc₀] at *
    have hne : (Q (n + 1) % p).toNat ≠ 0 := by
      intro h0
      have hp' : (0 : ℤ) < p := by exact_mod_cast hp
      have hnn := Int.emod_nonneg (Q (n + 1)) (ne_of_gt hp')
      have hz : Q (n + 1) % p = 0 := by
        have := Int.toNat_eq_zero.mp h0
        omega
      exact havoid 1 (by simp) (Int.dvd_of_emod_eq_zero hz)
    simp only [runWord, hstep, hne, ↓reduceIte]
    rw [ih (n + 1) (fun k hk => by
        have := hw (k + 1) (by simpa using Nat.succ_lt_succ hk)
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using this)
      (fun k hk => by
        have := havoid (k + 1) (by simpa using Nat.succ_le_succ hk)
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using this)]
    simp only [List.length_cons]
    rw [show n + 1 + w.length = n + (w.length + 1) by omega]

/-- Tail preservation under lifting (audit-02 命題 W4-a). The lifted covering
starts at the same time; avoidance of `p` is needed from that time on. -/
theorem lift_tail {V : Type*} (hp : 1 < p) (hinv : ((b : ℤ) * binv) % p = 1)
    (hrec : ∀ n, (b : ℤ) * Q (n + 1) = a * Q n + c n) (G : WGraph V) (n₀ : ℕ)
    (hcov : Covers G c n₀) (havoid : ∀ n, n₀ ≤ n → ¬ ((p : ℤ) ∣ Q n)) :
    Covers (Lift a p binv G) c n₀ := by
  obtain ⟨Cov⟩ := hcov
  have hp0 : 0 < p := by omega
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp0
  let q : ℕ → ℕ := fun i => (Q (Cov.t i) % p).toNat
  have hq0 : ∀ i, q i ≠ 0 := by
    intro i h0
    have hnn := Int.emod_nonneg (Q (Cov.t i)) (ne_of_gt hp')
    have hz : Q (Cov.t i) % p = 0 := by
      have := Int.toNat_eq_zero.mp h0
      omega
    exact havoid (Cov.t i) (by have := Cov.le_t i; omega) (Int.dvd_of_emod_eq_zero hz)
  have hqp : ∀ i, q i < p := by
    intro i
    have hnn := Int.emod_nonneg (Q (Cov.t i)) (ne_of_gt hp')
    have hlt := Int.emod_lt_of_pos (Q (Cov.t i)) hp'
    exact (Int.toNat_lt hnn).mpr hlt
  have hrun : ∀ i, runWord a p binv (Cov.w i) (q i) = some (q (i + 1)) := by
    intro i
    show runWord a p binv (Cov.w i) (Q (Cov.t i) % p).toNat = some (Q (Cov.t (i + 1)) % p).toNat
    rw [Cov.t_succ i]
    exact runWord_orbit a b p binv Q c hp0 hinv hrec (Cov.w i) (Cov.t i) (Cov.output i)
      (fun k _ => havoid _ (by have := Cov.le_t i; omega))
  exact ⟨⟨fun i => (Cov.v i, q i), Cov.w, Cov.t, Cov.t_zero,
    fun i => ⟨⟨Cov.v i, Cov.w i, Cov.v (i + 1)⟩, Cov.edge i, q i, hqp i,
      liftEdge_some a p binv _ _ _ (hq0 i) (hrun i)⟩,
    Cov.nonempty, Cov.t_succ, Cov.output⟩⟩

end Orbit

end MathPaper
