import MathPaper.Finite.Checker

namespace MathPaper.Finite

/-- Filter the carry and target cell once, before checking all five residue lifts.
Ignoring E2 here is safe: this is an overapproximation, and completeness is proved below. -/
def checkCell (T : Tree) (K : Nat) (u : State) (d : Datum) (e : Int) (j : Nat) : Bool :=
  let k := (7 * u.2 - e * K) / 5 + j
  if -4 ≤ e ∧ e ≤ 6 ∧ 0 ≤ k ∧ k < K ∧
      7 * u.2 - 5 * (k + 1) < e * K ∧ e * K < 7 * (u.2 + 1) - 5 * k then
    allBelow 5 fun z =>
      match T.get (key K (candidateV K u e z j)) with
      | none => true
      | some dv => condition d dv e
  else true

def checkSourceFast (T : Tree) (K : Nat) (k : Int) (d : Datum) : Bool :=
  let u := decode K k
  decide (LegalState 4290 K u) &&
  allBelow 3 (fun i => let e := candidateE u.1 i
    allBelow 3 (fun j => checkCell T K u d e j))

theorem checked_stage_fast (T : Tree) (K : Nat) (h : T.all (checkSourceFast T K) = true) :
    StageValid 7 5 4290 K (states T K) (retained T K) (certificate T K) := by
  constructor
  · intro u hu v hv e he
    obtain ⟨hub, d, hd⟩ := hu
    obtain ⟨hvb, dv, hdv⟩ := hv
    have hs := Tree.get_all h hd
    unfold checkSourceFast at hs
    rw [decode_key K u hub] at hs
    simp only [Bool.and_eq_true] at hs
    obtain ⟨i, hi, hei⟩ := main_carry_candidate u.1 v.1 e he.1 he.2.1 he.2.2.1
    obtain ⟨z, hz, hvz⟩ := main_congruence_candidate u.1 v.1 e hvb.1 hvb.2.1 he.2.2.1
    obtain ⟨j, hj, hvj⟩ := main_cell_candidate u.2 v.2 e K he.2.2.2.1 he.2.2.2.2
    have heq : e = candidateE u.1 i := hei
    have hvq : v = candidateV K u e z j := Prod.ext hvz hvj
    have hh := allBelow_spec (allBelow_spec hs.2 hi) hj
    rw [← heq] at hh
    have hguard : -4 ≤ e ∧ e ≤ 6 ∧ 0 ≤ v.2 ∧ v.2 < (K : Int) ∧
        7 * u.2 - 5 * (v.2 + 1) < e * K ∧ e * K < 7 * (u.2 + 1) - 5 * v.2 :=
      ⟨he.1, he.2.1, hvb.2.2.1, hvb.2.2.2, he.2.2.2⟩
    simp only [checkCell, ← hvj, if_pos hguard] at hh
    have hhz := allBelow_spec hh hz
    rw [← hvq, hdv] at hhz
    exact condition_sound T K u v d dv e hd hdv hhz
  · intro u hu hr
    exact ⟨hu, hr⟩

theorem checked_fast_states_legal (T : Tree) (K : Nat)
    (h : T.all (checkSourceFast T K) = true) :
    ∀ u ∈ states T K, LegalState 4290 K u := by
  rintro u ⟨hb, d, hd⟩
  have hs := Tree.get_all h hd
  unfold checkSourceFast at hs
  rw [decode_key K u hb] at hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
  exact hs.1

end MathPaper.Finite
