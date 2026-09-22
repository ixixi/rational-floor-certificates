import MathPaper.Success
import MathPaper.Enumeration

namespace MathPaper.Finite

structure Datum where
  owner : Nat
  phase : Nat
  deriving DecidableEq

inductive Tree where
  | nil
  | node (key : Int) (value : Datum) (left right : Tree)

namespace Tree

def get : Tree → Int → Option Datum
  | .nil, _ => none
  | .node k d l r, x => if x < k then l.get x else if x = k then some d else r.get x

def all (p : Int → Datum → Bool) : Tree → Bool
  | .nil => true
  | .node k d l r => p k d && l.all p && r.all p

theorem get_all {p : Int → Datum → Bool} {T : Tree} (h : T.all p = true)
    {x : Int} {d : Datum} (hx : T.get x = some d) : p x d = true := by
  induction T with
  | nil => simp [get] at hx
  | node k v l r il ir =>
    simp only [all, Bool.and_eq_true] at h
    simp only [get] at hx
    split at hx
    · exact il h.1.2 hx
    · split at hx
      next he => cases he; cases hx; exact h.1.1
      next => exact ir h.2 hx
end Tree

def allBelow : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => allBelow n p && p n

theorem allBelow_spec {n : Nat} {p : Nat → Bool} (h : allBelow n p = true)
    {i : Nat} (hi : i < n) : p i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true] at h
    by_cases he : i = n
    · simpa [he] using h.2
    · exact ih h.1 (by omega)

def key (K : Nat) (u : State) : Int := u.1 * K + u.2
def decode (K : Nat) (k : Int) : State := (k / K, k % K)

def Bounds (K : Nat) (u : State) : Prop :=
  0 ≤ u.1 ∧ u.1 < 4290 ∧ 0 ≤ u.2 ∧ u.2 < K
instance (K : Nat) (u : State) : Decidable (Bounds K u) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem decode_key (K : Nat) (u : State) (h : Bounds K u) : decode K (key K u) = u := by
  obtain ⟨hq0, hq1, hj0, hj1⟩ := h
  have hK : (0 : Int) < K := by omega
  unfold decode key
  apply Prod.ext
  · dsimp
    rw [Int.add_comm, Int.add_mul_ediv_right _ _ (ne_of_gt hK), Int.ediv_eq_zero_of_lt hj0 hj1]
    simp
  · dsimp
    simp [Int.add_emod, Int.emod_eq_of_lt hj0 hj1]

def ownerRetained (o : Nat) : Bool := o % 2 == 1
def ownerPeriod (o : Nat) : Nat := (o / 2) % 16
def ownerLabel (o p : Nat) : Int := ((o / 32 / 16 ^ p) % 16 : Nat) - (4 : Int)
def datum (T : Tree) (K : Nat) (u : State) : Datum := (T.get (key K u)).getD ⟨0, 0⟩
def certificate (T : Tree) (K : Nat) : RankCertificate State where
  owner := fun u => (datum T K u).owner
  rank := id
  retained := ownerRetained
  period := ownerPeriod
  phase := fun u => (datum T K u).phase
  label := ownerLabel

def states (T : Tree) (K : Nat) : Set State :=
  {u | Bounds K u ∧ ∃ d, T.get (key K u) = some d}
def retained (T : Tree) (K : Nat) : Set State :=
  {u | u ∈ states T K ∧ ownerRetained (datum T K u).owner = true}

def condition (d v : Datum) (e : Int) : Bool :=
  if d.owner = v.owner then
    ownerRetained d.owner || decide (0 < ownerPeriod d.owner ∧
      d.phase < ownerPeriod d.owner ∧ v.phase = (d.phase + 1) % ownerPeriod d.owner ∧
      e = ownerLabel d.owner d.phase)
  else decide (v.owner < d.owner)

theorem condition_sound (T : Tree) (K : Nat) (u v : State) (d dv : Datum) (e : Int)
    (hu : T.get (key K u) = some d) (hv : T.get (key K v) = some dv)
    (hc : condition d dv e = true) : (certificate T K).EdgeCondition u v e := by
  simpa [condition, certificate, datum, hu, hv, RankCertificate.EdgeCondition,
    Bool.or_eq_true] using hc

def candidateE (q : Int) (i : Nat) : Int := -4 + (4 - 7 * q) % 5 + 5 * i

def candidateV (K : Nat) (u : State) (e : Int) (z j : Nat) : State :=
  (((7 * u.1 + e) / 5) % 858 + 858 * z, (7 * u.2 - e * K) / 5 + j)

instance (K : Nat) (u v : State) (e : Int) : Decidable (Edge 7 5 4290 K u v e) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def checkCandidate (T : Tree) (K : Nat) (u : State) (d : Datum)
    (e : Int) (v : State) : Bool :=
  if Bounds K v ∧ Edge 7 5 4290 K u v e then
    match T.get (key K v) with
    | none => true
    | some dv => condition d dv e
  else true

instance (K : Nat) (u : State) : Decidable (LegalState 4290 K u) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def checkSource (T : Tree) (K : Nat) (k : Int) (d : Datum) : Bool :=
  let u := decode K k
  decide (LegalState 4290 K u) &&
  allBelow 3 (fun i => let e := candidateE u.1 i
    allBelow 5 (fun z => allBelow 3 (fun j => checkCandidate T K u d e (candidateV K u e z j))))

theorem checked_stage (T : Tree) (K : Nat) (h : T.all (checkSource T K) = true) :
    StageValid 7 5 4290 K (states T K) (retained T K) (certificate T K) := by
  constructor
  · intro u hu v hv e he
    obtain ⟨hub, d, hd⟩ := hu
    obtain ⟨hvb, dv, hdv⟩ := hv
    have hs := Tree.get_all h hd
    unfold checkSource at hs
    rw [decode_key K u hub] at hs
    simp only [Bool.and_eq_true] at hs
    have hs' := hs.2
    obtain ⟨i, hi, hei⟩ := main_carry_candidate u.1 v.1 e he.1 he.2.1 he.2.2.1
    obtain ⟨z, hz, hvz⟩ := main_congruence_candidate u.1 v.1 e hvb.1 hvb.2.1 he.2.2.1
    obtain ⟨j, hj, hvj⟩ := main_cell_candidate u.2 v.2 e K he.2.2.2.1 he.2.2.2.2
    have heq : e = candidateE u.1 i := hei
    have hvq : v = candidateV K u e z j := Prod.ext hvz hvj
    have hh := allBelow_spec (allBelow_spec (allBelow_spec hs' hi) hz) hj
    rw [← heq, ← hvq] at hh
    simp only [checkCandidate, if_pos (show Bounds K v ∧ Edge 7 5 4290 K u v e from ⟨hvb, he⟩), hdv] at hh
    exact condition_sound T K u v d dv e hd hdv hh
  · intro u hu hr
    exact ⟨hu, hr⟩

theorem checked_states_legal (T : Tree) (K : Nat)
    (h : T.all (checkSource T K) = true) :
    ∀ u ∈ states T K, LegalState 4290 K u := by
  rintro u ⟨hb, d, hd⟩
  have hs := Tree.get_all h hd
  unfold checkSource at hs
  rw [decode_key K u hb] at hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
  exact hs.1

theorem Tree.all_node_true (p : Int → Datum → Bool) (k : Int) (d : Datum) (l r : Tree)
    (hk : p k d = true) (hl : l.all p = true) (hr : r.all p = true) :
    (Tree.node k d l r).all p = true := by
  simp only [Tree.all, hk, hl, hr, Bool.and_self]

def present (T : Tree) (K : Nat) (u : State) : Bool :=
  decide (Bounds K u) && (T.get (key K u)).isSome

theorem present_spec (T : Tree) (K : Nat) (u : State) :
    present T K u = true ↔ u ∈ states T K := by
  simp [present, states, Option.isSome_iff_exists]

def checkInitial (T : Tree) : Bool :=
  allBelow 4290 fun q => if Nat.gcd q 4290 = 1 then
    allBelow 32 fun j => present T 32 (q, j) else true

theorem initial_sound (T : Tree) (h : checkInitial T = true) :
    ∀ u, LegalState 4290 32 u → u ∈ states T 32 := by
  rintro ⟨q, j⟩ ⟨hq0, hq, hg, hj0, hj⟩
  have heq : (q.toNat : Int) = q := Int.toNat_of_nonneg hq0
  have hej : (j.toNat : Int) = j := Int.toNat_of_nonneg hj0
  have hq' : q.toNat < 4290 := by omega
  have hj' : j.toNat < 32 := by omega
  have hg' : Nat.gcd q.toNat 4290 = 1 := by
    rw [← heq] at hg
    exact hg
  have hh := allBelow_spec h hq'
  simp only [if_pos hg'] at hh
  have hhh := allBelow_spec hh hj'
  rw [heq, hej] at hhh
  exact (present_spec T 32 (q, j)).mp hhh

def checkRefine (Tnext : Tree) (K : Nat) (k : Int) (d : Datum) : Bool :=
  if ownerRetained d.owner then
    let u := decode K k
    allBelow 4 fun i => present Tnext (4 * K) (u.1, 4 * u.2 + i)
  else true

theorem refine_sound (T Tnext : Tree) (K : Nat)
    (h : T.all (checkRefine Tnext K) = true) :
    Refine 4 (retained T K) ⊆ states Tnext (4 * K) := by
  rintro v ⟨u, ⟨⟨hub, d, hd⟩, hr⟩, i, hi0, hi, rfl⟩
  have hs := Tree.get_all h hd
  have hr' : ownerRetained d.owner = true := by simpa [datum, hd] using hr
  simp only [checkRefine, hr', ↓reduceIte, decode_key K u hub] at hs
  have hi' : i.toNat < 4 := by omega
  have hh := allBelow_spec hs hi'
  have hei : (i.toNat : Int) = i := Int.toNat_of_nonneg hi0
  rw [hei] at hh
  exact (present_spec Tnext (4 * K) _).mp hh

def checkEmpty (T : Tree) : Bool := T.all fun _ d => !ownerRetained d.owner

theorem empty_sound (T : Tree) (K : Nat) (h : checkEmpty T = true) :
    retained T K = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro u ⟨⟨_, d, hd⟩, hr⟩
  have hh := Tree.get_all h hd
  have hr' : ownerRetained d.owner = true := by simpa [datum, hd] using hr
  simp [hr'] at hh

end MathPaper.Finite
