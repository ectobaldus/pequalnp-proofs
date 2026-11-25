import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Choose

namespace G11FixedFactors

def negativeRows : List Nat :=
  [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]

def inputOn (r i : Nat) : Bool :=
  if i = 11 then r.testBit 1 && (r.testBit 8 || r.testBit 10)
  else if i = 12 then (r.testBit 2 || r.testBit 9) && (r.testBit 0 || r.testBit 5)
  else r.testBit i

def edgeRow (e : Fin 5) : Nat := ([1025,18,36,72,640] : List Nat)[e.val]!

def active (e : Fin 5) : List Nat := (List.range 13).filter (inputOn (edgeRow e))

def compatible (i j : Nat) : Bool :=
  !(negativeRows.any fun r => inputOn r i && inputOn r j)

def clean (a b : Nat → Prop) : Prop :=
  ∀ i ∈ List.range 13, a i → ∀ j ∈ List.range 13, b j → compatible i j = true

def fires (a b : Nat → Prop) (e : Fin 5) : Prop :=
  (∃ i ∈ active e, a i) ∧ (∃ j ∈ active e, b j)

private theorem checked : ∀ e f : Fin 5, e ≠ f →
    (active e).all (fun i => (active f).all (fun j =>
      (active e).all (fun k => (active f).all (fun l =>
        !(compatible i k && compatible i l && compatible j k && compatible j l))))) = true := by
  decide +kernel

theorem separates {a b : Nat → Prop} {e f : Fin 5} (hc : clean a b)
    (he : fires a b e) (hf : fires a b f) : e = f := by
  by_contra hne
  obtain ⟨⟨i, hi, ai⟩, ⟨k, hk, bk⟩⟩ := he
  obtain ⟨⟨j, hj, aj⟩, ⟨l, hl, bl⟩⟩ := hf
  have table := checked e f hne
  simp only [List.all_eq_true] at table
  have forbidden := table i hi j hj k hk l hl
  have vi := (List.mem_filter.mp hi).1
  have vj := (List.mem_filter.mp hj).1
  have vk := (List.mem_filter.mp hk).1
  have vl := (List.mem_filter.mp hl).1
  simp [hc i vi ai k vk bk, hc i vi ai l vl bl, hc j vj aj k vk bk, hc j vj aj l vl bl] at forbidden

theorem atLeastFive {T : Type*} [Fintype T] (a b : T → Nat → Prop)
    (sound : ∀ t, clean (a t) (b t))
    (cover : ∀ e : Fin 5, ∃ t, fires (a t) (b t) e) : 5 ≤ Fintype.card T := by
  classical
  choose pick hp using cover
  have inj : Function.Injective pick := by
    intro x y eq
    apply separates (sound (pick x)) (hp x)
    simpa only [eq] using hp y
  simpa using Fintype.card_le_of_injective pick inj

def graph (r : Nat) : Bool :=
  ([513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768] : List Nat).any
    (fun edge => (r &&& edge) == edge)

def termOn (a b : Nat → Prop) (r : Nat) : Prop :=
  (∃ i ∈ (List.range 13).filter (inputOn r), a i) ∧
  (∃ j ∈ (List.range 13).filter (inputOn r), b j)

private theorem negChecked : negativeRows.all (fun r => decide (r < 2048) && !graph r) = true := by
  decide +kernel

private theorem posChecked : ∀ e : Fin 5, edgeRow e < 2048 ∧ graph (edgeRow e) = true := by
  decide +kernel

theorem exactGraphNeedsFive {T : Type*} [Fintype T] (a b : T → Nat → Prop)
    (correct : ∀ r : Fin 2048, graph r = true ↔ ∃ t, termOn (a t) (b t) r) :
    5 ≤ Fintype.card T := by
  apply atLeastFive a b
  · intro t i vi ai j vj bj
    by_contra h
    have bad : negativeRows.any (fun r => inputOn r i && inputOn r j) = true := by
      simpa [compatible] using h
    obtain ⟨r, hr, hij⟩ := List.any_eq_true.mp bad
    have valid : r < 2048 ∧ graph r = false := by simpa using (List.all_eq_true.mp negChecked r hr)
    have both : inputOn r i = true ∧ inputOn r j = true := by simpa using hij
    have pos := (correct ⟨r,valid.1⟩).mpr ⟨t, ⟨i, List.mem_filter.mpr ⟨vi,both.1⟩, ai⟩,
      ⟨j,List.mem_filter.mpr ⟨vj,both.2⟩,bj⟩⟩
    change graph r = true at pos
    simp [valid.2] at pos
  · intro e
    exact (correct ⟨edgeRow e,(posChecked e).1⟩).mp (posChecked e).2

def witnessMasks (t : Fin 5) : Nat × Nat :=
  ([(1024,5),(4352,2592),(128,584),(64,1032),(16,1282)] : List (Nat × Nat))[t.val]!

def selected (m : Nat) (i : Nat) : Prop := m.testBit i = true

def bitTerm (r a b : Nat) : Bool :=
  let inputs := (List.range 13).filter (inputOn r)
  inputs.any (fun i => a.testBit i) && inputs.any (fun i => b.testBit i)

private theorem reflects (r a b : Nat) : bitTerm r a b = true ↔ termOn (selected a) (selected b) r := by
  simp [bitTerm, termOn, selected, List.any_eq_true, and_assoc]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1500000 in
private theorem coverTable : ∀ r : Fin 2048, graph r = true ↔
    ∃ t : Fin 5, bitTerm r (witnessMasks t).1 (witnessMasks t).2 = true := by
  decide +kernel

theorem fiveTermsSuffice : ∃ a b : Fin 5 → Nat → Prop,
    ∀ r : Fin 2048, graph r = true ↔ ∃ t, termOn (a t) (b t) r := by
  refine ⟨fun t => selected (witnessMasks t).1, fun t => selected (witnessMasks t).2, ?_⟩
  intro r
  simpa only [← reflects] using coverTable r

end G11FixedFactors
