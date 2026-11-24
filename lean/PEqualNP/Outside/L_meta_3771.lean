import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3771

def inD (z : Fin 13) : Bool :=
  z == 0 || z == 1 || z == 3 || z == 9

def compatMask : ℕ → ℕ
  | 0 => 7668
  | 1 => 3834
  | 2 => 1917
  | 3 => 5054
  | 4 => 2527
  | 5 => 5359
  | 6 => 6775
  | 7 => 7483
  | 8 => 7837
  | 9 => 8014
  | 10 => 4007
  | 11 => 6099
  | 12 => 7145
  | _ => 0

def pop13 : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, m => (if m % 2 = 1 then 1 else 0) + pop13 k (m / 2)

lemma compatMask_spec_bool :
    (List.finRange 13).all (fun a =>
      (List.finRange 13).all (fun y =>
        ((compatMask a.val).testBit y.val) == !(inD (a + y)))) = true := by
  decide

lemma compatMask_testBit (a y : Fin 13) :
    (compatMask a.val).testBit y.val = !(inD (a + y)) := by
  have ha := List.all_eq_true.mp compatMask_spec_bool a (List.mem_finRange a)
  have hy := List.all_eq_true.mp ha y (List.mem_finRange y)
  exact beq_iff_eq.mp hy

lemma bound_quad_bool :
    (List.range 13).all (fun a =>
      (List.range 13).all (fun b =>
        !(decide (a < b)) || (List.range 13).all (fun c =>
          !(decide (b < c)) || (List.range 13).all (fun d =>
            !(decide (c < d)) || decide (pop13 13 (compatMask a &&& compatMask b &&& compatMask c &&& compatMask d) ≤ 3))))) = true := by
  decide +kernel

lemma pop13_le_three {a b c d : ℕ} (ha : a < 13) (hb : b < 13) (hc : c < 13) (hd : d < 13)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    pop13 13 (compatMask a &&& compatMask b &&& compatMask c &&& compatMask d) ≤ 3 := by
  have h1 := List.all_eq_true.mp bound_quad_bool a (List.mem_range.mpr ha)
  have h2 := List.all_eq_true.mp h1 b (List.mem_range.mpr hb)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h2
  have h3 := List.all_eq_true.mp (h2.resolve_left (not_not.mpr hab)) c (List.mem_range.mpr hc)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h3
  have h4 := List.all_eq_true.mp (h3.resolve_left (not_not.mpr hbc)) d (List.mem_range.mpr hd)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at h4
  exact h4.resolve_left (not_not.mpr hcd)

lemma range_succ_eq_insert_image (k : ℕ) :
    Finset.range (k + 1) = insert 0 ((Finset.range k).image Nat.succ) := by
  ext x
  cases x with
  | zero => simp
  | succ x => simp

lemma pop13_eq_card (k m : ℕ) :
    pop13 k m = ((Finset.range k).filter (fun i => m.testBit i = true)).card := by
  induction k generalizing m with
  | zero => simp [pop13]
  | succ k ih =>
    rw [pop13, ih (m / 2), range_succ_eq_insert_image, Finset.filter_insert]
    have h0 : 0 ∉ ((Finset.range k).image Nat.succ).filter (fun i => m.testBit i = true) := by
      simp
    have himg : ((Finset.range k).image Nat.succ).filter (fun i => m.testBit i = true) =
        ((Finset.range k).filter (fun i => (m / 2).testBit i = true)).image Nat.succ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, hb⟩
        exact ⟨a, ⟨ha, by simpa [Nat.testBit_succ] using hb⟩, rfl⟩
      · rintro ⟨a, ⟨ha, hb⟩, rfl⟩
        exact ⟨⟨a, ha, rfl⟩, by simpa [Nat.testBit_succ] using hb⟩
    have hcard : (((Finset.range k).image Nat.succ).filter (fun i => m.testBit i = true)).card =
        ((Finset.range k).filter (fun i => (m / 2).testBit i = true)).card := by
      rw [himg, Finset.card_image_of_injective _ Nat.succ_injective]
    have htb0 : m.testBit 0 = true ↔ m % 2 = 1 := by
      simp [Nat.testBit_zero]
    by_cases hm : m % 2 = 1
    · have htb : m.testBit 0 = true := htb0.mpr hm
      rw [ite_eq_left hm, ite_eq_left htb, Finset.card_insert_of_notMem h0, hcard]
      omega
    · have htb : ¬ (m.testBit 0 = true) := fun h => hm (htb0.mp h)
      rw [ite_eq_right hm, ite_eq_right htb, hcard]
      omega

lemma fin_filter_card_eq_pop13 (m : ℕ) :
    (Finset.univ.filter (fun y : Fin 13 => m.testBit y.val = true)).card = pop13 13 m := by
  rw [pop13_eq_card]
  refine Finset.card_bij (fun y _ => y.val) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr y.isLt, hy⟩
  · intro y1 _ y2 _ h
    exact Fin.ext h
  · intro i hi
    obtain ⟨hir, him⟩ := Finset.mem_filter.mp hi
    exact ⟨⟨i, Finset.mem_range.mp hir⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, him⟩, rfl⟩

lemma inD_eq_false_of_not_mem (z : Fin 13)
    (hz : z ∉ ({(0 : Fin 13), (1 : Fin 13), (3 : Fin 13), (9 : Fin 13)} : Finset (Fin 13))) :
    inD z = false := by
  fin_cases z <;> simp_all [inD]

theorem main_proof :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
    ∀ (x2 x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∈ x2, ∀ x6 ∈ x3, x4 + x6 ∉ x1) → x2.card ≤ (3 : ℕ) ∨ x3.card ≤ (3 : ℕ) := by
  intro x1 x2 x3 h
  by_contra hnot
  have h2 : 4 ≤ x2.card := by omega
  have h3 : 4 ≤ x3.card := by omega
  obtain ⟨s, hs_sub, hs_card⟩ := Finset.exists_subset_card_eq h2
  let f := s.orderEmbOfFin hs_card
  let a := f 0
  let b := f 1
  let c := f 2
  let d := f 3
  have ha : a ∈ x2 := hs_sub (s.orderEmbOfFin_mem hs_card 0)
  have hb : b ∈ x2 := hs_sub (s.orderEmbOfFin_mem hs_card 1)
  have hc : c ∈ x2 := hs_sub (s.orderEmbOfFin_mem hs_card 2)
  have hd : d ∈ x2 := hs_sub (s.orderEmbOfFin_mem hs_card 3)
  have hab : a.val < b.val := f.strictMono (by decide)
  have hbc : b.val < c.val := f.strictMono (by decide)
  have hcd : c.val < d.val := f.strictMono (by decide)
  let m : ℕ := compatMask a.val &&& compatMask b.val &&& compatMask c.val &&& compatMask d.val
  have hsub : x3 ⊆ Finset.univ.filter (fun y : Fin 13 => m.testBit y.val = true) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, m, Nat.testBit_and, Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [compatMask_testBit, inD_eq_false_of_not_mem (a + y) (h a ha y hy)]; rfl
    · rw [compatMask_testBit, inD_eq_false_of_not_mem (b + y) (h b hb y hy)]; rfl
    · rw [compatMask_testBit, inD_eq_false_of_not_mem (c + y) (h c hc y hy)]; rfl
    · rw [compatMask_testBit, inD_eq_false_of_not_mem (d + y) (h d hd y hy)]; rfl
  have hcard : x3.card ≤ pop13 13 m := by
    calc x3.card ≤ (Finset.univ.filter (fun y : Fin 13 => m.testBit y.val = true)).card :=
          Finset.card_le_card hsub
      _ = pop13 13 m := fin_filter_card_eq_pop13 m
  have hle3 : pop13 13 m ≤ 3 :=
    pop13_le_three a.isLt b.isLt c.isLt d.isLt hab hbc hcd
  omega

end PEqualNP.Outside.L_meta_3771

theorem PEqualNP.Outside.L_meta_3771 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∈ x2, ∀ x6 ∈ x3, x4 + x6 ∉ x1) → x2.card ≤ (3 : ℕ) ∨ x3.card ≤ (3 : ℕ) :=
  PEqualNP.Outside.L_meta_3771.main_proof
