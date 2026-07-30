import Mathlib.Data.Option.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Sets.OpenCover
import Cheenta_Proofs.BasicLemmasforCD
import Cheenta_Proofs.Covering_Dimension


/-
Copyright (c) 2026 Cheenta Lean Project. All rights reserved.
Authors : Adhiraj Anand, Niranjan Rao, Parum Sarda, Shravas Matta, Shreesh Nayak, Shreya Iyer
-/

open Set

universe u
variable {X : Type u} [TopologicalSpace X]
-- Assuming your definition:
-- def Covering_Dimension_Strict (n : ℕ) : Prop :=
--  ∀ (m : ℕ) (u : {i : ℕ // i < m} → TopologicalSpace.Opens X),
--    TopologicalSpace.IsOpenCover u → (∀ i, (u i : Set X) ≠ ∅) → Function.Injective u →
--    ∃ (m' : ℕ) (v : {j : ℕ // j < m'} → TopologicalSpace.Opens X), ...

theorem subspaceOfDimension
  {Y : Set X} (hY : IsClosed Y) {n : ℕ} (hdim : Covering_Dimension_Strict (X := X) n) :
  Covering_Dimension_Strict (X := ↥Y) n := by
  intro m u hu_cov hu_ne hu_inj
  choose U hU_open hU_eq using fun i => isOpen_induced_iff.mp (u i).isOpen

  let U_ext : {i : ℕ // i < m + 1} → TopologicalSpace.Opens X := fun ⟨i, hi⟩ =>
    if h : i < m then ⟨U ⟨i, h⟩, hU_open ⟨i, h⟩⟩
    else ⟨Yᶜ, isOpen_compl_iff.mpr hY⟩

  have h_cov : TopologicalSpace.IsOpenCover U_ext := by
    ext x
    simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hx : x ∈ Y

    · have hS : (⋃ i, (u i : Set ↥Y)) = Set.univ := by rw [← TopologicalSpace.Opens.coe_iSup, hu_cov, TopologicalSpace.Opens.coe_top]
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hS.symm ▸ Set.mem_univ (⟨x, hx⟩ : Y))
      use ⟨i.val, Nat.lt_succ_of_lt i.property⟩
      dsimp only [U_ext]
      rw [dif_pos i.property]
      exact (Set.ext_iff.mp (hU_eq i) ⟨x, hx⟩).mpr hi
    · use ⟨m, Nat.lt_succ_self m⟩
      dsimp only [U_ext]
      rw [dif_neg (lt_irrefl m)]
      exact hx

  by_cases hm : m = 0
  · have hYa : IsEmpty ↥Y := ⟨fun y => by
      have hS : (⋃ i, (u i : Set ↥Y)) = Set.univ := by rw [← TopologicalSpace.Opens.coe_iSup, hu_cov, TopologicalSpace.Opens.coe_top]
      obtain ⟨i, _⟩ := Set.mem_iUnion.mp (hS.symm ▸ Set.mem_univ y)
      have h_impossible : i.val < 0 := hm ▸ i.property
      exact False.elim (Nat.not_lt_zero i.val h_impossible)⟩

    refine ⟨0, fun j => False.elim (Nat.not_lt_zero j.val j.property), ?_, ?_, ?_⟩
    · ext y; exact (hYa.false y).elim
    · intro i
      have h_impossible : i.val < 0 := hm ▸ i.property
      exact False.elim (Nat.not_lt_zero i.val h_impossible)
    · intro f hf
      have h_impossible : (f 0).val < 0 := (f 0).property
      exact False.elim (Nat.not_lt_zero (f 0).val h_impossible)
  by_cases hYc : Yᶜ = ∅
  · let U' : {i : ℕ // i < m} → TopologicalSpace.Opens X := fun i => ⟨U i, hU_open i⟩
    have hU'_cov : TopologicalSpace.IsOpenCover U' := by
      ext x
      simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion, Set.mem_univ, iff_true]
      have hx : x ∈ Y := by_contra fun h => (hYc ▸ h : x ∈ ∅)
      have hS : (⋃ i, (u i : Set ↥Y)) = Set.univ := by rw [← TopologicalSpace.Opens.coe_iSup, hu_cov, TopologicalSpace.Opens.coe_top]
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hS.symm ▸ Set.mem_univ (⟨x, hx⟩ : Y))
      exact ⟨i, (Set.ext_iff.mp (hU_eq i) ⟨x, hx⟩).mpr hi⟩

    have hU'_ne : ∀ i, (U' i : Set X) ≠ ∅ := by
      intro i he
      apply hu_ne i
      ext ⟨x, hx⟩
      exact (Set.ext_iff.mp (hU_eq i) ⟨x, hx⟩).symm.trans (Set.ext_iff.mp he x)

    have hU'_inj : Function.Injective U' := by
      intro i j heq
      apply hu_inj
      ext ⟨x, hx⟩
      have h1 : x ∈ U i ↔ ⟨x, hx⟩ ∈ (u i : Set Y) := Set.ext_iff.mp (hU_eq i) ⟨x, hx⟩
      have h2 : x ∈ U j ↔ ⟨x, hx⟩ ∈ (u j : Set Y) := Set.ext_iff.mp (hU_eq j) ⟨x, hx⟩
      have h3 : x ∈ U i ↔ x ∈ U j := Set.ext_iff.mp (congr_arg Subtype.val heq) x
      exact h1.symm.trans (h3.trans h2)

    obtain ⟨m', V, hV_cov, hV_ref, hV_ord⟩ := hdim m U' hU'_cov hU'_ne hU'_inj

    let v : {j : ℕ // j < m'} → TopologicalSpace.Opens ↥Y := fun j =>
      ⟨(↑) ⁻¹' (V j : Set X), (V j).isOpen.preimage continuous_subtype_val⟩

    refine ⟨m', v, ?_, ?_, ?_⟩
    · ext ⟨x, hx⟩
      simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion, Set.mem_univ, iff_true]
      have hV : (⋃ j, (V j : Set X)) = Set.univ := by rw [← TopologicalSpace.Opens.coe_iSup, hV_cov, TopologicalSpace.Opens.coe_top]
      exact Set.mem_iUnion.mp (hV.symm ▸ Set.mem_univ x)
    · intro j
      obtain ⟨i, hi⟩ := hV_ref j
      exact ⟨i, fun ⟨x, hx⟩ hVj => (Set.ext_iff.mp (hU_eq i) ⟨x, hx⟩).mp (hi hVj)⟩
    · intro f hf
      have h_ord := hV_ord f hf
      ext ⟨x, hx⟩
      simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
      intro h_in
      have h_empty : x ∈ (∅ : Set X) := by
        rw [← h_ord]
        simp only [Set.mem_iInter]
        exact h_in
      exact h_empty

  · have hU_ext_ne : ∀ i, (U_ext i : Set X) ≠ ∅ := by
      intro ⟨i, hi⟩
      dsimp only [U_ext]
      split_ifs with h
      · intro he
        apply hu_ne ⟨i, h⟩
        ext ⟨x, hx⟩
        exact (Set.ext_iff.mp (hU_eq ⟨i, h⟩) ⟨x, hx⟩).symm.trans (Set.ext_iff.mp he x)
      · exact hYc

    have hU_ext_inj : Function.Injective U_ext := by
      intro ⟨i, hi⟩ ⟨j, hj⟩ heq
      have heq_set : (U_ext ⟨i, hi⟩ : Set X) = (U_ext ⟨j, hj⟩ : Set X) := congr_arg Subtype.val heq
      dsimp only [U_ext] at heq_set
      split_ifs at heq_set with hi_lt hj_lt
      · have H : u ⟨i, hi_lt⟩ = u ⟨j, hj_lt⟩ := by
          ext ⟨x, hx⟩
          have h1 : x ∈ U ⟨i, hi_lt⟩ ↔ ⟨x, hx⟩ ∈ (u ⟨i, hi_lt⟩ : Set Y) := Set.ext_iff.mp (hU_eq ⟨i, hi_lt⟩) ⟨x, hx⟩
          have h2 : x ∈ U ⟨j, hj_lt⟩ ↔ ⟨x, hx⟩ ∈ (u ⟨j, hj_lt⟩ : Set Y) := Set.ext_iff.mp (hU_eq ⟨j, hj_lt⟩) ⟨x, hx⟩
          have h3 : x ∈ U ⟨i, hi_lt⟩ ↔ x ∈ U ⟨j, hj_lt⟩ := Set.ext_iff.mp heq_set x
          exact h1.symm.trans (h3.trans h2)
        exact Subtype.ext (congr_arg Subtype.val (hu_inj H))
      · exfalso
        apply hu_ne ⟨i, hi_lt⟩
        ext ⟨x, hx⟩
        have h_eq : x ∈ U ⟨i, hi_lt⟩ ↔ x ∈ Yᶜ := Set.ext_iff.mp heq_set x
        have h_Yc : x ∈ Yᶜ ↔ False := iff_of_false (fun h_not => h_not hx) id
        have h_u : x ∈ U ⟨i, hi_lt⟩ ↔ ⟨x, hx⟩ ∈ (u ⟨i, hi_lt⟩ : Set Y) := Set.ext_iff.mp (hU_eq ⟨i, hi_lt⟩) ⟨x, hx⟩
        exact h_u.symm.trans (h_eq.trans h_Yc)
      · exfalso
        apply hu_ne ⟨j, hj_lt⟩
        ext ⟨x, hx⟩
        have h_eq : x ∈ Yᶜ ↔ x ∈ U ⟨j, hj_lt⟩ := Set.ext_iff.mp heq_set x
        have h_Yc : x ∈ Yᶜ ↔ False := iff_of_false (fun h_not => h_not hx) id
        have h_u : x ∈ U ⟨j, hj_lt⟩ ↔ ⟨x, hx⟩ ∈ (u ⟨j, hj_lt⟩ : Set Y) := Set.ext_iff.mp (hU_eq ⟨j, hj_lt⟩) ⟨x, hx⟩
        exact h_u.symm.trans (h_eq.symm.trans h_Yc)
      · exact Subtype.ext (by omega)

    obtain ⟨m', V, hV_cov, hV_ref, hV_ord⟩ := hdim (m + 1) U_ext h_cov hU_ext_ne hU_ext_inj

    let v : {j : ℕ // j < m'} → TopologicalSpace.Opens ↥Y := fun j =>
      ⟨(↑) ⁻¹' (V j : Set X), (V j).isOpen.preimage continuous_subtype_val⟩

    refine ⟨m', v, ?_, ?_, ?_⟩
    · ext ⟨x, hx⟩
      simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion, Set.mem_univ, iff_true]
      have hV : (⋃ j, (V j : Set X)) = Set.univ := by rw [← TopologicalSpace.Opens.coe_iSup, hV_cov, TopologicalSpace.Opens.coe_top]
      exact Set.mem_iUnion.mp (hV.symm ▸ Set.mem_univ x)
    · intro j
      obtain ⟨i, hi⟩ := hV_ref j
      by_cases h_lt : i.val < m
      · exact ⟨⟨i.val, h_lt⟩, fun ⟨x, hx⟩ hVj => by
          have h_in_U_ext : x ∈ (U_ext i : Set X) := hi hVj
          dsimp only [U_ext] at h_in_U_ext
          rw [dif_pos h_lt] at h_in_U_ext
          exact (Set.ext_iff.mp (hU_eq ⟨i.val, h_lt⟩) ⟨x, hx⟩).mp h_in_U_ext⟩
      · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
        exact ⟨⟨0, hm_pos⟩, fun ⟨x, hx⟩ hVj => by
          have h_in_U_ext : x ∈ (U_ext i : Set X) := hi hVj
          dsimp only [U_ext] at h_in_U_ext
          rw [dif_neg h_lt] at h_in_U_ext
          exact False.elim (h_in_U_ext hx)⟩
    · intro f hf
      have h_ord := hV_ord f hf
      ext ⟨x, hx⟩
      simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
      intro h_in
      have h_empty : x ∈ (∅ : Set X) := by
        rw [← h_ord]
        simp only [Set.mem_iInter]
        exact h_in
      exact h_empty
