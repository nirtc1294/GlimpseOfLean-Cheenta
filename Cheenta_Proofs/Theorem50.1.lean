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


public section
open Set
universe u v w
variable {X : Type u} [TopologicalSpace X]

theorem subspaceOfDimension
  {Y : Set X}
  (hY : IsClosed Y)
  {n : ℕ}
  (hdim : Covering_Dimension_2.{u, v} (X := X) n) :
  Covering_Dimension_2.{u, v} (X := ↥Y) n := by
  unfold Covering_Dimension_2
  intro ι u hu
  choose U hU_open hU_eq using fun i => isOpen_induced_iff.mp (u i).isOpen

  let U_ext : Option ι → TopologicalSpace.Opens X := fun
    | none => ⟨Yᶜ, isOpen_compl_iff.mpr hY⟩
    | some i => ⟨U i, hU_open i⟩

  have h_cov : TopologicalSpace.IsOpenCover U_ext := by
    ext x
    simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hx : x ∈ Y
    · have hS : (⋃ i, (u i : Set ↥Y)) = Set.univ := by
        rw [← TopologicalSpace.Opens.coe_iSup, hu, TopologicalSpace.Opens.coe_top]
      have hx_univ : (⟨x, hx⟩ : ↥Y) ∈ (Set.univ : Set ↥Y) := Set.mem_univ _
      rw [← hS, Set.mem_iUnion] at hx_univ
      obtain ⟨i, hi⟩ := hx_univ
      exact ⟨some i, (Set.ext_iff.mp (hU_eq i) ⟨x, hx⟩).mpr hi⟩
    · exact ⟨none, hx⟩

  by_cases hι : Nonempty ι
  · rcases hdim (Option ι) U_ext h_cov with ⟨κ, V, hv_cov, hv_ref, hv_ord⟩
    refine ⟨κ, fun k => ⟨Subtype.val ⁻¹' (V k : Set X), (V k).isOpen.preimage continuous_subtype_val⟩, ?_, ?_, ?_⟩
    · ext ⟨y, hy⟩
      simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion, Set.mem_univ, iff_true, TopologicalSpace.Opens.coe_mk, Set.mem_preimage]
      have hS : (⋃ k, (V k : Set X)) = Set.univ := by
        rw [← TopologicalSpace.Opens.coe_iSup, hv_cov, TopologicalSpace.Opens.coe_top]
      have hy_univ : y ∈ (Set.univ : Set X) := Set.mem_univ _
      rw [← hS, Set.mem_iUnion] at hy_univ
      exact hy_univ
    · intro k
      rcases hv_ref k with ⟨none, hj⟩ | ⟨some i, hj⟩
      · exact ⟨Classical.choice hι, fun y hy => (hj hy y.prop).elim⟩
      · exact ⟨i, fun y hy => (Set.ext_iff.mp (hU_eq i) y).mp (hj hy)⟩
    · intro f hf
      ext ⟨y, hy⟩
      have h_ord := Set.ext_iff.mp (hv_ord f hf) y
      rw [Set.mem_empty_iff_false] at h_ord ⊢
      constructor
      · intro h_in
        apply h_ord.mp
        simp_rw [TopologicalSpace.Opens.coe_mk, Set.mem_iInter, Set.mem_preimage] at h_in ⊢
        exact h_in
      · intro h_false
        exact h_false.elim

  · have hYa : IsEmpty ↥Y := ⟨fun y => by
      have hS : (⋃ i, (u i : Set ↥Y)) = Set.univ := by
        rw [← TopologicalSpace.Opens.coe_iSup, hu, TopologicalSpace.Opens.coe_top]
      have hy_univ : y ∈ (Set.univ : Set ↥Y) := Set.mem_univ _
      rw [← hS, Set.mem_iUnion] at hy_univ
      obtain ⟨i, _⟩ := hy_univ
      exact hι ⟨i⟩⟩

    -- We bypass Lean's parser crashing on `⟨(PEmpty : Type v), ...⟩` by binding variables via `let` first
    let κ : Type v := PEmpty
    let V_empty : κ → TopologicalSpace.Opens ↥Y := fun _ => ⊥
    refine ⟨κ, V_empty, ?_, ?_, ?_⟩
    · ext y; exact (hYa.false y).elim
    · intro i; nomatch i
    · intro f hf
      ext y
      exact (hYa.false y).elim
