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

theorem subspaceOfDimension
  {Y : Set X} (hY : IsClosed Y) {n : ℕ} (hdim : CoveringDimensionLE (X := X) n) :
  CoveringDimensionLE (X := ↥Y) n := by
  unfold CoveringDimensionLE
  intro ι u hu
  choose U hU_open hU_eq using fun i => isOpen_induced_iff.mp (u i).isOpen
  let U_ext : Option ι → TopologicalSpace.Opens X := fun
    | none => ⟨Yᶜ, isOpen_compl_iff.mpr hY⟩
    | some i => ⟨U i, hU_open i⟩

  by_cases hι : Nonempty ι
  · have h_cov_sup : iSup U_ext = ⊤ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion, Set.mem_univ, iff_true]
      by_cases hx : x ∈ Y
      · have hu_sup : iSup u = ⊤ := hu
        have hS : (⋃ i, (u i : Set ↥Y)) = Set.univ := by rw [← TopologicalSpace.Opens.coe_iSup, hu_sup, TopologicalSpace.Opens.coe_top]
        have h_ex : ∃ i, (⟨x, hx⟩ : Y) ∈ u i := by
          have hx_univ : (⟨x, hx⟩ : Y) ∈ Set.univ := Set.mem_univ _
          rw [← hS] at hx_univ
          exact Set.mem_iUnion.mp hx_univ
        rcases h_ex with ⟨i, hi⟩
        exact ⟨some i, (Set.ext_iff.mp (hU_eq i) ⟨x, hx⟩).mpr hi⟩
      · exact ⟨none, hx⟩

    -- Cast to exactly what Shravas's definition expects
    have h_cov : TopologicalSpace.IsOpenCover U_ext := h_cov_sup

    rcases hdim U_ext h_cov with ⟨κ, V, hv_cov, hv_ref, hv_ord⟩
    let V_Y : κ → TopologicalSpace.Opens ↥Y := fun k => ⟨Subtype.val ⁻¹' (V k : Set X), (V k).isOpen.preimage continuous_subtype_val⟩

    have hc_sup : iSup V_Y = ⊤ := by
      ext ⟨y, hy⟩
      simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion, Set.mem_univ, iff_true]
      have hv_sup : iSup V = ⊤ := hv_cov
      have hS : (⋃ k, (V k : Set X)) = Set.univ := by rw [← TopologicalSpace.Opens.coe_iSup, hv_sup, TopologicalSpace.Opens.coe_top]
      have hy_univ : y ∈ Set.univ := Set.mem_univ y
      rw [← hS] at hy_univ
      exact Set.mem_iUnion.mp hy_univ

    have hc : TopologicalSpace.IsOpenCover V_Y := hc_sup

    have hr : Refines (fun k => (V_Y k : Set ↥Y)) (fun i => (u i : Set ↥Y)) := by
      intro k
      rcases hv_ref k with ⟨i_opt, hj⟩
      cases i_opt with
      | none => exact ⟨Classical.choice hι, fun y hy => (hj hy y.prop).elim⟩
      | some i => exact ⟨i, fun y hy => (Set.ext_iff.mp (hU_eq i) y).mp (hj hy)⟩

    have ho : HasOrderLE (fun k => (V_Y k : Set ↥Y)) n := by
      intro s hs
      have H := hv_ord s hs
      rw [Set.eq_empty_iff_forall_not_mem]
      intro ⟨y, hy⟩ hy_in
      rw [Set.eq_empty_iff_forall_not_mem] at H
      apply H y
      simp only [Set.mem_iInter] at hy_in ⊢
      intro k hk
      exact hy_in k hk

    exact ⟨κ, V_Y, hc, hr, ho⟩

  · have hYa : IsEmpty ↥Y := ⟨fun y => by
      have hu_sup : iSup u = ⊤ := hu
      have hS : (⋃ i, (u i : Set ↥Y)) = Set.univ := by rw [← TopologicalSpace.Opens.coe_iSup, hu_sup, TopologicalSpace.Opens.coe_top]
      have hy_univ : y ∈ Set.univ := Set.mem_univ y
      rw [← hS] at hy_univ
      have h_ex : ∃ i, y ∈ u i := Set.mem_iUnion.mp hy_univ
      rcases h_ex with ⟨i, _⟩
      exact hι ⟨i⟩⟩

    have hc_sup : iSup (fun (_ : PEmpty) => (⊥ : TopologicalSpace.Opens ↥Y)) = ⊤ := by ext y; exact (hYa.false y).elim
    have hc : TopologicalSpace.IsOpenCover (fun (_ : PEmpty) => (⊥ : TopologicalSpace.Opens ↥Y)) := hc_sup

    have hr : Refines (fun (j : PEmpty) => ((⊥ : TopologicalSpace.Opens ↥Y) : Set ↥Y)) (fun i => (u i : Set ↥Y)) := fun j => j.elim

    have ho : HasOrderLE (fun (j : PEmpty) => ((⊥ : TopologicalSpace.Opens ↥Y) : Set ↥Y)) n := by
      intro s hs
      rw [Set.eq_empty_iff_forall_not_mem]
      intro ⟨y, hy⟩ _
      exact (hYa.false ⟨y, hy⟩).elim

    exact ⟨PEmpty, fun _ => ⊥, hc, hr, ho⟩
