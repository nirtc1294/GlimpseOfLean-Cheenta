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
  · have h_cov : iSup U_ext = ⊤ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion, Set.mem_univ, iff_true]
      by_cases hx : x ∈ Y
      · have hS : (⋃ i, (u i : Set ↥Y)) = Set.univ := by rw [← TopologicalSpace.Opens.coe_iSup, hu, TopologicalSpace.Opens.coe_top]
        have h_ex : ∃ i, (⟨x, hx⟩ : Y) ∈ u i := Set.mem_iUnion.mp (hS.symm ▸ Set.mem_univ (⟨x, hx⟩ : Y))
        rcases h_ex with ⟨i, hi⟩
        exact ⟨some i, (Set.ext_iff.mp (hU_eq i) ⟨x, hx⟩).mpr hi⟩
      · exact ⟨none, hx⟩
    rcases hdim _ h_cov with ⟨κ, V, hv_cov, hv_ref, hv_ord⟩
    let V_Y : κ → TopologicalSpace.Opens ↥Y := fun k => ⟨Subtype.val ⁻¹' (V k : Set X), (V k).isOpen.preimage continuous_subtype_val⟩
    have hc : iSup V_Y = ⊤ := by
      ext ⟨y, hy⟩
      simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion, Set.mem_univ, iff_true, TopologicalSpace.Opens.coe_mk, Set.mem_preimage]
      have hS : (⋃ k, (V k : Set X)) = Set.univ := by rw [← TopologicalSpace.Opens.coe_iSup, hv_cov, TopologicalSpace.Opens.coe_top]
      exact Set.mem_iUnion.mp (hS.symm ▸ Set.mem_univ y)
    have hr : ∀ (k : κ), ∃ i, (V_Y k : Set ↥Y) ⊆ (u i : Set ↥Y) := by
      intro k
      rcases hv_ref k with ⟨i_opt, hj⟩
      cases i_opt
      · exact ⟨Classical.choice hι, fun y hy => (hj hy y.prop).elim⟩
      · rename_i i
        exact ⟨i, fun y hy => (Set.ext_iff.mp (hU_eq i) y).mp (hj hy)⟩
    have ho : HasOrderLE (fun k => (V_Y k : Set ↥Y)) n := by
      intro f hf
      ext ⟨y, hy⟩
      simpa [Set.mem_iInter] using Set.ext_iff.mp (hv_ord f hf) y
    exact ⟨κ, V_Y, hc, hr, ho⟩
  · have hYa : IsEmpty ↥Y := ⟨fun y => by
      have hS : (⋃ i, (u i : Set ↥Y)) = Set.univ := by rw [← TopologicalSpace.Opens.coe_iSup, hu, TopologicalSpace.Opens.coe_top]
      have h_ex : ∃ i, y ∈ u i := Set.mem_iUnion.mp (hS.symm ▸ Set.mem_univ y)
      rcases h_ex with ⟨i, _⟩
      exact hι ⟨i⟩⟩
    have hc : iSup (fun (_ : PEmpty) => (⊥ : TopologicalSpace.Opens ↥Y)) = ⊤ := by ext y; exact (hYa.false y).elim
    have hr : ∀ (j : PEmpty), ∃ i, ((⊥ : TopologicalSpace.Opens ↥Y) : Set ↥Y) ⊆ (u i : Set ↥Y) := fun j => j.elim
    have ho : HasOrderLE (fun (j : PEmpty) => ((⊥ : TopologicalSpace.Opens ↥Y) : Set ↥Y)) n := by intro f hf; ext y; exact (hYa.false y).elim
    exact ⟨PEmpty, fun _ => ⊥, hc, hr, ho⟩
