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
variable {X : Type u} [TopologicalSpace X]

universe v -- Removed `u` to avoid the "already declared" clash

variable {X : Type u} [TopologicalSpace X]

theorem subspaceOfDimension
  {Y : Set X} (hY : IsClosed Y) {n : ℕ} (hdim : Covering_Dimension_2.{u, v} (X := X) n) :
  Covering_Dimension_2.{u, v} (X := ↥Y) n := by
  unfold Covering_Dimension_2
  intro ι u hu
  choose U hU_open hU_eq using fun i => isOpen_induced_iff.mp (u i).isOpen

  let U_ext : Option ι → TopologicalSpace.Opens X := fun
    | none => ⟨Yᶜ, isOpen_compl_iff.mpr hY⟩
    | some i => ⟨U i, hU_open i⟩

  have h_cov : TopologicalSpace.IsOpenCover U_ext := by
    ext x; simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hx : x ∈ Y
    · have hS : (⋃ i, (u i : Set ↥Y)) = Set.univ := by rw [← TopologicalSpace.Opens.coe_iSup, hu, TopologicalSpace.Opens.coe_top]
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hS.symm ▸ Set.mem_univ (⟨x, hx⟩ : Y))
      exact ⟨some i, (Set.ext_iff.mp (hU_eq i) ⟨x, hx⟩).mpr hi⟩
    · exact ⟨none, hx⟩

  by_cases hι : Nonempty ι
  · rcases hdim (Option ι) U_ext h_cov with ⟨κ, V, hv_cov, hv_ref, hv_ord⟩
    refine ⟨κ, fun k => ⟨Subtype.val ⁻¹' (V k : Set X), (V k).isOpen.preimage continuous_subtype_val⟩, ?_, ?_, ?_⟩
    · ext ⟨y, hy⟩
      simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion, Set.mem_univ, iff_true, TopologicalSpace.Opens.coe_mk, Set.mem_preimage]
      have hS : (⋃ k, (V k : Set X)) = Set.univ := by rw [← TopologicalSpace.Opens.coe_iSup, hv_cov, TopologicalSpace.Opens.coe_top]
      exact Set.mem_iUnion.mp (hS.symm ▸ Set.mem_univ y)
    · intro k; rcases hv_ref k with ⟨_ | i, hj⟩
      · exact ⟨Classical.choice hι, fun y hy => (hj hy y.prop).elim⟩
      · exact ⟨i, fun y hy => (Set.ext_iff.mp (hU_eq i) y).mp (hj hy)⟩
    · intro f hf; ext ⟨y, hy⟩
      simpa [Set.mem_iInter] using Set.ext_iff.mp (hv_ord f hf) y

  · have hYa : IsEmpty ↥Y := ⟨fun y => by
      have hS : (⋃ i, (u i : Set ↥Y)) = Set.univ := by rw [← TopologicalSpace.Opens.coe_iSup, hu, TopologicalSpace.Opens.coe_top]
      exact hι ⟨(Set.mem_iUnion.mp (hS.symm ▸ Set.mem_univ y)).choose⟩⟩
    let κ : Type v := PEmpty
    exact ⟨κ, fun _ => ⊥, by ext y; exact (hYa.false y).elim, fun i => i.elim, fun _ _ => by ext y; exact (hYa.false y).elim⟩
