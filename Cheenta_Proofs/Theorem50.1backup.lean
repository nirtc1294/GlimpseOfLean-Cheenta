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
universe v w
variable {X : Type u} [TopologicalSpace X]

theorem subspaceOfDimension
  {Y : Set X} (hY : IsClosed Y) {n : ℕ} (hdim : Covering_Dimension_2.{u, v} (X := X) n) :
  Covering_Dimension_2.{u, v} (X := ↥Y) n := by
    unfold Covering_Dimension_2
    intro ι u hu
    choose U hU_open hU_eq using fun i => isOpen_induced_iff.mp (u i).isOpen
    let U_ext : Option ι → Set X := fun
      | none => Yᶜ
      | some i => U i
    have h_cov : TopologicalSpace.IsOpenCover U_ext := by
      refine ⟨fun | none => isOpen_compl_iff.mpr hY | some i => hU_open i, ?_⟩
      ext x; simp only [U_ext, Set.mem_iUnion, Set.mem_univ, iff_true]
      by_cases hx : x ∈ Y
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hu.2.symm ▸ Set.mem_univ (⟨x, hx⟩ : Y))
        exact ⟨some i, by rwa [← hU_eq i] at hi⟩
      · exact ⟨none, hx⟩
    by_cases hι : Nonempty ι
    · rcases hdim (Option ι) U_ext h_cov with ⟨κ, v, hv_cov, hv_ref, hv_ord⟩
      refine ⟨κ, fun k => Subtype.val ⁻¹' v k,
        ⟨fun k => (hv_cov.1 k).preimage continuous_subtype_val,
        by rw [← Set.preimage_iUnion, hv_cov.2, Set.preimage_univ]⟩, ?_, ?_⟩
      · intro k
        rcases hv_ref k with ⟨_ | i, hj⟩
        · exact ⟨Classical.choice hι, fun y hy => (hj hy y.prop).elim⟩
        · exact ⟨i, fun y hy => hU_eq i ▸ hj hy⟩
      · intro f hf
        rw [← Set.preimage_iInter, hv_ord f hf, Set.preimage_empty]
    · have hYa : IsEmpty ↥Y := ⟨fun y => by
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hu.2.symm ▸ Set.mem_univ y)
        exact hι ⟨i⟩⟩
      refine ⟨(PEmpty : Type v), (fun _ => ∅), ⟨?_, ?_⟩, ?_, ?_⟩
      · intro i; exact i.elim
      · ext y; exact (hYa.false y).elim
      · intro i; exact i.elim
      · intro f; exact (f 0).elim
