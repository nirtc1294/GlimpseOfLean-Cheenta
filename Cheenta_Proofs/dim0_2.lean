import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sets.OpenCover
import Mathlib.Topology.Connected.Clopen
import Cheenta_Proofs.BasicLemmasforCD
import Cheenta_Proofs.Covering_Dimension

/-
Copyright (c) 2026 Cheenta Lean Project. All rights reserved.
Authors : Adhiraj Anand, Niranjan Rao, Parum Sarda, Shravas Matta, Shreesh Nayak, Shreya Iyer
-/

open Set Topology

universe u v w u' κu

variable {X : Type u} [TopologicalSpace X]

/-- Main Theorem: Covering dimension ≤ 0 is equivalent to every open cover
    admitting a refinement that is a clopen partition. -/
theorem coveringDimensionLE_zero_iff_clopen_refinement
    [Nonempty X] [T1Space X] [NormalSpace X] :
    (∀ (ι : Type v) (u : ι → TopologicalSpace.Opens X), TopologicalSpace.IsOpenCover u →
        ∃ (κ : Type κu) (w : κ → TopologicalSpace.Opens X),
          TopologicalSpace.IsOpenCover w ∧
          Refines (fun k => (w k : Set X)) (fun i => (u i : Set X)) ∧
          HasOrderLE (fun k => (w k : Set X)) 0) ↔
      ∀ (ι : Type v) (U : ι → TopologicalSpace.Opens X), TopologicalSpace.IsOpenCover U →
        ∃ (κ : Type κu) (c : κ → Set X),
          (∀ k : κ, IsClopen (c k)) ∧
          ⋃ k, c k = (Set.univ : Set X) ∧
          Pairwise (fun i j => Disjoint (c i) (c j)) ∧
          Refines c (fun i => ((U i : Set X))) := by
  constructor
  · intro h_dim ι U hu
    rcases h_dim ι U hu with ⟨κ : Type κu, w', hw_cover, hw_ref, hw_order⟩
    letI : DecidableEq κ := Classical.decEq κ
    have hw_disj : Pairwise (fun i j => Disjoint (w' i : Set X) (w' j : Set X)) := by
      intro i j hij
      rw [Set.disjoint_iff_inter_eq_empty]
      ext x; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hxi, hxj⟩
      have hcard : ({i, j} : Finset κ).card = 0 + 2 := by rw [zero_add, Finset.card_eq_two]; exact ⟨i, j, hij, rfl⟩
      exact (Set.mem_empty_iff_false x).mp (by simpa [hw_order {i, j} hcard] using
        by simp only [Set.mem_iInter, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
           rintro k (rfl | rfl); exact hxi; exact hxj)
    have hw_cover_univ : ⋃ i, (w' i : Set X) = univ := hw_cover.iSup_set_eq_univ
    refine ⟨κ, fun k => (w' k : Set X), ?_, hw_cover_univ, hw_disj, hw_ref⟩
    intro k; refine ⟨?_, (w' k).isOpen⟩; rw [← isOpen_compl_iff]
    have h_compl : (w' k : Set X)ᶜ = ⋃ (j : {j // j ≠ k}), (w' j.val : Set X) := by
      ext x; simp only [Set.mem_compl_iff, Set.mem_iUnion]; constructor
      · intro hxk
        have hx_univ : x ∈ ⋃ i, (w' i : Set X) := by rw [hw_cover_univ]; exact Set.mem_univ x
        rcases Set.mem_iUnion.mp hx_univ with ⟨j, hj⟩
        exact ⟨⟨j, fun h => hxk (h ▸ hj)⟩, hj⟩
      · rintro ⟨⟨j, hjk⟩, hj⟩ hxk
        have h_disj_jk : Disjoint (w' j : Set X) (w' k : Set X) := hw_disj hjk
        rw [Set.disjoint_iff_inter_eq_empty] at h_disj_jk
        exact (Set.mem_empty_iff_false x).mp (h_disj_jk ▸ by simpa using ⟨hj, hxk⟩)
    exact h_compl ▸ isOpen_iUnion fun j => (w' j.val).isOpen
  · intro h_clopen ι U hu
    rcases h_clopen ι U hu with ⟨κ : Type κu, c, hc_clopen, hc_univ, hc_disj, hc_ref⟩
    letI : DecidableEq κ := Classical.decEq κ
    refine ⟨κ, fun k => ⟨c k, (hc_clopen k).2⟩, TopologicalSpace.IsOpenCover.of_sets (fun k => (hc_clopen k).2) hc_univ, hc_ref, ?_⟩
    intro s hs; obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp (by simpa using hs)
    ext x; simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    rintro hx
    have dis : c i ∩ c j = ∅ := (Set.disjoint_iff_inter_eq_empty).1 (hc_disj hij)
    exact dis ▸ by simpa using ⟨hx i (by simp), hx j (by simp)⟩
