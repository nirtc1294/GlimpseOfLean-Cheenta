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
theorem Dim0_iff_clopen_refinement
    [Nonempty X] [T1Space X] [NormalSpace X] :
    (∀ (ι : Type v)
        (u : ι → TopologicalSpace.Opens X),
        TopologicalSpace.IsOpenCover u →
        ∃ (κ : Type κu)
          (w : κ → TopologicalSpace.Opens X),
          TopologicalSpace.IsOpenCover w ∧
          Refines (fun k => (w k : Set X)) (fun i => (u i : Set X)) ∧
          HasOrderLE (fun k => (w k : Set X)) 0) ↔
      ∀ (ι : Type v)
        (U : ι → TopologicalSpace.Opens X),
        TopologicalSpace.IsOpenCover U →
        ∃ (κ : Type κu)
          (c : κ → Set X),
          (∀ k : κ, IsClopen (c k)) ∧
          ⋃ k, c k = (Set.univ : Set X) ∧
          Pairwise (fun i j => Disjoint (c i) (c j)) ∧
          Refines c (fun i => ((U i : Set X))) := by
  constructor
  · -- Forward Direction: CoveringDimensionLE 0 → Clopen Refinement
    intro h_dim ι U hu
    rcases h_dim ι U hu with ⟨κ : Type κu, w', hw_cover, hw_ref, hw_order⟩
    letI : DecidableEq κ := Classical.decEq κ

    have hw_disj : Pairwise (fun i j => Disjoint (w' i : Set X) (w' j : Set X)) := by
      intro i j hij
      rw [Set.disjoint_iff_inter_eq_empty]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hxi, hxj⟩
      have hcard : ({i, j} : Finset κ).card = 0 + 2 := by
        rw [zero_add, Finset.card_eq_two]
        exact ⟨i, j, hij, rfl⟩
      have hx_inter : x ∈ ⋂ k ∈ (↑({i, j} : Finset κ) : Set κ), (w' k : Set X) := by
        simp only [Set.mem_iInter, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
        rintro k (rfl | rfl)
        · exact hxi
        · exact hxj
      rw [hw_order {i, j} hcard] at hx_inter
      exact (Set.mem_empty_iff_false x).mp hx_inter

    have hw_cover_univ : ⋃ i, (w' i : Set X) = univ := hw_cover.iSup_set_eq_univ
    refine ⟨κ, fun k => (w' k : Set X), ?_, hw_cover_univ, hw_disj, hw_ref⟩
    intro k
    refine ⟨?_, (w' k).isOpen⟩
    rw [← isOpen_compl_iff (s := (w' k : Set X))]
    have h_compl : (w' k : Set X)ᶜ = ⋃ (j : {j // j ≠ k}), (w' j.val : Set X) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion]
      constructor
      · intro hxk
        have hx_univ : x ∈ ⋃ i, (w' i : Set X) := by
          rw [hw_cover_univ]
          exact Set.mem_univ x
        rcases Set.mem_iUnion.mp hx_univ with ⟨j, hj⟩
        have hjk : j ≠ k := by
          rintro rfl
          exact hxk hj
        exact ⟨⟨j, hjk⟩, hj⟩
      · rintro ⟨⟨j, hjk⟩, hj⟩ hxk
        have h_disj_jk : Disjoint (w' j : Set X) (w' k : Set X) := hw_disj hjk
        rw [Set.disjoint_iff_inter_eq_empty] at h_disj_jk
        have h_in : x ∈ (w' j : Set X) ∩ (w' k : Set X) := ⟨hj, hxk⟩
        rw [h_disj_jk] at h_in
        exact (Set.mem_empty_iff_false x).mp h_in
    rw [h_compl]
    exact isOpen_iUnion (fun j => (w' j.val).isOpen)

  · -- Backward Direction: Clopen Refinement → CoveringDimensionLE 0
    intro h_clopen ι U hu
    rcases h_clopen ι U hu with ⟨κ : Type κu, c, hc_clopen, hc_univ, hc_disj, hc_ref⟩
    letI : DecidableEq κ := Classical.decEq κ

    have hc_cov : TopologicalSpace.IsOpenCover (fun k => ⟨c k, (hc_clopen k).2⟩ : κ → TopologicalSpace.Opens X) := by
      classical
      have hc_union : ⋃ k, c k = univ := hc_univ
      exact TopologicalSpace.IsOpenCover.of_sets (fun k => (hc_clopen k).2) hc_union

    refine ⟨κ, fun k => ⟨c k, (hc_clopen k).2⟩, hc_cov, hc_ref, ?_⟩
    intro s hs
    have h2 : s.card = 2 := by rwa [zero_add] at hs
    obtain ⟨i, j, hij, hs_eq⟩ := Finset.card_eq_two.mp h2
    rw [hs_eq]
    ext x
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    intro hx
    have hxi : x ∈ c i := hx i (by simp)
    have hxj : x ∈ c j := hx j (by simp)
    have h_in : x ∈ c i ∩ c j := ⟨hxi, hxj⟩
    have h_disj_ij : Disjoint (c i) (c j) := hc_disj hij
    rw [Set.disjoint_iff_inter_eq_empty] at h_disj_ij
    rw [h_disj_ij] at h_in
    exact (Set.mem_empty_iff_false x).mp h_in
