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
variable {X : Type u} [TopologicalSpace X]
universe v w

-- Theorem: If Y is a closed subspace of X, and dim(X) ≤ n, then dim(Y) ≤ n.
theorem subspaceOfDimension
  {Y : Set X} (hY : IsClosed Y) {n : ℕ} (hdim : CoveringDimensionLE.{u, v, w} (X := X) n) :
  CoveringDimensionLE.{u, v, w} (X := ↥Y) n := by

  -- Let `u` be an arbitrary open cover of Y indexed by `ι`.
  -- `hu` is the proof that its union (iSup) covers the whole subspace (⊤).
  unfold CoveringDimensionLE
  intro ι u hu

  -- By definition of the subspace topology, every open set `u i` in Y
  -- is the intersection of some open set `U i` in X with Y.
  -- We use the Axiom of Choice (`choose`) to extract these `U i`.
  choose U hU_open hU_eq using fun i => isOpen_induced_iff.mp (u i).isOpen

  -- We construct an open cover of X, mathematically: { U_i }_i ∪ { Yᶜ }.
  -- `Option ι` adds a single extra element (`none`) to the index set `ι` to represent Yᶜ.
  let U_ext : Option ι → TopologicalSpace.Opens X := fun
    | none => ⟨Yᶜ, isOpen_compl_iff.mpr hY⟩ -- Yᶜ is open because Y is closed (hY)
    | some i => ⟨U i, hU_open i⟩            -- The lifted open sets

  -- The proof splits based on whether our original index set `ι` is empty or not.
  by_cases hι : Nonempty ι
  ·
    -- CASE 1: `ι` is not empty.

    -- First, we prove that `U_ext` actually covers X.
    have h_cov_sup : iSup U_ext = ⊤ := by
      ext x -- To prove set equality, take an arbitrary point x ∈ X
      simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion, Set.mem_univ, iff_true]
      -- If x ∈ Y, it's covered by some `u i`, therefore it's in `U i` (index: some i)
      -- If x ∉ Y, it's in Yᶜ (index: none)
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

    have h_cov : TopologicalSpace.IsOpenCover U_ext := h_cov_sup

    -- Apply the dimension hypothesis of X (dim X ≤ n) to our cover `U_ext`.
    -- This gives us a new refinement cover `V` indexed by `κ`.
    -- hv_cov: V covers X. hv_ref: V refines U_ext. hv_ord: order of V ≤ n.
    rcases hdim U_ext h_cov with ⟨κ, V, hv_cov, hv_ref, hv_ord⟩

    -- Restrict the refinement `V` back to Y (mathematically: V_k ∩ Y).
    -- In Lean, we express this as the preimage of the inclusion map (Subtype.val).
    let V_Y : κ → TopologicalSpace.Opens ↥Y := fun k => ⟨Subtype.val ⁻¹' (V k : Set X), (V k).isOpen.preimage continuous_subtype_val⟩

    -- Prove that `V_Y` covers Y (since V covers X, this is trivial).
    have hc_sup : iSup V_Y = ⊤ := by
      ext ⟨y, hy⟩
      simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion, Set.mem_univ, iff_true]
      have hv_sup : iSup V = ⊤ := hv_cov
      have hS : (⋃ k, (V k : Set X)) = Set.univ := by rw [← TopologicalSpace.Opens.coe_iSup, hv_sup, TopologicalSpace.Opens.coe_top]
      have hy_univ : y ∈ Set.univ := Set.mem_univ y
      rw [← hS] at hy_univ
      rcases Set.mem_iUnion.mp hy_univ with ⟨k, hk⟩
      exact ⟨k, hk⟩
    have hc : TopologicalSpace.IsOpenCover V_Y := hc_sup

    -- Prove that `V_Y` refines `u`.
    -- For any k, V_k is inside either U_i (so V_k ∩ Y ⊆ u_i) or Yᶜ (so V_k ∩ Y = ∅, which refines anything).
    have hr : Refines (fun k => (V_Y k : Set ↥Y)) (fun i => (u i : Set ↥Y)) := by
      intro k
      rcases hv_ref k with ⟨i_opt, hj⟩
      cases i_opt with
      -- If V_k was inside Yᶜ, its restriction to Y is empty. We just map it to an arbitrary index of `u`.
      | none => exact ⟨Classical.choice hι, fun y hy => (hj hy y.prop).elim⟩
      -- If V_k was inside U_i, its restriction to Y is inside u_i.
      | some i => exact ⟨i, fun y hy => (Set.ext_iff.mp (hU_eq i) y).mp (hj hy)⟩

    -- Prove the order of `V_Y` is ≤ n.
    -- Any intersection of sets in V_Y is contained in the intersection of the corresponding sets in V.
    -- Since no n+2 sets in V intersect (hv_ord), no n+2 sets in V_Y intersect.
    have ho : HasOrderLE (fun k => (V_Y k : Set ↥Y)) n := by
      intro s hs
      have H := hv_ord s hs
      ext ⟨y, hy⟩
      constructor
      · intro hy_in
        have hy_X : y ∈ ⋂ k ∈ (s : Set κ), (V k : Set X) := by
          simp only [Set.mem_iInter] at hy_in ⊢
          exact hy_in
        rw [H] at hy_X
        exact hy_X
      · intro h_empty
        exact h_empty.elim

    -- Provide the restricted cover `V_Y` as the proof that dim(Y) ≤ n.
    exact ⟨κ, V_Y, hc, hr, ho⟩

  ·
    -- CASE 2: `ι` is empty.
    -- If an empty collection of sets covers Y, then Y itself must be empty.
    have hYa : IsEmpty ↥Y := ⟨fun y => by
      have hu_sup : iSup u = ⊤ := hu
      have hS : (⋃ i, (u i : Set ↥Y)) = Set.univ := by rw [← TopologicalSpace.Opens.coe_iSup, hu_sup, TopologicalSpace.Opens.coe_top]
      have hy_univ : y ∈ Set.univ := Set.mem_univ y
      rw [← hS] at hy_univ
      have h_ex : ∃ i, y ∈ u i := Set.mem_iUnion.mp hy_univ
      rcases h_ex with ⟨i, _⟩
      exact hι ⟨i⟩⟩

    -- For an empty space, we can provide the empty cover (indexed by `PEmpty`).
    -- This trivially satisfies all conditions (covers the empty set, refines the empty set, has order 0 ≤ n).
    have hc_sup : iSup (fun (_ : PEmpty) => (⊥ : TopologicalSpace.Opens ↥Y)) = ⊤ := by ext y; exact (hYa.false y).elim
    have hc : TopologicalSpace.IsOpenCover (fun (_ : PEmpty) => (⊥ : TopologicalSpace.Opens ↥Y)) := hc_sup
    have hr : Refines (fun (j : PEmpty) => ((⊥ : TopologicalSpace.Opens ↥Y) : Set ↥Y)) (fun i => (u i : Set ↥Y)) := fun j => j.elim
    have ho : HasOrderLE (fun (j : PEmpty) => ((⊥ : TopologicalSpace.Opens ↥Y) : Set ↥Y)) n := by
      intro s hs
      ext ⟨y, hy⟩
      exact (hYa.false ⟨y, hy⟩).elim
    exact ⟨PEmpty, fun _ => ⊥, hc, hr, ho⟩
