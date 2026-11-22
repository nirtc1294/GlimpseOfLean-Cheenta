import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sets.OpenCover
import Mathlib.Topology.Connected.Clopen
import Mathlib.Order.WellFoundedSet
import Cheenta_Proofs.BasicLemmasforCD
import Cheenta_Proofs.Covering_Dimension

open Set Topology
universe u v
variable {X : Type u} [TopologicalSpace X]

theorem Dim0_iff_clopen_refinement_iff_clopen_basis
    [Nonempty X] [T1Space X] [NormalSpace X] [LindelofSpace X] :
    ((∀ (ι : Type v) (u : ι → TopologicalSpace.Opens X),
        TopologicalSpace.IsOpenCover u →
        ∃ (κ : Type u) (w : κ → TopologicalSpace.Opens X),
          TopologicalSpace.IsOpenCover w ∧
          Refines (fun k => (w k : Set X)) (fun i => (u i : Set X)) ∧
          HasOrderLE (fun k => (w k : Set X)) 0) ↔
      ∀ (ι : Type v) (U : ι → TopologicalSpace.Opens X),
        TopologicalSpace.IsOpenCover U →
        ∃ (κ : Type u) (c : κ → Set X),
          (∀ k : κ, IsClopen (c k)) ∧
          ⋃ k, c k = (Set.univ : Set X) ∧
          Pairwise (fun i j => Disjoint (c i) (c j)) ∧
          Refines c (fun i => ((U i : Set X)))) ∧
    ((∀ (ι : Type v) (u : ι → TopologicalSpace.Opens X),
        TopologicalSpace.IsOpenCover u →
        ∃ (κ : Type u) (w : κ → TopologicalSpace.Opens X),
          TopologicalSpace.IsOpenCover w ∧
          Refines (fun k => (w k : Set X)) (fun i => (u i : Set X)) ∧
          HasOrderLE (fun k => (w k : Set X)) 0) ↔
      ∀ (p : X) (U : TopologicalSpace.Opens X), p ∈ (U : Set X) →
        ∃ (V : Set X), IsClopen V ∧ p ∈ V ∧ V ⊆ (U : Set X)) := by
  -- Helper: B → A (Clopen partition refinement implies covering dim ≤ 0)
  have h_B_to_A :
      (∀ (ι : Type v) (U : ι → TopologicalSpace.Opens X),
        TopologicalSpace.IsOpenCover U →
        ∃ (κ : Type u) (c : κ → Set X),
          (∀ k : κ, IsClopen (c k)) ∧
          ⋃ k, c k = (Set.univ : Set X) ∧
          Pairwise (fun i j => Disjoint (c i) (c j)) ∧
          Refines c (fun i => (U i : Set X))) →
      (∀ (ι : Type v) (u : ι → TopologicalSpace.Opens X),
        TopologicalSpace.IsOpenCover u →
        ∃ (κ : Type u) (w : κ → TopologicalSpace.Opens X),
          TopologicalSpace.IsOpenCover w ∧
          Refines (fun k => (w k : Set X)) (fun i => (u i : Set X)) ∧
          HasOrderLE (fun k => (w k : Set X)) 0) := by
    intro h_clopen ι U hu
    rcases h_clopen ι U hu with ⟨κ, c, hc_clopen, hc_univ, hc_disj, hc_ref⟩
    letI : DecidableEq κ := Classical.decEq κ
    have hc_cov : TopologicalSpace.IsOpenCover
        (fun k => ⟨c k, (hc_clopen k).2⟩ : κ → TopologicalSpace.Opens X) :=
      TopologicalSpace.IsOpenCover.of_sets (fun k => (hc_clopen k).2) hc_univ
    refine ⟨κ, fun k => ⟨c k, (hc_clopen k).2⟩, hc_cov, hc_ref, ?_⟩
    intro s hs
    have h2 : s.card = 2 := by rwa [zero_add] at hs
    obtain ⟨i, j, hij, hs_eq⟩ := Finset.card_eq_two.mp h2
    rw [hs_eq]
    ext x
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    intro hx
    have h_in : x ∈ c i ∩ c j := ⟨hx i (by simp), hx j (by simp)⟩
    have h_disj_ij : Disjoint (c i) (c j) := hc_disj hij
    rw [Set.disjoint_iff_inter_eq_empty] at h_disj_ij
    rw [h_disj_ij] at h_in
    exact (Set.mem_empty_iff_false x).mp h_in

  constructor
  · -- Case 1: A ↔ B
    constructor
    · intro h_dim ι U hu
      rcases h_dim ι U hu with ⟨κ, w', hw_cover, hw_ref, hw_order⟩
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
      rw [← isOpen_compl_iff]
      have h_compl : (w' k : Set X)ᶜ = ⋃ (j : {j // j ≠ k}), (w' j.val : Set X) := by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_iUnion]
        constructor
        · intro hxk
          have hx_univ : x ∈ ⋃ i, (w' i : Set X) := by rw [hw_cover_univ]; exact trivial
          rcases Set.mem_iUnion.mp hx_univ with ⟨j, hj⟩
          exact ⟨⟨j, by rintro rfl; exact hxk hj⟩, hj⟩
        · rintro ⟨⟨j, hjk⟩, hj⟩ hxk
          have h_disj_jk : Disjoint (w' j : Set X) (w' k : Set X) := hw_disj hjk
          rw [Set.disjoint_iff_inter_eq_empty] at h_disj_jk
          have h_in : x ∈ (w' j : Set X) ∩ (w' k : Set X) := ⟨hj, hxk⟩
          rw [h_disj_jk] at h_in
          exact (Set.mem_empty_iff_false x).mp h_in
      rw [h_compl]
      exact isOpen_iUnion (fun j => (w' j.val).isOpen)
    · exact h_B_to_A

  · -- Case 2: A ↔ C
    constructor
    · -- A → C
      intro h_dim p U hp
      let u : ULift.{v} Bool → TopologicalSpace.Opens X := fun b =>
        if b.down then U else ⟨({p} : Set X)ᶜ, isOpen_compl_singleton⟩
      have hu_union : ⋃ b, (u b : Set X) = Set.univ := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
        by_cases hx : x = p
        · exact ⟨ULift.up true, by simpa [hx] using hp⟩
        · exact ⟨ULift.up false, hx⟩
      have hu_cover : TopologicalSpace.IsOpenCover u :=
        TopologicalSpace.IsOpenCover.of_sets (fun b => (u b).isOpen) hu_union
      rcases h_dim (ULift.{v} Bool) u hu_cover with ⟨κ, w, hw_cov, hw_ref, hw_order⟩
      letI : DecidableEq κ := Classical.decEq κ
      have hw_disj : Pairwise (fun i j => Disjoint (w i : Set X) (w j : Set X)) := by
        intro i j hij
        rw [Set.disjoint_iff_inter_eq_empty]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hxi, hxj⟩
        have hcard : ({i, j} : Finset κ).card = 0 + 2 := by
          rw [zero_add, Finset.card_eq_two]
          exact ⟨i, j, hij, rfl⟩
        have hx_inter : x ∈ ⋂ k ∈ (↑({i, j} : Finset κ) : Set κ), (w k : Set X) := by
          simp only [Set.mem_iInter, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
          rintro k (rfl | rfl)
          · exact hxi
          · exact hxj
        rw [hw_order {i, j} hcard] at hx_inter
        exact (Set.mem_empty_iff_false x).mp hx_inter
      have hw_cov_univ : ⋃ k, (w k : Set X) = Set.univ := hw_cov.iSup_set_eq_univ
      rcases Set.mem_iUnion.mp (hw_cov_univ.symm ▸ Set.mem_univ p) with ⟨k, hk⟩
      refine ⟨w k, ?_, hk, ?_⟩
      · refine ⟨?_, (w k).isOpen⟩
        rw [← isOpen_compl_iff]
        have h_compl : (w k : Set X)ᶜ = ⋃ (j : {j // j ≠ k}), (w j.val : Set X) := by
          ext x
          simp only [Set.mem_compl_iff, Set.mem_iUnion]
          constructor
          · intro hxk
            rcases Set.mem_iUnion.mp (hw_cov_univ.symm ▸ Set.mem_univ x) with ⟨j, hj⟩
            exact ⟨⟨j, by rintro rfl; exact hxk hj⟩, hj⟩
          · rintro ⟨⟨j, hjk⟩, hj⟩ hxk
            have h_disj_jk : Disjoint (w j : Set X) (w k : Set X) := hw_disj hjk
            rw [Set.disjoint_iff_inter_eq_empty] at h_disj_jk
            have h_in : x ∈ (w j : Set X) ∩ (w k : Set X) := ⟨hj, hxk⟩
            rw [h_disj_jk] at h_in
            exact (Set.mem_empty_iff_false x).mp h_in
        rw [h_compl]
        exact isOpen_iUnion (fun j => (w j.val).isOpen)
      · rcases hw_ref k with ⟨b, hb⟩
        dsimp [u] at hb
        split_ifs at hb with h_b
        · exact hb
        · exact False.elim ((hb hk) rfl)

    · -- C → A (via C → B and h_B_to_A)
      intro h_basis
      apply h_B_to_A
      intro ι U hu
      have h_cover_univ : ⋃ i, (U i : Set X) = Set.univ := hu.iSup_set_eq_univ
      have hx_in_U : ∀ x : X, ∃ i : ι, x ∈ (U i : Set X) := fun x =>
        Set.mem_iUnion.mp (h_cover_univ.symm ▸ Set.mem_univ x)
      choose f hf using hx_in_U
      choose V hV_clopen hV_mem hV_sub using fun x => h_basis x (U (f x)) (hf x)

      -- Extract a countable subcover using Lindelöf
      obtain ⟨s, hs_count, hs_cov⟩ :=
        isLindelof_univ.elim_nhds_subcover V (fun x _ => (hV_clopen x).2.mem_nhds (hV_mem x))
      -- Enumerate the countable subcover by ℕ
      have hs_nonempty : s.Nonempty := by
        obtain ⟨x₀⟩ := ‹Nonempty X›
        have hx₀ : x₀ ∈ ⋃ x ∈ s, V x := hs_cov.2 (mem_univ x₀)
        rcases mem_iUnion₂.mp hx₀ with ⟨x, hxs, _⟩
        exact ⟨x, hxs⟩
      obtain ⟨g, hg_surj⟩ := hs_count.exists_eq_range hs_nonempty

      -- Disjointify the countable clopen cover: c n = V (g n) \ ⋃ k < n, V (g k)
      let c : ℕ → Set X := fun n => V (g n) \ ⋃ k < n, V (g k)
      refine ⟨ULift.{u} ℕ, fun n => c n.down, ?_, ?_, ?_, ?_⟩
      · -- Each c n is clopen (clopen minus a FINITE union of clopen sets)
        intro n
        dsimp only
        have h_fin_union : IsClopen (⋃ k ∈ Finset.range n.down, V (g k)) :=
          isClopen_biUnion_finset (fun k _ => hV_clopen (g k))
        have h_eq : c n.down = V (g n.down) \ ⋃ k ∈ Finset.range n.down, V (g k) := by
          dsimp only [c]
          congr 1
          ext y
          simp [Finset.mem_range]
        rw [h_eq]
        exact (hV_clopen (g n.down)).diff h_fin_union
      · -- Covers univ (by Nat.find on the first n with x ∈ V (g n))
        ext x
        simp only [mem_iUnion, mem_univ, iff_true]
        have hx_s : x ∈ ⋃ y ∈ s, V y := hs_cov.2 (mem_univ x)
        rcases mem_iUnion₂.mp hx_s with ⟨y, hys, hy⟩
        rw [hg_surj] at hys
        rcases hys with ⟨m, rfl⟩
        classical
        let n := Nat.find (⟨m, hy⟩ : ∃ k, x ∈ V (g k))
        refine ⟨ULift.up n, Nat.find_spec (⟨m, hy⟩ : ∃ k, x ∈ V (g k)), ?_⟩
        simp only [mem_iUnion, exists_prop, not_exists, not_and]
        intro k hk
        exact Nat.find_min (⟨m, hy⟩ : ∃ k, x ∈ V (g k)) hk
      · -- Pairwise disjoint
        intro i j hij
        rw [Set.disjoint_iff_inter_eq_empty]
        ext x
        simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
        rintro ⟨hxi, hxj⟩
        have hne : i.down ≠ j.down := fun h => hij (ULift.ext _ _ h)
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact hxj.2 (mem_iUnion₂.mpr ⟨i.down, hlt, hxi.1⟩)
        · exact hxi.2 (mem_iUnion₂.mpr ⟨j.down, hgt, hxj.1⟩)
      · -- Refines U
        intro n
        exact ⟨f (g n.down), Set.diff_subset.trans (hV_sub (g n.down))⟩
