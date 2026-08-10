import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Regular
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Cheenta_Proofs.BasicLemmasforCD
import Cheenta_Proofs.Dim0_iff_Clopen
import Cheenta_Proofs.Covering_Dimension
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Connected.PathConnected

public section
open Set Filter Function

open Filter Topology
open Classical Set

universe u v

variable {X : Type u} [TopologicalSpace X]

open Set Topology

theorem real_not_dim0 : ¬ CoveringDimensionLE.{0, 0} (X := ℝ) 0 := by
  intro h
  classical
  let u : Fin 2 → TopologicalSpace.Opens ℝ := fun i =>
    if i = 0 then ⟨Set.Iio 1, isOpen_Iio⟩ else ⟨Set.Ioi 0, isOpen_Ioi⟩
  have hu : TopologicalSpace.IsOpenCover u := by
    rw [TopologicalSpace.IsOpenCover]
    ext x
    simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hx : x < 1
    · exact ⟨0, by simp [u, hx]⟩
    · exact ⟨1, by simp [u]; push_neg at hx; linarith⟩
  obtain ⟨κ, v, hvclopen, hvcov, hvdisj, hvref⟩ :=
      (Dim0_iff_clopen_refinement (X := ℝ)).mp (fun ι w hw => h w hw) (Fin 2) u hu
  have h_clopen : ∀ k, (v k : Set ℝ) = ∅ ∨ (v k : Set ℝ) = Set.univ := fun k =>
    isClopen_iff.mp (hvclopen k)
  have h_zero : (0 : ℝ) ∈ (Set.univ : Set ℝ) := Set.mem_univ 0
  rw [← hvcov] at h_zero
  simp only [Set.mem_iUnion] at h_zero
  obtain ⟨k, hk⟩ := h_zero
  have hvk_univ : (v k : Set ℝ) = Set.univ := by
    rcases h_clopen k with h_empty | h_univ
    · rw [h_empty] at hk
      simp at hk
    · exact h_univ
  obtain ⟨i, hi⟩ := hvref k
  have hfull : (u i : Set ℝ) = Set.univ :=
    Set.eq_univ_of_univ_subset (hvk_univ ▸ hi)
  have hi2 : i.val = 0 ∨ i.val = 1 := by omega
  rcases hi2 with h0 | h1
  · simp [u, show i = (0 : Fin 2) from Fin.ext h0] at hfull
    have h_two : (2 : ℝ) ∈ Set.Iio 1 := by
      rw [hfull]
      exact Set.mem_univ 2
    norm_num at h_two

  · simp [u, show i = (1 : Fin 2) from Fin.ext h1] at hfull
    have h_minus_one : (-1 : ℝ) ∈ Set.Ioi 0 := by
      rw [hfull]
      exact Set.mem_univ (-1)
    norm_num at h_minus_one
