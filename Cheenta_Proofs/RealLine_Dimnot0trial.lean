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
  obtain ⟨κ, v, hvclopen, hvcov, hvdisj, hvref⟩ := (Dim0_iff_clopen_refinement (X := ℝ)).mp h u hu
  obtain ⟨s, hsU, hsuniv⟩ := isConnected_iff_sUnion_disjoint_open.mp
    (isConnected_univ (α := ℝ))
    (Set.range (fun k => (v k : Set ℝ)))
    (fun a ha b hb hab => by
      simp only [Set.mem_range] at ha hb
      obtain ⟨k₁, rfl⟩ := ha; obtain ⟨k₂, rfl⟩ := hb
      by_contra hne
      exact absurd hab (by simp [hvdisj k₁ k₂ (fun h => hne (congrArg _ h))]))
    (fun s hs => by
      simp only [Set.mem_range] at hs
      obtain ⟨k, rfl⟩ := hs
      exact (v k).isOpen)
    (fun x _ => by
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hvcov.2 ▸ Set.mem_univ x)
      exact ⟨(v k : Set ℝ), Set.mem_range_self k, hk⟩)
  simp only [Set.mem_range] at hsU
  obtain ⟨k, rfl⟩ := hsU
  obtain ⟨i, hi⟩ := hvref k
  have hfull : (u i : Set ℝ) = Set.univ :=
    Set.eq_univ_of_univ_subset (Set.eq_univ_of_univ_subset hsuniv ▸ hi)
  have hi2 : i.val = 0 ∨ i.val = 1 := by omega
  rcases hi2 with h0 | h1
  · simp [u, show i = (0 : Fin 2) from Fin.ext h0] at hfull
  · simp [u, show i = (1 : Fin 2) from Fin.ext h1] at hfull
