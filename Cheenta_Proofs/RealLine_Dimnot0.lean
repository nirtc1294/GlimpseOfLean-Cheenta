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

theorem real_not_dim0 : ¬ CoveringDimensionLE (X := ℝ) 0 := by
  intro h
  classical
  let u : Fin 2 → Set ℝ := fun i => if i = 0 then Set.Iio 1 else Set.Ioi 0
  have hu : TopologicalSpace.IsOpenCover u := by
    constructor
    · intro i
      show IsOpen (if i = 0 then Set.Iio (1:ℝ) else Set.Ioi 0)
      split_ifs <;> [exact isOpen_Iio; exact isOpen_Ioi]
    · ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      by_cases hx : x < 1
      · exact ⟨0, by simp [u, hx]⟩
      · exact ⟨1, by simp [u]; push_neg at hx; linarith⟩
  have hFin := h (Fin 2) inferInstance u hu
  obtain ⟨κ, hκ, v, hvcov, hvref, hvord⟩ := hFin
  obtain ⟨κ, hκ, v, hvcov, hvref, hvdisj⟩ :=
    (dim0_iff_disjoint_clopen_refinement u hu).mp ⟨κ, hκ, v, hvcov, hvref, hvord⟩
  haveI : Fintype κ := hκ
  obtain ⟨s, hsU, hsuniv⟩ := isConnected_iff_sUnion_disjoint_open.mp
    (isConnected_univ (α := ℝ))
    (Finset.univ.image v)
    (fun a ha b hb hab => by
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
      obtain ⟨k₁, rfl⟩ := ha; obtain ⟨k₂, rfl⟩ := hb
      by_contra hne
      exact absurd hab (by simp [hvdisj k₁ k₂ (fun h => hne (congrArg v h))]))
    (fun s hs => by
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hs
      obtain ⟨k, rfl⟩ := hs
      exact hvcov.1 k)
    (fun x _ => by
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hvcov.2 ▸ Set.mem_univ x)
      exact ⟨v k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩, hk⟩)
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hsU
  obtain ⟨k, rfl⟩ := hsU
  obtain ⟨i, hi⟩ := hvref k
  have hfull : u i = Set.univ :=
    Set.eq_univ_of_univ_subset (Set.eq_univ_of_univ_subset hsuniv ▸ hi)
  have hi2 : i.val = 0 ∨ i.val = 1 := by omega
  rcases hi2 with h0 | h1
  · simp [u, show i = (0 : Fin 2) from Fin.ext h0] at hfull
  · simp [u, show i = (1 : Fin 2) from Fin.ext h1] at hfull
