import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sets.OpenCover


/-!


Copyright (c) 2026 Cheenta Lean Project. All rights reserved.
Authors: Adhiraj Anand, Niranjan Rao, Parum Sarda, Shravas Matta, Shreesh Nayak, Shreya Iyer


-/


/-!
# Covering Dimension


This file develops basic definitions and lemmas concerning covers, their
multiplicity, order, and refinements.
-/


open Set


universe u v


variable {X : Type u} [TopologicalSpace X]


/-!
### Multiplicity and order
-/


/--
`multiplicity u x n` expresses a condition on the family of sets `u`
containing a point `x`.
-/
def multiplicity
   {ι : Type*}
   (u : ι → Set X) (x : X) (_ : ℕ) : Prop :=
 ∀ s : Set ι, (∀ i ∈ s, x ∈ u i) →
   ∀ f : ℕ → ι, (∀ n, f n ∈ s) → ¬Function.Injective f


/--
`HasOrderLE v n` expresses that the intersection of any `n + 2`
distinct members of the family `v` is empty.
-/
def HasOrderLE {κ : Type*} (v : κ → Set X) (n : ℕ) : Prop :=
 ∀ s : Finset κ,
   s.card = n + 2 →
     (⋂ k ∈ (↑s : Set κ), v k) = ∅


/-!
### Refinements
-/


/--
A family `v` refines a family `u` if every member of `v` is contained
in some member of `u`.
-/
def Refines
   {ι κ : Type*}
   (v : κ → Set X)
   (u : ι → Set X) : Prop :=
 ∀ k : κ, ∃ i : ι, v k ⊆ u i


omit [TopologicalSpace X] in
lemma refines_refl
   {ι : Type*}
   (u : ι → Set X) :
   Refines u u := by
 intro i
 exact ⟨i, subset_rfl⟩


omit [TopologicalSpace X] in
lemma refines_trans
   {ι κ σ : Type*}
   {u : ι → Set X}
   {v : κ → Set X}
   {w : σ → Set X}
   (h₁ : Refines w v)
   (h₂ : Refines v u) :
   Refines w u := by
 intro s
 rcases h₁ s with ⟨k, hkv⟩
 rcases h₂ k with ⟨i, hui⟩
 refine ⟨i, ?_⟩
 exact Set.Subset.trans hkv hui


/-!
### Basic covers
-/


/--
The trivial cover consisting of the universal set indexed by `Unit`.
-/
def trivialCover : Unit → Set X :=
 fun _ => Set.univ


lemma trivialCover_open :
   TopologicalSpace.IsOpenCover
     (fun _ => ⟨Set.univ, isOpen_univ⟩ : Unit → TopologicalSpace.Opens X) := by
 classical
 simp [TopologicalSpace.IsOpenCover]


omit [TopologicalSpace X] in
lemma trivialCover_order :
   HasOrderLE (trivialCover : Unit → Set X) 0 := by
 classical
 intro s hs
 have hcard : s.card ≤ 1 := by
   refine (s.card_le_one).2 ?_
   intro a ha b hb
   exact Subsingleton.elim a b
 have hlt : s.card < 2 :=
   Nat.lt_of_le_of_lt hcard (by decide)
 have hfalse : False := by
   rw [hs] at hlt
   exact Nat.lt_irrefl 2 hlt
 exact hfalse.elim


/-!
### Restriction of covers
-/


omit [TopologicalSpace X] in
lemma restrict_cover_union
   {ι : Type*}
   (u : ι → Set X)
   (hu : (⋃ i, u i) = Set.univ)
   (Y : Set X) :
   (⋃ i, (Y ∩ u i)) = Y := by
 calc
   ⋃ i, (Y ∩ u i) = Y ∩ (⋃ i, u i) := by
     rw [Set.inter_iUnion]
   _ = Y ∩ Set.univ := by
     rw [hu]
   _ = Y := by
     simp
