import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Data.Fintype.Card
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Sets.OpenCover

/-
Copyright (c) 2026 Cheenta Lean Project. All rights reserved.
Authors : Adhiraj Anand, Niranjan Rao, Parum Sarda, Shravas Matta, Shreesh Nayak, Shreya Iyer
-/


open Set
universe u v
variable {X : Type u} [TopologicalSpace X]

def multiplicity
   {ι : Type*}
   (u : ι → Set X) (x : X) (_ : ℕ) : Prop :=
  ∀ (s : Set ι), (∀ i ∈ s, x ∈ u i) →
    (∀ (f : ℕ → ι), (∀ n, f n ∈ s) → ¬ Function.Injective f)

def HasOrderLENiranjan {κ : Type*} (v : κ → Set X) (n : ℕ) : Prop :=
  ∀ (f : Fin (n + 2) → κ), Function.Injective f → (⋂ i, v (f i)) = ∅

 def HasOrderLE {κ : Type*} (v : κ → Set X) (n : ℕ) : Prop :=
  ∀ s : Finset κ,
    s.card = n + 2 →
    (⋂ k ∈ (↑s : Set κ), v k) = ∅

/-def IsOpenCover {ι : Type*}
 (u : ι → Set X) : Prop :=
 (∀ i, IsOpen (u i)) ∧
 (⋃ i, u i) = univ-/

def Refines {ι : Type*}
  {κ : Type*} (v : κ → Set X)
  (u : ι → Set X) : Prop :=
    ∀ k : κ, ∃ i : ι, v k ⊆ u i

def trivialCover : Unit → Set X :=
  fun _ => Set.univ

lemma trivialCover_open :
   TopologicalSpace.IsOpenCover (fun _ => ⟨Set.univ, isOpen_univ⟩ : Unit → TopologicalSpace.Opens X) := by
 classical
 simp [TopologicalSpace.IsOpenCover]

omit [TopologicalSpace X] in
lemma refines_refl
  {ι : Type*}
  (u : ι → Set X) :
  Refines u u := by
    intro i
    exact ⟨i, subset_rfl⟩

omit [TopologicalSpace X] in
lemma refines_trans
   {ι : Type*}
   {κ : Type*}
   {σ : Type*}
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

omit [TopologicalSpace X] in
lemma trivialCover_order :
    HasOrderLE (trivialCover : Unit → Set X) 0 := by
  classical
  intro s hs
  have hcard : s.card ≤ 1 := by
    classical
    refine (s.card_le_one).2 ?_
    intro a ha b hb
    exact Subsingleton.elim a b
  have hlt : s.card < 2 := Nat.lt_of_le_of_lt hcard (by decide)
  have hfalse : False := by
    rw [hs] at hlt
    exact Nat.lt_irrefl 2 hlt
  exact hfalse.elim

omit [TopologicalSpace X] in
lemma restrict_cover_union
   {ι : Type*}
   (u : ι → Set X)
   (hu : (⋃ i, u i) = Set.univ)
   (Y : Set X) :
   (⋃ i, (Y ∩ u i)) = Y := by
   calc
   ⋃ i, (Y ∩ u i)
       = Y ∩ (⋃ i, u i) := by
           rw [Set.inter_iUnion]
   _ = Y ∩ Set.univ := by
           rw [hu]
   _ = Y := by
           simp
