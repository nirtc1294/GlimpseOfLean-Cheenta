import Mathlib.Topology.Connected.Basic

theorem sUnion_connected_of_nonempty_intersection
    {α : Type*} [TopologicalSpace α]
    (S : Set (Set α))
    (hS : S.Nonempty)
    (hconn : ∀ s ∈ S, IsConnected s)
    (hint : (⋂₀ S).Nonempty) :
    IsConnected (⋃₀ S) := by
  obtain ⟨x, hx⟩ := hint
  constructor
  · obtain ⟨s, hs⟩ := hS
    exact ⟨x, s, hs, hx s hs⟩
  · apply isPreconnected_sUnion x
    · exact fun s hs => hx s hs
    · exact fun s hs => (hconn s hs).isPreconnected

theorem connected_prod {X₁ X₂ : Type*} [TopologicalSpace X₁] [TopologicalSpace X₂]
    (hX₁ : IsConnected (Set.univ : Set X₁))
    (hX₂ : IsConnected (Set.univ : Set X₂)) :
    IsConnected (Set.univ : Set (X₁ × X₂)) := by
  obtain ⟨x₁, _⟩ := hX₁.nonempty
  obtain ⟨x₂, _⟩ := hX₂.nonempty

  have hslice_conn : IsConnected (Set.univ ×ˢ ({x₂} : Set X₂) : Set (X₁ × X₂)) := by
    constructor
    · exact ⟨(x₁, x₂), by simp⟩
    · intro u v hu hv hcover ⟨⟨a₁, b₁⟩, hab₁, huab₁⟩ ⟨⟨a₂, b₂⟩, hab₂, hvab₂⟩
      simp at hab₁ hab₂
      obtain ⟨_, rfl⟩ := hab₁
      obtain ⟨_, rfl⟩ := hab₂
      have hcover₁ : Set.univ ⊆ (fun a => (a, x₂)) ⁻¹' u ∪ (fun a => (a, x₂)) ⁻¹' v := by
        intro a _
        have : (a, x₂) ∈ Set.univ ×ˢ ({x₂} : Set X₂) := by simp
        exact hcover this
      have hpu : IsOpen ((fun a => (a, x₂)) ⁻¹' u) := hu.preimage (by continuity)
      have hpv : IsOpen ((fun a => (a, x₂)) ⁻¹' v) := hv.preimage (by continuity)
      have hune : (Set.univ ∩ (fun a => (a, x₂)) ⁻¹' u).Nonempty := ⟨a₁, trivial, huab₁⟩
      have hvne : (Set.univ ∩ (fun a => (a, x₂)) ⁻¹' v).Nonempty := ⟨a₂, trivial, hvab₂⟩
      obtain ⟨a, _, hau, hav⟩ := hX₁.2 _ _ hpu hpv hcover₁ hune hvne
      exact ⟨(a, x₂), by simp, hau, hav⟩

  have vslice_conn : ∀ c : X₁, IsConnected (({c} : Set X₁) ×ˢ (Set.univ : Set X₂) : Set (X₁ × X₂)) := by
    intro c
    constructor
    · exact ⟨(c, x₂), by simp⟩
    · intro u v hu hv hcover ⟨⟨a₁, b₁⟩, hab₁, huab₁⟩ ⟨⟨a₂, b₂⟩, hab₂, hvab₂⟩
      simp at hab₁ hab₂
      obtain ⟨rfl, _⟩ := hab₁
      obtain ⟨rfl, _⟩ := hab₂
      have hcover₁ : Set.univ ⊆ (fun b => (c, b)) ⁻¹' u ∪ (fun b => (c, b)) ⁻¹' v := by
        intro b _
        have : (c, b) ∈ ({c} : Set X₁) ×ˢ Set.univ := by simp
        exact hcover this
      have hpu : IsOpen ((fun b => (c, b)) ⁻¹' u) := hu.preimage (by continuity)
      have hpv : IsOpen ((fun b => (c, b)) ⁻¹' v) := hv.preimage (by continuity)
      have hune : (Set.univ ∩ (fun b => (c, b)) ⁻¹' u).Nonempty := ⟨b₁, trivial, huab₁⟩
      have hvne : (Set.univ ∩ (fun b => (c, b)) ⁻¹' v).Nonempty := ⟨b₂, trivial, hvab₂⟩
      obtain ⟨b, _, hbu, hbv⟩ := hX₂.2 _ _ hpu hpv hcover₁ hune hvne
      exact ⟨(c, b), by simp, hbu, hbv⟩

  have cross_conn : ∀ c : X₁, IsConnected (({c} : Set X₁) ×ˢ (Set.univ : Set X₂) ∪ (Set.univ : Set X₁) ×ˢ ({x₂} : Set X₂) : Set (X₁ × X₂)) := by
    intro c
    let S : Set (Set (X₁ × X₂)) := {({c} : Set X₁) ×ˢ Set.univ, Set.univ ×ˢ {x₂}}
    have hSunion : ⋃₀ S = ({c} : Set X₁) ×ˢ Set.univ ∪ Set.univ ×ˢ {x₂} := by
      ext x; simp [S];
    rw [← hSunion]
    apply sUnion_connected_of_nonempty_intersection S
    · exact ⟨({c} : Set X₁) ×ˢ Set.univ, by simp [S]⟩
    · intro s hs
      simp [S] at hs
      rcases hs with rfl | rfl
      · exact vslice_conn c
      · exact hslice_conn
    · exact ⟨(c, x₂), by
        intro s hs
        simp [S] at hs
        rcases hs with rfl | rfl <;> simp⟩

  let crosses := fun c : X₁ => (({c} : Set X₁) ×ˢ (Set.univ : Set X₂) ∪ (Set.univ : Set X₁) ×ˢ ({x₂} : Set X₂) : Set (X₁ × X₂))

  have cover : ⋃₀ (Set.range crosses) = Set.univ := by
    ext ⟨a, b⟩
    constructor
    · intro; trivial
    · intro _
      exact ⟨crosses a, ⟨a, rfl⟩, Or.inl ⟨rfl, trivial⟩⟩

  rw [← cover]
  apply sUnion_connected_of_nonempty_intersection
  · exact ⟨crosses x₁, ⟨x₁, rfl⟩⟩
  · intro s hs
    rcases hs with ⟨c, rfl⟩
    exact cross_conn c
  · exact ⟨(x₁, x₂), by
      intro s hs
      rcases hs with ⟨c, rfl⟩
      exact Or.inr ⟨trivial, rfl⟩⟩
