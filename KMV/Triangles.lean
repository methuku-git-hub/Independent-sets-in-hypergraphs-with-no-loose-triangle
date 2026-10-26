module
public import KMV.Statements
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V] {e f g : Finset V}

/-- Exact three-vertex formulation from Li--Postle, Definition 1.2. -/
theorem triangle_iff_witnesses : Triangle e f g ↔
    ∃ u v w : V, u ≠ v ∧ v ≠ w ∧ w ≠ u ∧
      {u, v} ⊆ e ∧ {v, w} ⊆ f ∧ {w, u} ⊆ g ∧
      {u, v, w} ∩ e ∩ f ∩ g = ∅ := by
  simp only [Triangle, Finset.Nonempty, Finset.mem_sdiff, Finset.mem_inter,
    Finset.insert_subset_iff, Finset.singleton_subset_iff,
    Finset.eq_empty_iff_forall_notMem, Finset.mem_insert, Finset.mem_singleton]
  grind

theorem triangle_edges_distinct (ht : Triangle e f g) : e ≠ f ∧ f ≠ g ∧ g ≠ e := by
  rcases ht with ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩
  simp only [Finset.mem_sdiff, Finset.mem_inter] at hx hy hz
  grind

theorem loose_triangle_is_triangle (ht : LooseTriangle e f g) : Triangle e f g := by
  obtain ⟨_, _, _, hef, hfg, hge, hempty⟩ := ht
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (e ∩ f).card by omega)
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 < (f ∩ g).card by omega)
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (show 0 < (g ∩ e).card by omega)
  have hem : ∀ v, ¬ (v ∈ e ∧ v ∈ f ∧ v ∈ g) := by
    intro v hv
    have : v ∈ e ∩ f ∩ g := by simp only [Finset.mem_inter]; tauto
    rw [hempty] at this
    simp at this
  refine ⟨⟨x, ?_⟩, ⟨y, ?_⟩, ⟨z, ?_⟩⟩ <;>
    simp only [Finset.mem_sdiff, Finset.mem_inter] at * <;> grind

theorem triangle_free_loose_triangle_free {H : Hypergraph V} (h : TriangleFree H) :
    LooseTriangleFree H := by
  intro e he f hf g hg ht
  exact h e he f hf g hg (loose_triangle_is_triangle ht)

end KMV
