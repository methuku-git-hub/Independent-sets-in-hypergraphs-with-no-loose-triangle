module
public import KMV.DensityStructure
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V]

theorem two_stars_looseTriangle {F : Finset V} {v x y a b : V}
    (hx : x ∈ F) (hy : y ∈ F) (hv : v ∉ F) (ha : a ∉ F) (hb : b ∉ F)
    (hxy : x ≠ y) (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b) :
    LooseTriangle ({v,x,a} : Finset V) {v,y,b} F := by
  have hxv : x ≠ v := fun h => hv (h ▸ hx)
  have hyv : y ≠ v := fun h => hv (h ▸ hy)
  have hxa : x ≠ a := fun h => ha (h ▸ hx)
  have hyb : y ≠ b := fun h => hb (h ▸ hy)
  have h₁ : ({v,x,a} : Finset V) ∩ {v,y,b} = {v} := by
    ext z
    simp only [mem_inter, mem_insert, mem_singleton]
    grind
  have h₂ : ({v,y,b} : Finset V) ∩ F = {y} := by
    ext z
    simp only [mem_inter, mem_insert, mem_singleton]
    grind
  have h₃ : F ∩ ({v,x,a} : Finset V) = {x} := by
    ext z
    simp only [mem_inter, mem_insert, mem_singleton]
    grind
  have hFc : 2 ≤ F.card := by
    have he : ({x,y} : Finset V) ⊆ F := insert_subset_iff.mpr ⟨hx,singleton_subset_iff.mpr hy⟩
    simpa [hxy] using card_le_card he
  apply looseTriangle_of_card_inter
    (by simp [hxv.symm,hav.symm,hxa]) (by simp [hyv.symm,hbv.symm,hyb]) hFc
    (by simp [h₁]) (by simp [h₂]) (by simp [h₃])
  rw [h₁]
  simp [hv]

theorem star_pair_looseTriangle {F : Finset V} {v x y a : V}
    (hx : x ∈ F) (hy : y ∈ F) (hv : v ∉ F) (ha : a ∉ F)
    (hxy : x ≠ y) (hav : a ≠ v) :
    LooseTriangle ({v,x,a} : Finset V) {y,a} F := by
  have hxv : x ≠ v := fun h => hv (h ▸ hx)
  have hxa : x ≠ a := fun h => ha (h ▸ hx)
  have hya : y ≠ a := fun h => ha (h ▸ hy)
  have h₁ : ({v,x,a} : Finset V) ∩ {y,a} = {a} := by
    ext z
    simp only [mem_inter, mem_insert, mem_singleton]
    grind
  have h₂ : ({y,a} : Finset V) ∩ F = {y} := by
    ext z
    simp only [mem_inter, mem_insert, mem_singleton]
    grind
  have h₃ : F ∩ ({v,x,a} : Finset V) = {x} := by
    ext z
    simp only [mem_inter, mem_insert, mem_singleton]
    grind
  have hFc : 2 ≤ F.card := by
    have he : ({x,y} : Finset V) ⊆ F := insert_subset_iff.mpr ⟨hx,singleton_subset_iff.mpr hy⟩
    simpa [hxy] using card_le_card he
  apply looseTriangle_of_card_inter
    (by simp [hxv.symm,hav.symm,hxa]) (by simp [hya]) hFc
    (by simp [h₁]) (by simp [h₂]) (by simp [h₃])
  rw [h₁]
  simp [ha]

/-- The one-light-pair case of the density reduction. Expandability allows
the last extension to be discharged by the already proved Lemma 4.1. -/
theorem unique_light_star_independent {H : Hypergraph V} {r : ℕ}
    (hH : RankBounds H r) (hfree : LooseTriangleFree H)
    {v : V} {X : Finset V} (hvX : v ∉ X)
    (hstar : ∀ x ∈ X, ∃ a, a ≠ v ∧ a ∉ X ∧ {v,x,a} ∈ H ∧ Expandable H r {x,a}) :
    Independent H X := by
  intro F hF hFX
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp
    (show 1 < F.card by have := (hH F hF).1; omega)
  obtain ⟨a,hav,haX,hea,hex⟩ := hstar x (hFX hx)
  obtain ⟨b,hbv,hbX,heb,hey⟩ := hstar y (hFX hy)
  have hv : v ∉ F := fun h => hvX (hFX h)
  have ha : a ∉ F := fun h => haX (hFX h)
  have hb : b ∉ F := fun h => hbX (hFX h)
  by_cases hab : a = b
  · subst b
    exact expandable_no_loose_triangle hH hfree (edge_expandable hH hea) hey
      (edge_expandable hH hF) (star_pair_looseTriangle hx hy hv ha hxy hav)
  · exact hfree _ hea _ heb F hF (two_stars_looseTriangle hx hy hv ha hb hxy hav hbv hab)

end KMV
