module
public import KMV.DensityCounting
public import Mathlib.Tactic.Ring
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V]
open scoped Classical

theorem triple_with_nonexpandable_pair {H : Hypergraph V} {r : ℕ}
    (hH : RankBounds H r) (hfree : LooseTriangleFree H) {e : Finset V}
    (he : e ∈ H) (hc : e.card = 3) :
    ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ e = {a,b,c} ∧ ¬ Expandable H r {a,b} := by
  obtain ⟨P,hPc,hPe,hP⟩ := edge_contains_nonexpandable_pair hH hfree he
  obtain ⟨c,hcP,hce⟩ := Finset.exists_eq_insert_iff.mpr ⟨hPe,by omega⟩
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hPc
  have hca : c ≠ a := fun h => hcP (by simp [h])
  have hcb : c ≠ b := fun h => hcP (by simp [h])
  refine ⟨a,b,c,hab,hca.symm,hcb.symm,?_,hP⟩
  apply hce.symm.trans
  ext z
  simp only [mem_insert, mem_singleton]
  tauto

theorem triple_light_cover {H : Hypergraph V} {r : ℕ}
    (hH : RankBounds H r) (hfree : LooseTriangleFree H) {e : Finset V}
    (he : e ∈ H) (hc : e.card = 3) :
    ∃ v, e ∈ lightStar H r v ∨
      ∃ x ∈ singleLightVertices H r v, e ∈ containingEdges H 3 {v,x} := by
  obtain ⟨a,b,c,hab,hac,hbc,rfl,hP⟩ := triple_with_nonexpandable_pair hH hfree he hc
  by_cases hQ : Expandable H r {a,c}
  · by_cases hR : Expandable H r {b,c}
    · refine ⟨a,Or.inr ⟨b,?_,?_⟩⟩
      · exact mem_filter.mpr ⟨mem_univ _,hab.symm,hP,c,hac.symm,hbc.symm,he,hQ,hR⟩
      · exact mem_filter.mpr ⟨he,hc,by simp⟩
    · refine ⟨b,Or.inl ?_⟩
      simp only [lightStar, mem_filter]
      refine ⟨he,hc,by simp,?_⟩
      intro x hx hxb
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · simpa [Finset.pair_comm] using hP
      · exact False.elim (hxb rfl)
      · exact hR
  · refine ⟨a,Or.inl ?_⟩
    simp only [lightStar, mem_filter]
    refine ⟨he,hc,by simp,?_⟩
    intro x hx hxa
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact False.elim (hxa rfl)
    · exact hP
    · exact hQ

theorem exists_largest_independent {H : Hypergraph V} {r : ℕ} (hH : RankBounds H r) :
    ∃ I : Finset V, Independent H I ∧ ∀ J, Independent H J → J.card ≤ I.card := by
  classical
  have h0 : Independent H ∅ := by
    intro e he hs
    have hc := card_le_card hs
    have := (hH e he).1
    simp only [card_empty] at hc
    omega
  let F := (Finset.univ : Finset V).powerset.filter (Independent H)
  obtain ⟨I,hI,hmax⟩ := Finset.exists_max_image F Finset.card
    (show F.Nonempty from ⟨∅,by simp [F,h0]⟩)
  refine ⟨I,(mem_filter.mp hI).2,fun J hJ => ?_⟩
  exact hmax J (by simp [F,hJ])

/-- Density reduction with an explicit, deliberately nonoptimal constant.
Using nonexpandable pairs as light pairs gives m3 ≤ 6 r n α, hence
α ≥ d3/(18 r). This is sufficient for the main theorem's r-dependent constant. -/
theorem density {H : Hypergraph V} {r : ℕ}
    (hH : RankBounds H r) (hfree : LooseTriangleFree H) :
    ∃ I : Finset V, Independent H I ∧
      codegree H 3 ∅ ≤ 6*r*(Fintype.card V)*I.card := by
  classical
  obtain ⟨I,hI,hmax⟩ := exists_largest_independent hH
  let C := fun v => lightStar H r v ∪
    (singleLightVertices H r v).biUnion (fun x => containingEdges H 3 {v,x})
  have hcover : containingEdges H 3 ∅ ⊆ Finset.univ.biUnion C := by
    intro e he
    obtain ⟨heH,hec,_⟩ := mem_filter.mp he
    obtain ⟨v,hv⟩ := triple_light_cover hH hfree heH hec
    refine mem_biUnion.mpr ⟨v,mem_univ _,?_⟩
    rcases hv with hv | ⟨x,hx,he⟩
    · exact mem_union_left _ hv
    · exact mem_union_right _ (mem_biUnion.mpr ⟨x,hx,he⟩)
  have hC : ∀ v, (C v).card ≤ 6*r*I.card := by
    intro v
    obtain ⟨J,hJ,hL⟩ := lightStar_bound hH hfree v
    have hJc := hmax J hJ
    have hXc := hmax _ (singleLightVertices_independent hH hfree v)
    have hU := singleLightCover_bound H r v
    have hc := Finset.card_union_le (lightStar H r v)
      ((singleLightVertices H r v).biUnion (fun x => containingEdges H 3 {v,x}))
    change _ ≤ 6*r*I.card
    have hL' := hL.trans (Nat.mul_le_mul_left (4*r) hJc)
    have hU' := hU.trans (Nat.mul_le_mul_left (2*r) hXc)
    calc
      _ ≤ (lightStar H r v).card +
          ((singleLightVertices H r v).biUnion (fun x => containingEdges H 3 {v,x})).card := hc
      _ ≤ 4*r*I.card + 2*r*I.card := Nat.add_le_add hL' hU'
      _ = 6*r*I.card := by ring
  refine ⟨I,hI,?_⟩
  calc
    _ ≤ (Finset.univ.biUnion C).card := card_le_card hcover
    _ ≤ ∑ v : V, (C v).card := card_biUnion_le
    _ ≤ ∑ _v : V, 6*r*I.card := sum_le_sum (fun v _ => hC v)
    _ = 6*r*(Fintype.card V)*I.card := by simp [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm]

end KMV
