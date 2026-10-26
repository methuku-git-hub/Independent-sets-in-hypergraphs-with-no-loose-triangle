module
public import KMV.ConfigurationMonotone
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V]
open scoped Classical

@[expose] noncomputable def separatedUnions (H : Hypergraph V) (G : V → V → Prop) : Hypergraph V :=
  ({3,4} : Finset ℕ).biUnion (fun i => ({3,4} : Finset ℕ).biUnion (separatedPairUnions H G i))

@[expose] noncomputable def fourTripleUnions (H : Hypergraph V) : Hypergraph V :=
  configurationUnions (intersectingAt H 4 4 3) (fun p => p.1 ∪ p.2) 5

@[expose] def highRankEdges (H : Hypergraph V) : Hypergraph V :=
  H.filter (fun e => 5 ≤ e.card)

@[expose] noncomputable def forbiddenUnions (H : Hypergraph V) (G : V → V → Prop) : Hypergraph V :=
  ((separatedUnions H G ∪ fourTripleUnions H) ∪ remainingTriangleUnions H) ∪ highRankEdges H

theorem independent_union_iff {H K : Hypergraph V} {U : Finset V} :
    Independent (H ∪ K) U ↔ Independent H U ∧ Independent K U := by
  constructor
  · intro h
    exact ⟨fun e he => h e (mem_union_left _ he),fun e he => h e (mem_union_right _ he)⟩
  · rintro ⟨hH,hK⟩ e he
    rcases mem_union.mp he with he | he
    · exact hH e he
    · exact hK e he

set_option maxHeartbeats 1000000 in
theorem separated_pair_union_mem {H : Hypergraph V} {G : V → V → Prop} {e f : Finset V}
    (he : e ∈ H) (hf : f ∈ H) (hec : 3 ≤ e.card ∧ e.card ≤ 4) (hfc : 3 ≤ f.card ∧ f.card ≤ 4)
    (hint : (e ∩ f).card = 2) (hsep : Separated G (e ∪ f)) :
    e ∪ f ∈ separatedUnions H G := by
  have hi : e.card ∈ ({3,4} : Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
  have hj : f.card ∈ ({3,4} : Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
  have hsize : (e ∪ f).card=e.card+f.card-2 := by
    have hc := card_union_add_card_inter e f
    omega
  have hp : (e,f) ∈ intersectingAt H e.card f.card 2 :=
    mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_filter.mpr ⟨he,rfl,empty_subset _⟩,mem_filter.mpr ⟨hf,rfl,empty_subset _⟩⟩,hint.ge⟩
  have hm : e ∪ f ∈ separatedPairUnions H G e.card f.card := by
    simp only [separatedPairUnions,configurationUnions,mem_image,mem_filter]
    exact ⟨(e,f),⟨⟨hp,hsep⟩,hsize⟩,rfl⟩
  simp only [separatedUnions,mem_biUnion]
  exact ⟨e.card,hi,f.card,hj,hm⟩

theorem four_three_union_mem {H : Hypergraph V} {e f : Finset V}
    (he : e ∈ H) (hf : f ∈ H) (hec : e.card = 4) (hfc : f.card = 4)
    (hint : (e ∩ f).card = 3) : e ∪ f ∈ fourTripleUnions H := by
  have hsize : (e ∪ f).card=5 := by have hc := card_union_add_card_inter e f; omega
  have hp : (e,f) ∈ intersectingAt H 4 4 3 :=
    mem_filter.mpr ⟨mem_product.mpr ⟨mem_filter.mpr ⟨he,hec,empty_subset _⟩,
      mem_filter.mpr ⟨hf,hfc,empty_subset _⟩⟩,hint.ge⟩
  exact configurationUnions_mem (C:=intersectingAt H 4 4 3) (U:=fun p => p.1 ∪ p.2) (c:=(e,f)) hp hsize

/-- Deterministic cleaning: avoid the listed unions and retain graph
independence. The full original induced hypergraph then has only edges of sizes 3 and 4 and no
Li--Postle triangle, with every transfer from the original families explicit. -/
theorem cleaned_triangleFree {H : Hypergraph V} {G : V → V → Prop} {r : ℕ}
    (hr : RankBounds H r) (ha : Antichain H) (hl : LooseTriangleFree H)
    (hsep : ∀ e ∈ H, (∀ x ∈ e, ∀ y ∈ e, ¬ G x y) → Separated G e)
    {U : Finset V} (hG : ∀ x ∈ U, ∀ y ∈ U, ¬ G x y)
    (hB : Independent (forbiddenUnions H G) U) :
    RankBounds (induced H U) 4 ∧ TriangleFree (induced H U) := by
  have hparts : ((Independent (separatedUnions H G) U ∧ Independent (fourTripleUnions H) U) ∧
      Independent (remainingTriangleUnions H) U) ∧ Independent (highRankEdges H) U := by
    simpa only [forbiddenUnions,independent_union_iff] using hB
  have hsub : induced H U ⊆ H := filter_subset _ _
  have hr' : RankBounds (induced H U) 4 := by
    intro e he
    have heH := hsub he
    refine ⟨(hr e heH).1,?_⟩
    by_contra hn
    exact hparts.2 e (mem_filter.mpr ⟨heH,by omega⟩) (mem_filter.mp he).2
  have hs : ∀ e ∈ induced H U, Separated G e := by
    intro e he
    exact hsep e (hsub he) (fun x hx y hy => hG x ((mem_filter.mp he).2 hx) y ((mem_filter.mp he).2 hy))
  have hbad₂ : ∀ e ∈ induced H U, ∀ f ∈ induced H U, e ≠ f → (e ∩ f).card=2 →
      ¬ Separated G (e ∪ f) := by
    intro e he f hf _ hint hs
    exact hparts.1.1.1 (e ∪ f)
      (separated_pair_union_mem (hsub he) (hsub hf) (hr' e he) (hr' f hf) hint hs)
      (union_subset (mem_filter.mp he).2 (mem_filter.mp hf).2)
  have hbad₃ : ∀ e ∈ induced H U, ∀ f ∈ induced H U, e.card=4 → f.card=4 → (e ∩ f).card≠3 := by
    intro e he f hf hec hfc hint
    exact hparts.1.1.2 (e ∪ f) (four_three_union_mem (hsub he) (hsub hf) hec hfc hint)
      (union_subset (mem_filter.mp he).2 (mem_filter.mp hf).2)
  refine ⟨hr',?_⟩
  intro e he f hf g hg ht
  have hm := triangle_union_covered hr' (induced_antichain ha U) (induced_looseTriangleFree hl U)
    hs hbad₂ hbad₃ he hf hg ht
  exact hparts.1.2 (e ∪ f ∪ g) (remainingTriangleUnions_mono hsub hm)
    (union_subset (union_subset (mem_filter.mp he).2 (mem_filter.mp hf).2) (mem_filter.mp hg).2)

end KMV
