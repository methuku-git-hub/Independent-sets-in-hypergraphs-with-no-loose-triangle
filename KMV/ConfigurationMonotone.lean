module
public import KMV.TriangleCover
public import KMV.RandomDegrees
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V]
open scoped Classical

theorem containingEdges_mono {H K : Hypergraph V} (h : H ⊆ K) (j : ℕ) (P : Finset V) :
    containingEdges H j P ⊆ containingEdges K j P := by
  intro e he
  exact mem_filter.mpr ⟨h (mem_filter.mp he).1,(mem_filter.mp he).2⟩

theorem configurationUnions_mono {α : Type*} [DecidableEq α] {C D : Finset α}
    (h : C ⊆ D) (U : α → Finset V) (k : ℕ) :
    configurationUnions C U k ⊆ configurationUnions D U k := by
  intro e he
  obtain ⟨c,hc,rfl⟩ := mem_image.mp he
  exact mem_image.mpr ⟨c,mem_filter.mpr ⟨h (mem_filter.mp hc).1,(mem_filter.mp hc).2⟩,rfl⟩

theorem intersectingEdgePairs_mono {H K : Hypergraph V} (h : H ⊆ K) (i j : ℕ) :
    intersectingEdgePairs H i j ⊆ intersectingEdgePairs K i j := by
  intro p hp
  obtain ⟨hprod,hint⟩ := mem_filter.mp hp
  obtain ⟨he,hf⟩ := mem_product.mp hprod
  exact mem_filter.mpr ⟨mem_product.mpr ⟨containingEdges_mono h i ∅ he,
    containingEdges_mono h j ∅ hf⟩,hint⟩

theorem tripleExtensions_mono {H K : Hypergraph V} (h : H ⊆ K) (U : Finset V) :
    tripleExtensions H U ⊆ tripleExtensions K U := by
  intro e he
  exact mem_filter.mpr ⟨h (mem_filter.mp he).1,(mem_filter.mp he).2⟩

theorem typeOneCandidates_mono {H K : Hypergraph V} (h : H ⊆ K) (i j : ℕ) :
    typeOneCandidates H i j ⊆ typeOneCandidates K i j := by
  intro t ht
  simp only [typeOneCandidates,mem_biUnion,mem_image] at ht ⊢
  obtain ⟨p,hp,e,he,ht⟩ := ht
  exact ⟨p,intersectingEdgePairs_mono h i j hp,e,tripleExtensions_mono h _ he,ht⟩

theorem pairCompletion_mono {H K : Hypergraph V} (h : H ⊆ K) (e P Q : Finset V) :
    pairCompletion H e P Q ⊆ pairCompletion K e P Q := by
  intro t ht
  simp only [pairCompletion,mem_biUnion,mem_image] at ht ⊢
  obtain ⟨f,hf,c,hc,g,hg,ht⟩ := ht
  exact ⟨f,containingEdges_mono h 4 P hf,c,hc,g,containingEdges_mono h 4 _ hg,ht⟩

theorem pairGenerated_mono {H K : Hypergraph V} (h : H ⊆ K) (e : Finset V) :
    pairGenerated H e ⊆ pairGenerated K e := by
  intro t ht
  simp only [pairGenerated,mem_biUnion] at ht ⊢
  obtain ⟨P,hP,Q,hQ,ht⟩ := ht
  exact ⟨P,hP,Q,hQ,pairCompletion_mono h e P Q ht⟩

theorem pairGeneratedTriples_mono {H K : Hypergraph V} (h : H ⊆ K) (j : ℕ) :
    pairGeneratedTriples H j ⊆ pairGeneratedTriples K j := by
  intro t ht
  simp only [pairGeneratedTriples,mem_biUnion,mem_image] at ht ⊢
  obtain ⟨e,he,p,hp,ht⟩ := ht
  exact ⟨e,containingEdges_mono h j ∅ he,p,pairGenerated_mono h e hp,ht⟩

theorem remainingTriangleUnions_mono {H K : Hypergraph V} (h : H ⊆ K) :
    remainingTriangleUnions H ⊆ remainingTriangleUnions K := by
  intro e he
  simp only [remainingTriangleUnions,mem_union,mem_biUnion] at he ⊢
  rcases he with ⟨i,hi,j,hj,he⟩ | ⟨j,hj,he⟩
  · exact Or.inl ⟨i,hi,j,hj,configurationUnions_mono (typeOneCandidates_mono h i j) _ _ he⟩
  · exact Or.inr ⟨j,hj,configurationUnions_mono (pairGeneratedTriples_mono h j) _ _ he⟩

theorem induced_antichain {H : Hypergraph V} (hH : Antichain H) (U : Finset V) :
    Antichain (induced H U) := by
  intro e he f hf hef
  exact hH e (mem_filter.mp he).1 f (mem_filter.mp hf).1 hef

end KMV
