module
public import KMV.TriangleClassification
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V]
open scoped Classical

@[expose] noncomputable def intersectingEdgePairs (H : Hypergraph V) (i j : ℕ) :
    Finset (Finset V × Finset V) :=
  ((containingEdges H i ∅).product (containingEdges H j ∅)).filter
    (fun p => (p.1 ∩ p.2).Nonempty)

theorem intersectingEdgePairs_card [Fintype V] (H : Hypergraph V) (i j Di Dj : ℕ)
    (hi : ∀ v, sizeDegree H i v ≤ Di) (hj : ∀ v, sizeDegree H j v ≤ Dj) :
    (intersectingEdgePairs H i j).card ≤ Fintype.card V * Di * Dj := by
  let C := fun v => (H.filter (fun e => e.card=i ∧ v∈e)).product
    (H.filter (fun e => e.card=j ∧ v∈e))
  have hs : intersectingEdgePairs H i j ⊆ Finset.univ.biUnion C := by
    intro p hp
    obtain ⟨hprod,x,hx⟩ := mem_filter.mp hp
    obtain ⟨he,hf⟩ := mem_product.mp hprod
    obtain ⟨heH,hec,_⟩ := mem_filter.mp he
    obtain ⟨hfH,hfc,_⟩ := mem_filter.mp hf
    exact mem_biUnion.mpr ⟨x,mem_univ _,mem_product.mpr
      ⟨mem_filter.mpr ⟨heH,hec,(mem_inter.mp hx).1⟩,
       mem_filter.mpr ⟨hfH,hfc,(mem_inter.mp hx).2⟩⟩⟩
  calc
    _ ≤ (Finset.univ.biUnion C).card := card_le_card hs
    _ ≤ ∑ v : V, (C v).card := card_biUnion_le
    _ ≤ ∑ _v : V, Di*Dj := by
      apply sum_le_sum
      intro v _
      exact (card_product _ _).le.trans (Nat.mul_le_mul (hi v) (hj v))
    _ = Fintype.card V * Di * Dj := by simp [Nat.mul_assoc]

@[expose] noncomputable def tripleExtensions (H : Hypergraph V) (U : Finset V) : Hypergraph V :=
  H.filter (fun e => e.card = 4 ∧ 3 ≤ (e ∩ U).card)

theorem tripleExtensions_card {H : Hypergraph V} {B : ℕ}
    (hB : ∀ X : Finset V, X.card = 3 → codegree H 4 X ≤ B) (U : Finset V) :
    (tripleExtensions H U).card ≤ 2^U.card * B := by
  let T := U.powerset.filter (fun X => X.card=3)
  have hs : tripleExtensions H U ⊆ T.biUnion (containingEdges H 4) := by
    intro e he
    obtain ⟨heH,hec,hint⟩ := mem_filter.mp he
    obtain ⟨X,hXeU,hXc⟩ := Finset.exists_subset_card_eq hint
    have hXU : X ⊆ U := hXeU.trans inter_subset_right
    have hXe : X ⊆ e := hXeU.trans inter_subset_left
    refine mem_biUnion.mpr ⟨X,?_,mem_filter.mpr ⟨heH,hec,hXe⟩⟩
    exact mem_filter.mpr ⟨mem_powerset.mpr hXU,hXc⟩
  have hTc : T.card ≤ 2^U.card := by
    exact (card_le_card (filter_subset _ _)).trans (card_powerset U).le
  calc
    _ ≤ (T.biUnion (containingEdges H 4)).card := card_le_card hs
    _ ≤ ∑ X ∈ T, (containingEdges H 4 X).card := card_biUnion_le
    _ ≤ ∑ _X ∈ T, B := sum_le_sum (fun X hX => hB X (mem_filter.mp hX).2)
    _ = T.card*B := by simp
    _ ≤ 2^U.card*B := Nat.mul_le_mul_right B hTc

theorem tripleExtensions_card_eight {H : Hypergraph V} {B : ℕ}
    (hB : ∀ X : Finset V, X.card = 3 → codegree H 4 X ≤ B) {U : Finset V} (hU : U.card ≤ 8) :
    (tripleExtensions H U).card ≤ 256*B := by
  have hp : 2^U.card ≤ 2^8 := Nat.pow_le_pow_right (by decide) hU
  exact (tripleExtensions_card hB U).trans (Nat.mul_le_mul_right B (by norm_num at hp ⊢; exact hp))

@[expose] noncomputable def typeOneCandidates (H : Hypergraph V) (i j : ℕ) :
    Finset ((Finset V × Finset V) × Finset V) :=
  (intersectingEdgePairs H i j).biUnion (fun p =>
    (tripleExtensions H (p.1 ∪ p.2)).image (fun e => (p,e)))

/-- A uniform constant 256 replaces the sharper 24 in the manuscript;
the dependence on vertex degrees and B is unchanged. -/
theorem typeOneCandidates_card [Fintype V] {H : Hypergraph V} {B i j Di Dj : ℕ}
    (hi4 : i ≤ 4) (hj4 : j ≤ 4)
    (hB : ∀ X : Finset V, X.card = 3 → codegree H 4 X ≤ B)
    (hi : ∀ v, sizeDegree H i v ≤ Di) (hj : ∀ v, sizeDegree H j v ≤ Dj) :
    (typeOneCandidates H i j).card ≤ 256*B*(Fintype.card V)*Di*Dj := by
  have hext : ∀ p ∈ intersectingEdgePairs H i j,
      (tripleExtensions H (p.1 ∪ p.2)).card ≤ 256*B := by
    intro p hp
    obtain ⟨hprod,_⟩ := mem_filter.mp hp
    obtain ⟨he,hf⟩ := mem_product.mp hprod
    have hec := (mem_filter.mp he).2.1
    have hfc := (mem_filter.mp hf).2.1
    apply tripleExtensions_card_eight hB
    have hc := card_union_le p.1 p.2
    omega
  calc
    _ ≤ ∑ p ∈ intersectingEdgePairs H i j,
        ((tripleExtensions H (p.1 ∪ p.2)).image (fun e => (p,e))).card := card_biUnion_le
    _ ≤ ∑ _p ∈ intersectingEdgePairs H i j, 256*B :=
      sum_le_sum (fun p hp => card_image_le.trans (hext p hp))
    _ = (intersectingEdgePairs H i j).card*(256*B) := by simp
    _ ≤ (Fintype.card V * Di * Dj)*(256*B) :=
      Nat.mul_le_mul_right _ (intersectingEdgePairs_card H i j Di Dj hi hj)
    _ = 256*B*(Fintype.card V)*Di*Dj := by ring

end KMV
