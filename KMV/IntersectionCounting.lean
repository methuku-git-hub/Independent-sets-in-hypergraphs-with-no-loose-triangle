module
public import KMV.ConfigurationLoss
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V]
open scoped Classical

theorem sum_codegree_fixed_card (H : Hypergraph V) (j k : ℕ) :
    (∑ P ∈ Finset.univ.powersetCard k, codegree H j P) = j.choose k * codegree H j ∅ := by
  have hd : ∀ P, codegree H j P = ∑ e ∈ H, if e.card=j ∧ P⊆e then 1 else 0 := by
    intro P; simp [codegree,containingEdges, ← Finset.sum_filter]
  simp_rw [hd]
  rw [Finset.sum_comm]
  have he : ∀ e : Finset V,
      (∑ P ∈ Finset.univ.powersetCard k, if e.card=j ∧ P⊆e then 1 else 0) =
        if e.card=j then j.choose k else 0 := by
    intro e
    by_cases hc : e.card=j
    · simp only [hc,true_and,ite_true, ← Finset.sum_filter]
      have hf : (Finset.univ.powersetCard k).filter (fun P : Finset V => P⊆e) = e.powersetCard k := by
        ext P
        simp only [mem_filter,mem_powersetCard,subset_univ,true_and]
        tauto
      simp [hf,card_powersetCard,hc]
    · simp [hc]
  simp_rw [he]
  rw [← Finset.sum_filter]
  simp [codegree,containingEdges,Nat.mul_comm]

@[expose] noncomputable def intersectingAt (H : Hypergraph V) (i j k : ℕ) :
    Finset (Finset V × Finset V) :=
  ((containingEdges H i ∅).product (containingEdges H j ∅)).filter
    (fun p => k ≤ (p.1 ∩ p.2).card)

theorem intersectingAt_card {H : Hypergraph V} {i j k M : ℕ}
    (hM : ∀ P : Finset V, P.card=k → codegree H j P ≤ M) :
    (intersectingAt H i j k).card ≤ i.choose k * codegree H i ∅ * M := by
  let F := fun P => (containingEdges H i P).product (containingEdges H j P)
  have hsub : intersectingAt H i j k ⊆ (Finset.univ.powersetCard k).biUnion F := by
    intro p hp
    obtain ⟨hprod,hint⟩ := mem_filter.mp hp
    obtain ⟨he,hf⟩ := mem_product.mp hprod
    obtain ⟨P,hP,hPc⟩ := Finset.exists_subset_card_eq hint
    refine mem_biUnion.mpr ⟨P,mem_powersetCard.mpr ⟨subset_univ _,hPc⟩,?_⟩
    exact mem_product.mpr
      ⟨mem_filter.mpr ⟨(mem_filter.mp he).1,(mem_filter.mp he).2.1,hP.trans inter_subset_left⟩,
       mem_filter.mpr ⟨(mem_filter.mp hf).1,(mem_filter.mp hf).2.1,hP.trans inter_subset_right⟩⟩
  calc
    _ ≤ ((Finset.univ.powersetCard k).biUnion F).card := card_le_card hsub
    _ ≤ ∑ P ∈ Finset.univ.powersetCard k, (F P).card := card_biUnion_le
    _ ≤ ∑ P ∈ Finset.univ.powersetCard k, codegree H i P * M := by
      apply sum_le_sum
      intro P hP
      exact (card_product _ _).le.trans (Nat.mul_le_mul_left _ (hM P (mem_powersetCard.mp hP).2))
    _ = (∑ P ∈ Finset.univ.powersetCard k, codegree H i P)*M := by rw [Finset.sum_mul]
    _ = i.choose k * codegree H i ∅ * M := by rw [sum_codegree_fixed_card]

@[expose] noncomputable def separatedPairUnions (H : Hypergraph V) (G : V → V → Prop)
    (i j : ℕ) : Hypergraph V :=
  configurationUnions ((intersectingAt H i j 2).filter (fun p => Separated G (p.1 ∪ p.2)))
    (fun p => p.1 ∪ p.2) (i+j-2)

theorem separatedPairUnions_loss (d : FiniteLaw (Finset V)) {p : ℝ} (hp : 0 ≤ p)
    {H : Hypergraph V} {G : V → V → Prop} {i j M : ℕ}
    (hprob : ∀ S, Separated G S → d.probability (fun I => S ⊆ I) ≤ p^S.card)
    (hM : ∀ P : Finset V, P.card=2 → codegree H j P ≤ M) :
    d.expect (fun I => (((separatedPairUnions H G i j).filter (fun e => e ⊆ I)).card : ℝ)) ≤
      (i.choose 2 * codegree H i ∅ * M : ℕ)*p^(i+j-2) := by
  rw [expect_forbidden_count]
  have hb : (separatedPairUnions H G i j).card ≤ i.choose 2 * codegree H i ∅ * M :=
    (configurationUnions_card _ _ _).trans
      ((card_le_card (filter_subset _ _)).trans (intersectingAt_card hM))
  calc
    _ ≤ ∑ _e ∈ separatedPairUnions H G i j, p^(i+j-2) := by
      apply sum_le_sum
      intro e he
      have hs : Separated G e := by
        obtain ⟨a,ha,rfl⟩ := mem_image.mp he
        exact (mem_filter.mp (mem_filter.mp ha).1).2
      have hc := configurationUnions_size he
      simpa [hc] using hprob e hs
    _ = ((separatedPairUnions H G i j).card : ℝ)*p^(i+j-2) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hb) (pow_nonneg hp _)

theorem four_pair_three_loss (d : FiniteLaw (Finset V)) {β : ℝ} (hβ : 0 ≤ β)
    (hprob : ∀ S : Finset V, d.probability (fun I => S ⊆ I) ≤ β^S.card)
    {H : Hypergraph V} {B : ℕ}
    (hB : ∀ X : Finset V, X.card=3 → codegree H 4 X ≤ B) :
    d.expect (fun I => (((configurationUnions (intersectingAt H 4 4 3)
      (fun p => p.1 ∪ p.2) 5).filter (fun e => e ⊆ I)).card : ℝ)) ≤
      (4*codegree H 4 ∅*B : ℕ)*β^5 := by
  apply configuration_loss d hβ hprob
  simpa using (intersectingAt_card (i:=4) hB)

end KMV
