module
public import KMV.Cleaning
public section
namespace KMV
open Finset FiniteLaw
variable {V : Type*} [DecidableEq V] [Fintype V]
open scoped Classical

@[expose] noncomputable def expectedPresent (d : FiniteLaw (Finset V)) (B : Hypergraph V) : ℝ :=
  d.expect (fun I => ((B.filter (fun e => e ⊆ I)).card : ℝ))

theorem expectedPresent_union_le {d : FiniteLaw (Finset V)} (hd : d.Valid) (B C : Hypergraph V) :
    expectedPresent d (B ∪ C) ≤ expectedPresent d B + expectedPresent d C := by
  rw [expectedPresent,expectedPresent,expectedPresent, ← FiniteLaw.expect_add]
  apply FiniteLaw.expect_mono hd (FiniteLaw.all_of_forall d ?_)
  intro I
  rw [Finset.filter_union]
  exact_mod_cast Finset.card_union_le (B.filter (fun e => e ⊆ I)) (C.filter (fun e => e ⊆ I))

theorem expectedPresent_biUnion_le {α : Type*} [DecidableEq α] {d : FiniteLaw (Finset V)}
    (hd : d.Valid) (S : Finset α) (F : α → Hypergraph V) :
    expectedPresent d (S.biUnion F) ≤ ∑ x ∈ S, expectedPresent d (F x) := by
  induction S using Finset.induction_on with
  | empty => simp [expectedPresent,FiniteLaw.expect_const]
  | @insert x S hx ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert hx]
    exact (expectedPresent_union_le hd _ _).trans (add_le_add (le_refl _) ih)

theorem expected_size_edges {d : FiniteLaw (Finset V)} {H : Hypergraph V} {p : ℝ}
    (hprob : ∀ e ∈ H, d.probability (fun I => e ⊆ I) ≤ p^e.card) (j : ℕ) :
    expectedPresent d (containingEdges H j ∅) ≤ (codegree H j ∅ : ℝ)*p^j := by
  rw [expectedPresent,expect_forbidden_count]
  calc
    _ ≤ ∑ _e ∈ containingEdges H j ∅, p^j := by
      apply sum_le_sum
      intro e he
      have hm := mem_filter.mp he
      simpa only [hm.2.1] using hprob e hm.1
    _ = (codegree H j ∅ : ℝ)*p^j := by simp [codegree]

theorem highRank_loss {d : FiniteLaw (Finset V)} (hd : d.Valid) {H : Hypergraph V} {r : ℕ}
    (hr : RankBounds H r) {p : ℝ}
    (hprob : ∀ e ∈ H, d.probability (fun I => e ⊆ I) ≤ p^e.card) :
    expectedPresent d (highRankEdges H) ≤
      ∑ j ∈ Finset.Icc 5 r, (codegree H j ∅ : ℝ)*p^j := by
  have heq : highRankEdges H = (Finset.Icc 5 r).biUnion (fun j => containingEdges H j ∅) := by
    ext e
    simp only [highRankEdges,containingEdges,mem_filter,mem_biUnion,mem_Icc,empty_subset,and_true]
    constructor
    · rintro ⟨he,hc⟩
      exact ⟨e.card,⟨hc,(hr e he).2⟩,he,rfl⟩
    · rintro ⟨j,⟨hj,_⟩,he,hc⟩
      exact ⟨he,by omega⟩
  rw [heq]
  exact (expectedPresent_biUnion_le hd _ _).trans (sum_le_sum (fun j _ => expected_size_edges hprob j))

@[expose] noncomputable def configurationCost (H : Hypergraph V) (r : ℕ)
    (Δ M : ℕ → ℕ) (B : ℕ) (p β : ℝ) : ℝ :=
  (∑ i ∈ ({3,4} : Finset ℕ), ∑ j ∈ ({3,4} : Finset ℕ),
    ((i.choose 2 * codegree H i ∅ * M j : ℕ) : ℝ)*p^(i+j-2)) +
  ((4*codegree H 4 ∅*B : ℕ) : ℝ)*β^5 +
  ((∑ i ∈ ({3,4} : Finset ℕ), ∑ j ∈ ({3,4} : Finset ℕ),
    ((256*B*(Fintype.card V)*Δ i*Δ j : ℕ) : ℝ)*β^(i+j)) +
   (∑ j ∈ ({3,4} : Finset ℕ), ((codegree H j ∅*(1024*M 4*B) : ℕ) : ℝ)*β^(j+3))) +
  (∑ j ∈ Finset.Icc 5 r, (codegree H j ∅ : ℝ)*p^j)

theorem forbidden_loss {d : FiniteLaw (Finset V)} (hd : d.Valid)
    {H : Hypergraph V} {G : V → V → Prop} {r B : ℕ} {Δ M : ℕ → ℕ} {p β : ℝ}
    (hr : RankBounds H r) (hp : 0 ≤ p) (hβ : 0 ≤ β)
    (hdegree : ∀ j ∈ ({3,4} : Finset ℕ), ∀ v, sizeDegree H j v ≤ Δ j)
    (hpair : ∀ j ∈ ({3,4} : Finset ℕ), ∀ P : Finset V, P.card=2 → codegree H j P ≤ M j)
    (htr : ∀ X : Finset V, X.card=3 → codegree H 4 X ≤ B)
    (hsep : ∀ S, Separated G S → d.probability (fun I => S ⊆ I) ≤ p^S.card)
    (hcap : ∀ S : Finset V, d.probability (fun I => S ⊆ I) ≤ β^S.card)
    (hedge : ∀ e ∈ H, d.probability (fun I => e ⊆ I) ≤ p^e.card) :
    expectedPresent d (forbiddenUnions H G) ≤ configurationCost H r Δ M B p β := by
  have hsl : expectedPresent d (separatedUnions H G) ≤
      ∑ i ∈ ({3,4} : Finset ℕ), ∑ j ∈ ({3,4} : Finset ℕ),
        ((i.choose 2 * codegree H i ∅ * M j : ℕ) : ℝ)*p^(i+j-2) := by
    apply (expectedPresent_biUnion_le hd _ _).trans
    apply sum_le_sum
    intro i hi
    apply (expectedPresent_biUnion_le hd _ _).trans
    exact sum_le_sum (fun j hj => separatedPairUnions_loss d hp hsep (hpair j hj))
  have hfl := four_pair_three_loss d hβ hcap htr
  have hrl : expectedPresent d (remainingTriangleUnions H) ≤
      (∑ i ∈ ({3,4} : Finset ℕ), ∑ j ∈ ({3,4} : Finset ℕ),
        ((256*B*(Fintype.card V)*Δ i*Δ j : ℕ) : ℝ)*β^(i+j)) +
      (∑ j ∈ ({3,4} : Finset ℕ), ((codegree H j ∅*(1024*M 4*B) : ℕ) : ℝ)*β^(j+3)) := by
    apply (expectedPresent_union_le hd _ _).trans
    apply add_le_add
    · apply (expectedPresent_biUnion_le hd _ _).trans
      apply sum_le_sum
      intro i hi
      apply (expectedPresent_biUnion_le hd _ _).trans
      apply sum_le_sum
      intro j hj
      have hi4 : i ≤ 4 := by simp only [mem_insert,mem_singleton] at hi; omega
      have hj4 : j ≤ 4 := by simp only [mem_insert,mem_singleton] at hj; omega
      exact typeOne_loss d hβ hcap hi4 hj4 htr (hdegree i hi) (hdegree j hj)
    · apply (expectedPresent_biUnion_le hd _ _).trans
      apply sum_le_sum
      intro j hj
      have hj4 : j ≤ 4 := by simp only [mem_insert,mem_singleton] at hj; omega
      exact pairGenerated_loss d hβ hcap hj4 (hpair 4 (by simp)) htr
  have hhl := highRank_loss hd hr hedge
  have hu₁ := expectedPresent_union_le hd (separatedUnions H G) (fourTripleUnions H)
  have hu₂ := expectedPresent_union_le hd (separatedUnions H G ∪ fourTripleUnions H) (remainingTriangleUnions H)
  have hu₃ := expectedPresent_union_le hd
    ((separatedUnions H G ∪ fourTripleUnions H) ∪ remainingTriangleUnions H) (highRankEdges H)
  change expectedPresent d (fourTripleUnions H) ≤ _ at hfl
  change expectedPresent d (forbiddenUnions H G) ≤ _ at hu₃
  unfold configurationCost
  linarith

end KMV
