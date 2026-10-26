module
public import KMV.PairConfigurations
public section
namespace KMV
open Finset FiniteLaw
variable {V : Type*} [DecidableEq V]
open scoped Classical

@[expose] noncomputable def configurationUnions {α : Type*} [DecidableEq α]
    (C : Finset α) (U : α → Finset V) (k : ℕ) : Hypergraph V :=
  (C.filter (fun c => (U c).card=k)).image U

theorem configurationUnions_card {α : Type*} [DecidableEq α]
    (C : Finset α) (U : α → Finset V) (k : ℕ) : (configurationUnions C U k).card ≤ C.card :=
  card_image_le.trans (card_le_card (filter_subset _ _))

theorem configurationUnions_size {α : Type*} [DecidableEq α]
    {C : Finset α} {U : α → Finset V} {k : ℕ} {e : Finset V}
    (he : e ∈ configurationUnions C U k) : e.card = k := by
  obtain ⟨c,hc,rfl⟩ := mem_image.mp he
  exact (mem_filter.mp hc).2

theorem configurationUnions_mem {α : Type*} [DecidableEq α]
    {C : Finset α} {U : α → Finset V} {k : ℕ} {c : α}
    (hc : c ∈ C) (hk : (U c).card=k) : U c ∈ configurationUnions C U k :=
  mem_image.mpr ⟨c,mem_filter.mpr ⟨hc,hk⟩,rfl⟩

theorem probability_nonneg {α : Type*} {d : FiniteLaw α} (hd : d.Valid) (P : α → Prop) :
    0 ≤ d.probability P := by
  unfold FiniteLaw.probability
  apply FiniteLaw.expect_nonneg hd (FiniteLaw.all_of_forall d ?_)
  intro x
  split_ifs <;> norm_num

theorem fixed_size_loss (d : FiniteLaw (Finset V)) {β : ℝ} (hβ : 0 ≤ β)
    (hprob : ∀ S : Finset V, d.probability (fun I => S ⊆ I) ≤ β^S.card)
    {B : Hypergraph V} {k N : ℕ} (hsize : ∀ e ∈ B, e.card=k) (hN : B.card ≤ N) :
    d.expect (fun I => ((B.filter (fun e => e ⊆ I)).card : ℝ)) ≤ (N : ℝ)*β^k := by
  rw [expect_forbidden_count]
  calc
    _ ≤ ∑ _e ∈ B, β^k := sum_le_sum (fun e he => by simpa [hsize e he] using hprob e)
    _ = (B.card : ℝ)*β^k := by simp
    _ ≤ (N : ℝ)*β^k := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hN) (pow_nonneg hβ k)

theorem configuration_loss {α : Type*} [DecidableEq α]
    (d : FiniteLaw (Finset V)) {β : ℝ} (hβ : 0 ≤ β)
    (hprob : ∀ S : Finset V, d.probability (fun I => S ⊆ I) ≤ β^S.card)
    (C : Finset α) (U : α → Finset V) (k : ℕ) {N : ℕ} (hN : C.card ≤ N) :
    d.expect (fun I => (((configurationUnions C U k).filter (fun e => e ⊆ I)).card : ℝ)) ≤
      (N : ℝ)*β^k :=
  fixed_size_loss d hβ hprob (fun _ he => configurationUnions_size he)
    ((configurationUnions_card C U k).trans hN)

/-- Exact finite loss bound for type (i), before analytic substitution. -/
theorem typeOne_loss [Fintype V] (d : FiniteLaw (Finset V)) {β : ℝ} (hβ : 0 ≤ β)
    (hprob : ∀ S : Finset V, d.probability (fun I => S ⊆ I) ≤ β^S.card)
    {H : Hypergraph V} {B i j Di Dj : ℕ} (hi4 : i ≤ 4) (hj4 : j ≤ 4)
    (hB : ∀ X : Finset V, X.card = 3 → codegree H 4 X ≤ B)
    (hi : ∀ v, sizeDegree H i v ≤ Di) (hj : ∀ v, sizeDegree H j v ≤ Dj) :
    d.expect (fun I => (((configurationUnions (typeOneCandidates H i j)
      (fun p => p.2 ∪ p.1.1 ∪ p.1.2) (i+j)).filter (fun e => e ⊆ I)).card : ℝ)) ≤
      (256*B*(Fintype.card V)*Di*Dj : ℕ)*β^(i+j) :=
  configuration_loss d hβ hprob _ _ _ (typeOneCandidates_card hi4 hj4 hB hi hj)

/-- Exact finite loss bound for types (ii) and (iii). -/
theorem pairGenerated_loss (d : FiniteLaw (Finset V)) {β : ℝ} (hβ : 0 ≤ β)
    (hprob : ∀ S : Finset V, d.probability (fun I => S ⊆ I) ≤ β^S.card)
    {H : Hypergraph V} {M B j : ℕ} (hj : j ≤ 4)
    (hM : ∀ P : Finset V, P.card = 2 → codegree H 4 P ≤ M)
    (hB : ∀ X : Finset V, X.card = 3 → codegree H 4 X ≤ B) :
    d.expect (fun I => (((configurationUnions (pairGeneratedTriples H j)
      (fun p => p.1 ∪ p.2.1 ∪ p.2.2) (j+3)).filter (fun e => e ⊆ I)).card : ℝ)) ≤
      (codegree H j ∅*(1024*M*B) : ℕ)*β^(j+3) :=
  configuration_loss d hβ hprob _ _ _ (pairGeneratedTriples_card hj hM hB)

end KMV
