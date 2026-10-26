module
public import KMV.ConfigurationCounting
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V]
open scoped Classical

theorem card_biUnion_le_mul {α β : Type*} [DecidableEq β] (S : Finset α)
    (F : α → Finset β) (K : ℕ) (h : ∀ x ∈ S, (F x).card ≤ K) :
    (S.biUnion F).card ≤ S.card*K := by
  calc
    _ ≤ ∑ x ∈ S, (F x).card := card_biUnion_le
    _ ≤ ∑ _x ∈ S, K := sum_le_sum h
    _ = S.card*K := by simp

@[expose] noncomputable def pairCompletion (H : Hypergraph V) (e P Q : Finset V) :
    Finset (Finset V × Finset V) :=
  (containingEdges H 4 P).biUnion (fun f => (f \ e).biUnion (fun c =>
    (containingEdges H 4 (insert c Q)).image (fun g => (f,g))))

theorem pairCompletion_card {H : Hypergraph V} {M B : ℕ}
    (hM : ∀ P : Finset V, P.card = 2 → codegree H 4 P ≤ M)
    (hB : ∀ X : Finset V, X.card = 3 → codegree H 4 X ≤ B)
    {e P Q : Finset V} (hP : P.card = 2) (hQ : Q.card = 2) (hQe : Q ⊆ e) :
    (pairCompletion H e P Q).card ≤ M*(4*B) := by
  have hc : ∀ f ∈ containingEdges H 4 P,
      ((f \ e).biUnion (fun c => (containingEdges H 4 (insert c Q)).image (fun g => (f,g)))).card ≤ 4*B := by
    intro f hf
    have hfc := (mem_filter.mp hf).2.1
    have hcard : (f \ e).card ≤ 4 := (card_le_card sdiff_subset).trans hfc.le
    apply (card_biUnion_le_mul _ _ B ?_).trans (Nat.mul_le_mul_right B hcard)
    intro c hc
    have hcQ : c ∉ Q := fun h => (mem_sdiff.mp hc).2 (hQe h)
    have hc3 : (insert c Q).card = 3 := by simp [hcQ,hQ]
    exact card_image_le.trans (hB _ hc3)
  exact (card_biUnion_le_mul _ _ (4*B) hc).trans (Nat.mul_le_mul_right _ (hM P hP))

@[expose] noncomputable def pairGenerated (H : Hypergraph V) (e : Finset V) :
    Finset (Finset V × Finset V) :=
  (e.powerset.filter (fun P => P.card=2)).biUnion (fun P =>
    (e.powerset.filter (fun Q => Q.card=2)).biUnion (fun Q => pairCompletion H e P Q))

theorem pairGenerated_card {H : Hypergraph V} {M B : ℕ}
    (hM : ∀ P : Finset V, P.card = 2 → codegree H 4 P ≤ M)
    (hB : ∀ X : Finset V, X.card = 3 → codegree H 4 X ≤ B)
    {e : Finset V} (he : e.card ≤ 4) : (pairGenerated H e).card ≤ 1024*M*B := by
  have hpow : (e.powerset.filter (fun P => P.card=2)).card ≤ 16 := by
    have hp : 2^e.card ≤ 2^4 := Nat.pow_le_pow_right (by decide) he
    have hc := (card_le_card (filter_subset (fun P : Finset V => P.card=2) e.powerset)).trans
      (card_powerset e).le
    norm_num at hp
    exact hc.trans hp
  apply (card_biUnion_le_mul _ _ (16*(M*(4*B))) ?_).trans ?_
  · intro P hP
    apply (card_biUnion_le_mul _ _ (M*(4*B)) ?_).trans (Nat.mul_le_mul_right _ hpow)
    intro Q hQ
    exact pairCompletion_card hM hB (mem_filter.mp hP).2 (mem_filter.mp hQ).2
      (mem_powerset.mp (mem_filter.mp hQ).1)
  · calc
      _ ≤ 16*(16*(M*(4*B))) := Nat.mul_le_mul_right _ hpow
      _ = 1024*M*B := by ring

@[expose] noncomputable def pairGeneratedTriples (H : Hypergraph V) (j : ℕ) :
    Finset (Finset V × (Finset V × Finset V)) :=
  (containingEdges H j ∅).biUnion (fun e => (pairGenerated H e).image (fun p => (e,p)))

theorem pairGeneratedTriples_card {H : Hypergraph V} {M B j : ℕ} (hj : j ≤ 4)
    (hM : ∀ P : Finset V, P.card = 2 → codegree H 4 P ≤ M)
    (hB : ∀ X : Finset V, X.card = 3 → codegree H 4 X ≤ B) :
    (pairGeneratedTriples H j).card ≤ codegree H j ∅*(1024*M*B) := by
  apply card_biUnion_le_mul
  intro e he
  exact card_image_le.trans (pairGenerated_card hM hB ((mem_filter.mp he).2.1.le.trans hj))

/-- Both types (ii) and (iii) fit this construction after selecting their
base edge. The triangle witness supplies c outside the base edge. -/
theorem triangle_mem_pairGenerated {H : Hypergraph V} {e f g : Finset V}
    (hf : f ∈ H) (hg : g ∈ H) (hf4 : f.card = 4) (hg4 : g.card = 4)
    (hef : (e ∩ f).card = 2) (heg : (e ∩ g).card = 2) (ht : Triangle e f g) :
    (f,g) ∈ pairGenerated H e := by
  obtain ⟨c,hc⟩ := ht.2.1
  obtain ⟨hcfg,hce⟩ := mem_sdiff.mp hc
  obtain ⟨hcf,hcg⟩ := mem_inter.mp hcfg
  apply mem_biUnion.mpr
  refine ⟨e ∩ f,mem_filter.mpr ⟨mem_powerset.mpr inter_subset_left,hef⟩,?_⟩
  apply mem_biUnion.mpr
  refine ⟨e ∩ g,mem_filter.mpr ⟨mem_powerset.mpr inter_subset_left,heg⟩,?_⟩
  apply mem_biUnion.mpr
  refine ⟨f,mem_filter.mpr ⟨hf,hf4,inter_subset_right⟩,?_⟩
  apply mem_biUnion.mpr
  refine ⟨c,mem_sdiff.mpr ⟨hcf,hce⟩,?_⟩
  exact mem_image.mpr ⟨g,mem_filter.mpr ⟨hg,hg4,insert_subset_iff.mpr ⟨hcg,inter_subset_right⟩⟩,rfl⟩

theorem triangle_mem_typeOneCandidates {H : Hypergraph V} {e f g : Finset V} {i j : ℕ}
    (he : e ∈ H) (hf : f ∈ H) (hg : g ∈ H)
    (he4 : e.card = 4) (hfi : f.card = i) (hgj : g.card = j)
    (hef : (e ∩ f).card = 2) (heg : (e ∩ g).card = 1)
    (hzero : (e ∩ f ∩ g).card = 0) (ht : Triangle e f g) :
    ((f,g),e) ∈ typeOneCandidates H i j := by
  have hfg : (f ∩ g).Nonempty :=
    let ⟨x,hx⟩ := ht.2.1; ⟨x,(mem_sdiff.mp hx).1⟩
  have hp : (f,g) ∈ intersectingEdgePairs H i j :=
    mem_filter.mpr ⟨mem_product.mpr ⟨mem_filter.mpr ⟨hf,hfi,empty_subset _⟩,
      mem_filter.mpr ⟨hg,hgj,empty_subset _⟩⟩,hfg⟩
  have hi : (e ∩ (f ∪ g)).card = 3 := by
    have hh := shared_card_identity e f g
    have heq : e ∩ (f ∪ g) = (e ∩ f) ∪ (e ∩ g) := by
      ext x; simp only [mem_inter,mem_union]; tauto
    rw [heq]
    omega
  exact mem_biUnion.mpr ⟨(f,g),hp,mem_image.mpr ⟨e,mem_filter.mpr ⟨he,he4,hi.ge⟩,rfl⟩⟩

end KMV
