module
public import KMV.DensityStars
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V]
open scoped Classical

@[expose] noncomputable def lightStar (H : Hypergraph V) (r : ℕ) (v : V) : Hypergraph V :=
  H.filter (fun e => e.card = 3 ∧ v ∈ e ∧ ∀ x ∈ e, x ≠ v → ¬ Expandable H r {v,x})

theorem lightStar_bound {H : Hypergraph V} {r : ℕ}
    (hH : RankBounds H r) (hfree : LooseTriangleFree H) (v : V) :
    ∃ I : Finset V, Independent H I ∧ (lightStar H r v).card ≤ 4*r*I.card := by
  classical
  let L := lightStar H r v
  let K := L.image (fun e => e.erase v)
  have hL : ∀ e ∈ L, e ∈ H ∧ e.card = 3 ∧ v ∈ e ∧
      ∀ x ∈ e, x ≠ v → ¬ Expandable H r {v,x} := by
    intro e he; exact mem_filter.mp he
  have hK : ∀ e ∈ K, e.card = 2 ∧ v ∉ e ∧ insert v e ∈ H := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    have hf' := hL f hf
    refine ⟨?_,notMem_erase _ _,?_⟩
    · rw [card_erase_of_mem hf'.2.2.1,hf'.2.1]
    · simpa [insert_erase hf'.2.2.1] using hf'.1
  have hc : K.card = L.card := by
    apply card_image_of_injOn
    intro e he f hf hef
    have heq := congrArg (insert v) hef
    simpa [insert_erase (hL e he).2.2.1, insert_erase (hL f hf).2.2.1] using heq
  have hdeg : ∀ x, (K.filter (fun e => x ∈ e)).card ≤ 2*r := by
    intro x
    by_cases hz : K.filter (fun e => x ∈ e) = ∅
    · simp [hz]
    obtain ⟨e,he⟩ := nonempty_iff_ne_empty.mpr hz
    obtain ⟨heK,hxe⟩ := mem_filter.mp he
    obtain ⟨f,hf,hef⟩ := mem_image.mp heK
    have hxf : x ∈ f := mem_of_mem_erase (hef.symm ▸ hxe)
    have hxv : x ≠ v := (mem_erase.mp (hef.symm ▸ hxe)).1
    have hlight := (hL f hf).2.2.2 x hxf hxv
    have hsub : K.filter (fun e => x ∈ e) ⊆
        (containingEdges H 3 {v,x}).image (fun e => e.erase v) := by
      intro a ha
      obtain ⟨haK,hxa⟩ := mem_filter.mp ha
      obtain ⟨b,hb,rfl⟩ := mem_image.mp haK
      refine mem_image.mpr ⟨b,mem_filter.mpr ⟨(hL b hb).1,(hL b hb).2.1,?_⟩,rfl⟩
      exact insert_subset_iff.mpr ⟨(hL b hb).2.2.1,
        singleton_subset_iff.mpr (mem_of_mem_erase hxa)⟩
    exact ((card_le_card hsub).trans card_image_le).trans
      (nonexpandable_pair_triples (by simp [hxv.symm]) hlight)
  obtain ⟨M,hMK,hm,hbound⟩ := exists_large_matching
    (fun e he => ⟨card_pos.mp (by rw [(hK e he).1]; decide),(hK e he).1.le⟩) hdeg
  obtain ⟨I,hI,hIc⟩ := star_matching_independent hH hfree v hm (fun e he =>
    ⟨card_pos.mp (by rw [(hK e (hMK he)).1]; decide),(hK e (hMK he)).2⟩)
  refine ⟨I,hI,?_⟩
  rw [hc] at hbound
  rw [hIc]
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hbound

@[expose] noncomputable def singleLightVertices [Fintype V]
    (H : Hypergraph V) (r : ℕ) (v : V) : Finset V :=
  Finset.univ.filter (fun x => x ≠ v ∧ ¬ Expandable H r {v,x} ∧
    ∃ a, a ≠ v ∧ a ≠ x ∧ {v,x,a} ∈ H ∧ Expandable H r {v,a} ∧ Expandable H r {x,a})

theorem singleLightVertices_independent [Fintype V] {H : Hypergraph V} {r : ℕ}
    (hH : RankBounds H r) (hfree : LooseTriangleFree H) (v : V) :
    Independent H (singleLightVertices H r v) := by
  apply unique_light_star_independent hH hfree (v:=v)
  · simp [singleLightVertices]
  · intro x hx
    obtain ⟨hxv,hlight,a,hav,hax,he,hva,hxa⟩ := (mem_filter.mp hx).2
    refine ⟨a,hav,?_,he,hxa⟩
    intro ha
    exact (mem_filter.mp ha).2.2.1 hva

theorem singleLightCover_bound [Fintype V] (H : Hypergraph V) (r : ℕ) (v : V) :
    ((singleLightVertices H r v).biUnion (fun x => containingEdges H 3 {v,x})).card ≤
      2*r*(singleLightVertices H r v).card := by
  calc
    _ ≤ ∑ x ∈ singleLightVertices H r v, (containingEdges H 3 {v,x}).card := card_biUnion_le
    _ ≤ ∑ _x ∈ singleLightVertices H r v, 2*r := by
      apply sum_le_sum
      intro x hx
      obtain ⟨hxv,hlight,_⟩ := (mem_filter.mp hx).2
      exact nonexpandable_pair_triples (by simp [hxv.symm]) hlight
    _ = 2*r*(singleLightVertices H r v).card := by simp [Nat.mul_comm]

end KMV
