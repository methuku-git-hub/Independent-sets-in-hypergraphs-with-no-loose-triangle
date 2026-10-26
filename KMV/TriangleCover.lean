module
public import KMV.ConfigurationLoss
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V]
open scoped Classical
set_option maxHeartbeats 1000000

theorem triangle_cycle {e f g : Finset V} (h : Triangle e f g) : Triangle f g e :=
  ⟨h.2.1,h.2.2,h.1⟩

theorem triangle_swap {e f g : Finset V} (h : Triangle e f g) : Triangle f e g := by
  refine ⟨?_,?_,?_⟩
  · simpa only [inter_comm] using h.1
  · simpa only [inter_comm] using h.2.2
  · simpa only [inter_comm] using h.2.1

@[expose] noncomputable def oneUnions (H : Hypergraph V) (i j : ℕ) : Hypergraph V :=
  configurationUnions (typeOneCandidates H i j) (fun p => p.2 ∪ p.1.1 ∪ p.1.2) (i+j)

@[expose] noncomputable def pairUnions (H : Hypergraph V) (j : ℕ) : Hypergraph V :=
  configurationUnions (pairGeneratedTriples H j) (fun p => p.1 ∪ p.2.1 ∪ p.2.2) (j+3)

@[expose] noncomputable def remainingTriangleUnions (H : Hypergraph V) : Hypergraph V :=
  ({3,4} : Finset ℕ).biUnion (fun i => ({3,4} : Finset ℕ).biUnion (oneUnions H i)) ∪
    ({3,4} : Finset ℕ).biUnion (pairUnions H)

theorem one_union_mem {H : Hypergraph V} (hr : RankBounds H 4) {e f g : Finset V}
    (he : e ∈ H) (hf : f ∈ H) (hg : g ∈ H) (ht : Triangle e f g)
    (he4 : e.card = 4) (hef : (e ∩ f).card = 2) (heg : (e ∩ g).card = 1)
    (hfg : (f ∩ g).card = 1) (hz : (e ∩ f ∩ g).card = 0) :
    e ∪ f ∪ g ∈ remainingTriangleUnions H := by
  have hfc : f.card ∈ ({3,4} : Finset ℕ) := by have := hr f hf; simp only [mem_insert,mem_singleton]; omega
  have hgc : g.card ∈ ({3,4} : Finset ℕ) := by have := hr g hg; simp only [mem_insert,mem_singleton]; omega
  have hu := three_union_card e f g
  have hge : (g ∩ e).card = 1 := by simpa only [inter_comm] using heg
  have hsize : (e ∪ f ∪ g).card = f.card+g.card := by omega
  have hm := triangle_mem_typeOneCandidates he hf hg he4 rfl rfl hef heg hz ht
  have hm' : e ∪ f ∪ g ∈ oneUnions H f.card g.card :=
    configurationUnions_mem (C:=typeOneCandidates H f.card g.card)
      (U:=fun p => p.2 ∪ p.1.1 ∪ p.1.2) (c:=((f,g),e)) hm hsize
  simp only [remainingTriangleUnions,mem_union,mem_biUnion]
  exact Or.inl ⟨f.card,hfc,g.card,hgc,hm'⟩

theorem pair_union_mem {H : Hypergraph V} (hr : RankBounds H 4) {e f g : Finset V}
    (he : e ∈ H) (hf : f ∈ H) (hg : g ∈ H) (ht : Triangle e f g)
    (hf4 : f.card = 4) (hg4 : g.card = 4)
    (hef : (e ∩ f).card = 2) (heg : (e ∩ g).card = 2)
    (hsize : (e ∪ f ∪ g).card = e.card+3) : e ∪ f ∪ g ∈ remainingTriangleUnions H := by
  have hec : e.card ∈ ({3,4} : Finset ℕ) := by have := hr e he; simp only [mem_insert,mem_singleton]; omega
  have hm := triangle_mem_pairGenerated hf hg hf4 hg4 hef heg ht
  have hm' : (e,(f,g)) ∈ pairGeneratedTriples H e.card := by
    simp only [pairGeneratedTriples,mem_biUnion,mem_image]
    exact ⟨e,mem_filter.mpr ⟨he,rfl,empty_subset _⟩,(f,g),hm,rfl⟩
  have hU : e ∪ f ∪ g ∈ pairUnions H e.card :=
    configurationUnions_mem (C:=pairGeneratedTriples H e.card)
      (U:=fun p => p.1 ∪ p.2.1 ∪ p.2.2) (c:=(e,(f,g))) hm' hsize
  simp only [remainingTriangleUnions,mem_union,mem_biUnion]
  exact Or.inr ⟨e.card,hec,hU⟩

set_option maxHeartbeats 1000000 in
/-- Assemble the classification into one finite family of forbidden unions.
Candidate families are filtered by union size before their probability bounds
are used. No permutation or orientation is assumed without proof. -/
theorem triangle_union_covered {H : Hypergraph V} {G : V → V → Prop}
    (hr : RankBounds H 4) (ha : Antichain H) (hl : LooseTriangleFree H)
    (hs : ∀ e ∈ H, Separated G e)
    (hbad₂ : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card = 2 → ¬ Separated G (e ∪ f))
    (hbad₃ : ∀ e ∈ H, ∀ f ∈ H, e.card = 4 → f.card = 4 → (e ∩ f).card ≠ 3)
    {e f g : Finset V} (he : e ∈ H) (hf : f ∈ H) (hg : g ∈ H) (ht : Triangle e f g) :
    e ∪ f ∪ g ∈ remainingTriangleUnions H := by
  have hc := (triangle_classification hr ha hl hs hbad₂ hbad₃ he hf hg ht).1
  have hu := three_union_card e f g
  have ht₁ := triangle_cycle ht
  have ht₂ := triangle_cycle ht₁
  have hh₁ : f ∩ g ∩ e = e ∩ f ∩ g := by ext x; simp only [mem_inter]; tauto
  have hh₂ : g ∩ e ∩ f = e ∩ f ∩ g := by ext x; simp only [mem_inter]; tauto
  have hcfe : (f ∩ e).card = (e ∩ f).card := by rw [inter_comm]
  have hceg : (e ∩ g).card = (g ∩ e).card := by rw [inter_comm]
  have hcgf : (g ∩ f).card = (f ∩ g).card := by rw [inter_comm]
  rcases hc with ⟨hz,hpat⟩ | ⟨hz,he4,hf4,hg4,hpat⟩ | ⟨hz,hef,hfg,hge,hlarge⟩
  · rcases hpat with ⟨hef,hfg,hge,he4 | hf4⟩ | ⟨hfg,hge,hef,hf4 | hg4⟩ | ⟨hge,hef,hfg,hg4 | he4⟩
    · exact one_union_mem hr he hf hg ht he4 hef (hceg.trans hge) hfg hz
    · have hh := one_union_mem hr hf he hg (triangle_swap ht) hf4 (hcfe.trans hef) hfg
        (hceg.trans hge) (by simpa only [inter_comm f e] using hz)
      simpa only [union_assoc,union_comm,union_left_comm] using hh
    · have hh := one_union_mem hr hf hg he ht₁ hf4 hfg (hcfe.trans hef) hge (by simpa only [hh₁] using hz)
      simpa only [union_assoc,union_comm,union_left_comm] using hh
    · have hh := one_union_mem hr hg hf he (triangle_swap ht₁) hg4 (hcgf.trans hfg) hge
        (hcfe.trans hef) (by simpa only [inter_comm g f,hh₁] using hz)
      simpa only [union_assoc,union_comm,union_left_comm] using hh
    · have hh := one_union_mem hr hg he hf ht₂ hg4 hge (hcgf.trans hfg) hef (by simpa only [hh₂] using hz)
      simpa only [union_assoc,union_comm,union_left_comm] using hh
    · have hh := one_union_mem hr he hg hf (triangle_swap ht₂) he4 (hceg.trans hge) hef
        (hcgf.trans hfg) (by simpa only [inter_comm e g,hh₂] using hz)
      simpa only [union_assoc,union_comm,union_left_comm] using hh
  · have hd := triangle_edges_distinct ht
    have hb₁ := intersection_le_two ha hr he hf hd.1 (hbad₃ e he f hf)
    have hb₂ := intersection_le_two ha hr hf hg hd.2.1 (hbad₃ f hf g hg)
    have hb₃ := intersection_le_two ha hr hg he hd.2.2 (hbad₃ g hg e he)
    by_cases hef : (e ∩ f).card = 1
    · have hge : (g ∩ e).card = 2 := by omega
      have hgf : (g ∩ f).card = 2 := by omega
      have hh := pair_union_mem hr hg he hf ht₂ he4 hf4 hge hgf
        (show (g ∪ e ∪ f).card=g.card+3 by
          have heq : g ∪ e ∪ f = e ∪ f ∪ g := by ac_rfl
          rw [heq]; omega)
      simpa only [union_assoc,union_comm,union_left_comm] using hh
    · by_cases hfg : (f ∩ g).card = 1
      · exact pair_union_mem hr he hf hg ht hf4 hg4 (by omega) (by omega) (by omega)
      · have hh := pair_union_mem hr hf hg he ht₁ hg4 he4 (by omega) (by omega)
          (show (f ∪ g ∪ e).card=f.card+3 by
            have heq : f ∪ g ∪ e = e ∪ f ∪ g := by ac_rfl
            rw [heq]; omega)
        simpa only [union_assoc,union_comm,union_left_comm] using hh
  · have hr₁ := hr e he
    have hr₂ := hr f hf
    have hr₃ := hr g hg
    by_cases hf4 : f.card = 4
    · by_cases hg4 : g.card = 4
      · exact pair_union_mem hr he hf hg ht hf4 hg4 hef (hceg.trans hge) (by omega)
      · have he4 : e.card = 4 := by omega
        have hh := pair_union_mem hr hg he hf ht₂ he4 hf4 hge (hcgf.trans hfg)
          (show (g ∪ e ∪ f).card=g.card+3 by
            have heq : g ∪ e ∪ f = e ∪ f ∪ g := by ac_rfl
            rw [heq]; omega)
        simpa only [union_assoc,union_comm,union_left_comm] using hh
    · have he4 : e.card = 4 := by omega
      have hg4 : g.card = 4 := by omega
      have hh := pair_union_mem hr hf hg he ht₁ hg4 he4 hfg (hcfe.trans hef)
        (show (f ∪ g ∪ e).card=f.card+3 by
          have heq : f ∪ g ∪ e = e ∪ f ∪ g := by ac_rfl
          rw [heq]; omega)
      simpa only [union_assoc,union_comm,union_left_comm] using hh

end KMV
