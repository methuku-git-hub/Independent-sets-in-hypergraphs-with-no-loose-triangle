module
public import KMV.TriangleCleaning
public import Mathlib.Tactic.IntervalCases
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V]

theorem intersection_lt_of_antichain {H : Hypergraph V} (hH : Antichain H)
    {e f : Finset V} (he : e ∈ H) (hf : f ∈ H) (hne : e ≠ f) :
    (e ∩ f).card < e.card := by
  by_contra hn
  have heq := eq_of_subset_of_card_le (inter_subset_left : e ∩ f ⊆ e) (le_of_not_gt hn)
  have hsub : e ⊆ f := by rw [← heq]; exact inter_subset_right
  exact hne (hH e he f hf hsub)

theorem intersection_le_two {H : Hypergraph V} (hH : Antichain H)
    (hr : RankBounds H 4) {e f : Finset V} (he : e ∈ H) (hf : f ∈ H) (hne : e ≠ f)
    (hbad : e.card = 4 → f.card = 4 → (e ∩ f).card ≠ 3) : (e ∩ f).card ≤ 2 := by
  have h₁ := intersection_lt_of_antichain hH he hf hne
  have h₂ := intersection_lt_of_antichain hH hf he hne.symm
  rw [inter_comm f e] at h₂
  have hec := hr e he
  have hfc := hr f hf
  by_contra hn
  have hi : (e ∩ f).card = 3 := by omega
  exact hbad (by omega) (by omega) hi

theorem shared_card_identity (e f g : Finset V) :
    ((e ∩ f) ∪ (e ∩ g)).card + (e ∩ f ∩ g).card = (e ∩ f).card + (e ∩ g).card := by
  have he : (e ∩ f) ∩ (e ∩ g) = e ∩ f ∩ g := by ext x; simp only [mem_inter]; tauto
  simpa only [he] using Finset.card_union_add_card_inter (e ∩ f) (e ∩ g)

theorem shared_card_le (e f g : Finset V) :
    (e ∩ f).card + (e ∩ g).card ≤ e.card + (e ∩ f ∩ g).card := by
  have hs : (e ∩ f) ∪ (e ∩ g) ⊆ e :=
    union_subset inter_subset_left inter_subset_left
  have hc := card_le_card hs
  have hi := shared_card_identity e f g
  omega

theorem cross_covered_of_shared_card {e f g : Finset V}
    (hc : e.card + (e ∩ f ∩ g).card = (e ∩ f).card + (e ∩ g).card) : e \ f ⊆ g := by
  have hs : (e ∩ f) ∪ (e ∩ g) ⊆ e := union_subset inter_subset_left inter_subset_left
  have hi := shared_card_identity e f g
  have heq := eq_of_subset_of_card_le hs (show e.card ≤ ((e ∩ f) ∪ (e ∩ g)).card by omega)
  intro x hx
  have hxu : x ∈ (e ∩ f) ∪ (e ∩ g) := heq.symm ▸ (mem_sdiff.mp hx).1
  rcases mem_union.mp hxu with h | h
  · exact False.elim ((mem_sdiff.mp hx).2 (mem_inter.mp h).2)
  · exact (mem_inter.mp h).2

theorem nonseparated_pair_extra {G : V → V → Prop} {e f g : Finset V}
    (he : Separated G e) (hf : Separated G f) (hg : Separated G g)
    (hbad : ¬ Separated G (e ∪ f)) :
    2*(e ∩ f).card + (f ∩ g).card + (g ∩ e).card <
      e.card + f.card + 2*(e ∩ f ∩ g).card := by
  have hi₁ := shared_card_le e f g
  have hi₂ := shared_card_le f e g
  have hcomm : f ∩ e ∩ g = e ∩ f ∩ g := by rw [inter_comm f e]
  rw [hcomm,inter_comm f e] at hi₂
  rw [inter_comm e g] at hi₁
  by_contra hn
  have h₁ : e.card + (e ∩ f ∩ g).card = (e ∩ f).card + (e ∩ g).card := by
    rw [inter_comm e g]; omega
  have h₂ : f.card + (f ∩ e ∩ g).card = (f ∩ e).card + (f ∩ g).card := by
    rw [hcomm,inter_comm f e]; omega
  exact hbad (separated_union_of_cross_covered he hf hg
    (cross_covered_of_shared_card h₁) (cross_covered_of_shared_card h₂))

theorem triangle_intersection_lower {e f g : Finset V} (ht : Triangle e f g) :
    (e ∩ f ∩ g).card + 1 ≤ (e ∩ f).card := by
  have hp := card_pos.mpr ht.1
  have he : g ∩ (e ∩ f) = e ∩ f ∩ g := by ext x; simp only [mem_inter]; tauto
  rw [card_sdiff,he] at hp
  omega

theorem three_union_card (e f g : Finset V) :
    (e ∪ f ∪ g).card + (e ∩ f).card + (f ∩ g).card + (g ∩ e).card =
      e.card + f.card + g.card + (e ∩ f ∩ g).card := by
  have h₁ := Finset.card_union_add_card_inter e f
  have h₂ := Finset.card_union_add_card_inter (e ∪ f) g
  have h₃ := Finset.card_union_add_card_inter (e ∩ g) (f ∩ g)
  have he₁ : (e ∪ f) ∩ g = (e ∩ g) ∪ (f ∩ g) := by
    ext x; simp only [mem_inter,mem_union]; tauto
  have he₂ : (e ∩ g) ∩ (f ∩ g) = e ∩ f ∩ g := by ext x; simp only [mem_inter]; tauto
  rw [he₁] at h₂
  rw [he₂] at h₃
  rw [inter_comm g e]
  omega

set_option maxHeartbeats 4000000 in
/-- Exhaustive cardinal patterns in Lemma 6.1. The disjunction explicitly
allows all three cyclic choices of the exceptional intersection. -/
theorem triangle_classification {H : Hypergraph V} {G : V → V → Prop}
    (hr : RankBounds H 4) (ha : Antichain H) (hl : LooseTriangleFree H)
    (hs : ∀ e ∈ H, Separated G e)
    (hbad₂ : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card = 2 → ¬ Separated G (e ∪ f))
    (hbad₃ : ∀ e ∈ H, ∀ f ∈ H, e.card = 4 → f.card = 4 → (e ∩ f).card ≠ 3)
    {e f g : Finset V} (he : e ∈ H) (hf : f ∈ H) (hg : g ∈ H) (ht : Triangle e f g) :
    (((e ∩ f ∩ g).card = 0 ∧
      (((e ∩ f).card = 2 ∧ (f ∩ g).card = 1 ∧ (g ∩ e).card = 1 ∧ (e.card = 4 ∨ f.card = 4)) ∨
       ((f ∩ g).card = 2 ∧ (g ∩ e).card = 1 ∧ (e ∩ f).card = 1 ∧ (f.card = 4 ∨ g.card = 4)) ∨
       ((g ∩ e).card = 2 ∧ (e ∩ f).card = 1 ∧ (f ∩ g).card = 1 ∧ (g.card = 4 ∨ e.card = 4)))) ∨
     ((e ∩ f ∩ g).card = 0 ∧ e.card = 4 ∧ f.card = 4 ∧ g.card = 4 ∧
       (e ∩ f).card + (f ∩ g).card + (g ∩ e).card = 5) ∨
     ((e ∩ f ∩ g).card = 1 ∧ (e ∩ f).card = 2 ∧ (f ∩ g).card = 2 ∧
       (g ∩ e).card = 2 ∧ 11 ≤ e.card + f.card + g.card)) ∧
      6 ≤ (e ∪ f ∪ g).card ∧ (e ∪ f ∪ g).card ≤ 8 := by
  have hd := triangle_edges_distinct ht
  have hc₁ := intersection_le_two ha hr he hf hd.1 (hbad₃ e he f hf)
  have hc₂ := intersection_le_two ha hr hf hg hd.2.1 (hbad₃ f hf g hg)
  have hc₃ := intersection_le_two ha hr hg he hd.2.2 (hbad₃ g hg e he)
  have ht' : Triangle f g e := ⟨ht.2.1,ht.2.2,ht.1⟩
  have ht'' : Triangle g e f := ⟨ht.2.2,ht.1,ht.2.1⟩
  have heq₁ : f ∩ g ∩ e = e ∩ f ∩ g := by ext x; simp only [mem_inter]; tauto
  have heq₂ : g ∩ e ∩ f = e ∩ f ∩ g := by ext x; simp only [mem_inter]; tauto
  have hb₁ := triangle_intersection_lower ht
  have hb₂ := triangle_intersection_lower ht'
  have hb₃ := triangle_intersection_lower ht''
  rw [heq₁] at hb₂
  rw [heq₂] at hb₃
  have hn : ¬ ((e ∩ f).card ≤ 1 ∧ (f ∩ g).card ≤ 1 ∧ (g ∩ e).card ≤ 1) := by
    rintro ⟨h₁,h₂,h₃⟩
    exact hl e he f hf g hg (triangle_of_small_intersections ht h₁ h₂ h₃)
  have hx₁ := fun h => nonseparated_pair_extra (hs e he) (hs f hf) (hs g hg) (hbad₂ e he f hf hd.1 h)
  have hx₂ := fun h => nonseparated_pair_extra (hs f hf) (hs g hg) (hs e he) (hbad₂ f hf g hg hd.2.1 h)
  have hx₃ := fun h => nonseparated_pair_extra (hs g hg) (hs e he) (hs f hf) (hbad₂ g hg e he hd.2.2 h)
  simp only [heq₁,heq₂] at hx₂ hx₃
  have hu := three_union_card e f g
  have hr₁ := hr e he
  have hr₂ := hr f hf
  have hr₃ := hr g hg
  have hi₁ := shared_card_le e f g
  have hi₂ := shared_card_le f g e
  have hi₃ := shared_card_le g e f
  rw [inter_comm e g] at hi₁
  rw [heq₁,inter_comm f e] at hi₂
  rw [heq₂,inter_comm g f] at hi₃
  interval_cases h₁ : (e ∩ f).card <;>
    interval_cases h₂ : (f ∩ g).card <;>
    interval_cases h₃ : (g ∩ e).card <;> omega

end KMV
