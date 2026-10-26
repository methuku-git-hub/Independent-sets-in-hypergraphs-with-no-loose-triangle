module
public import KMV.Basic
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V]

/-- The manuscript's definition, including its nonemptiness requirement. -/
@[expose] def Expandable (H : Hypergraph V) (r : ℕ) (X : Finset V) : Prop :=
  X.Nonempty ∧ ∀ Y : Finset V, Disjoint X Y → Y.card ≤ 2 * r →
    ∃ e ∈ H, X ⊆ e ∧ Disjoint e Y

omit [DecidableEq V] in
theorem edge_expandable {H : Hypergraph V} {r : ℕ} (hH : RankBounds H r)
    {e : Finset V} (he : e ∈ H) : Expandable H r e := by
  refine ⟨Finset.card_pos.mp (by have := (hH e he).1; omega), ?_⟩
  intro Y hY _
  exact ⟨e, he, Subset.refl e, hY⟩

omit [DecidableEq V] in
theorem expandable_card_le {H : Hypergraph V} {r : ℕ} (hH : RankBounds H r)
    {X : Finset V} (hX : Expandable H r X) : X.card ≤ r := by
  obtain ⟨e, he, hXe, _⟩ := hX.2 ∅ (by simp) (by simp)
  exact (Finset.card_le_card hXe).trans (hH e he).2

private theorem forbidden_card_le {a b X : Finset V} {r : ℕ}
    (ha : a.card ≤ r) (hb : b.card ≤ r) : ((a ∪ b) \ X).card ≤ 2 * r := by
  have h₁ := Finset.card_le_card (Finset.sdiff_subset : (a ∪ b) \ X ⊆ a ∪ b)
  have h₂ := Finset.card_union_le a b
  omega

private theorem disjoint_sdiff_self (X U : Finset V) : Disjoint X (U \ X) := by
  exact Finset.disjoint_left.mpr fun v hv hv' => (Finset.mem_sdiff.mp hv').2 hv

private theorem disjoint_sdiff_of_subset {e U W X : Finset V}
    (h : Disjoint e (W \ X)) (hUW : U ⊆ W) : Disjoint e (U \ X) := by
  apply Finset.disjoint_left.mpr
  intro v hve hv
  exact Finset.disjoint_left.mp h hve
    (Finset.mem_sdiff.mpr ⟨hUW (Finset.mem_sdiff.mp hv).1, (Finset.mem_sdiff.mp hv).2⟩)

/-- Successive extensions keep the prescribed intersection exactly. -/
private theorem extension_inter {X Y e f : Finset V}
    (hXe : X ⊆ e) (hYf : Y ⊆ f)
    (he : Disjoint e (Y \ X)) (hf : Disjoint f (e \ Y)) :
    e ∩ f = X ∩ Y := by
  ext v
  constructor
  · intro hv
    obtain ⟨hve, hvf⟩ := Finset.mem_inter.mp hv
    have hvY : v ∈ Y := by
      by_contra hn
      exact Finset.disjoint_left.mp hf hvf (Finset.mem_sdiff.mpr ⟨hve, hn⟩)
    have hvX : v ∈ X := by
      by_contra hn
      exact Finset.disjoint_left.mp he hve (Finset.mem_sdiff.mpr ⟨hvY, hn⟩)
    exact Finset.mem_inter.mpr ⟨hvX, hvY⟩
  · intro hv
    exact Finset.mem_inter.mpr ⟨hXe (Finset.mem_inter.mp hv).1,
      hYf (Finset.mem_inter.mp hv).2⟩

private theorem ne_of_inter_card_one {e f : Finset V}
    (he : 3 ≤ e.card) (h : (e ∩ f).card = 1) : e ≠ f := by
  intro hef
  subst f
  simp only [Finset.inter_self] at h
  omega

/-- Manuscript Lemma 4.1: three expandable sets cannot form a loose triangle.
All three extensions and their forbidden-set bounds are explicit. -/
theorem expandable_no_loose_triangle {H : Hypergraph V} {r : ℕ}
    (hH : RankBounds H r) (hfree : LooseTriangleFree H)
    {X₁ X₂ X₃ : Finset V} (h₁ : Expandable H r X₁)
    (h₂ : Expandable H r X₂) (h₃ : Expandable H r X₃) :
    ¬ LooseTriangle X₁ X₂ X₃ := by
  intro ht
  have hc₂ := expandable_card_le hH h₂
  have hc₃ := expandable_card_le hH h₃
  obtain ⟨e₁, he₁, hX₁, hd₁⟩ := h₁.2 ((X₂ ∪ X₃) \ X₁)
    (disjoint_sdiff_self _ _) (forbidden_card_le hc₂ hc₃)
  obtain ⟨e₂, he₂, hX₂, hd₂⟩ := h₂.2 ((e₁ ∪ X₃) \ X₂)
    (disjoint_sdiff_self _ _) (forbidden_card_le (hH e₁ he₁).2 hc₃)
  obtain ⟨e₃, he₃, hX₃, hd₃⟩ := h₃.2 ((e₁ ∪ e₂) \ X₃)
    (disjoint_sdiff_self _ _) (forbidden_card_le (hH e₁ he₁).2 (hH e₂ he₂).2)
  have h₁₂ : e₁ ∩ e₂ = X₁ ∩ X₂ := extension_inter hX₁ hX₂
    (disjoint_sdiff_of_subset hd₁ Finset.subset_union_left)
    (disjoint_sdiff_of_subset hd₂ Finset.subset_union_left)
  have h₁₃ : e₁ ∩ e₃ = X₁ ∩ X₃ := extension_inter hX₁ hX₃
    (disjoint_sdiff_of_subset hd₁ Finset.subset_union_right)
    (disjoint_sdiff_of_subset hd₃ Finset.subset_union_left)
  have h₂₃ : e₂ ∩ e₃ = X₂ ∩ X₃ := extension_inter hX₂ hX₃
    (disjoint_sdiff_of_subset hd₂ Finset.subset_union_right)
    (disjoint_sdiff_of_subset hd₃ Finset.subset_union_right)
  obtain ⟨_, _, _, hc₁₂, hc₂₃, hc₃₁, hempty⟩ := ht
  have c₁₂ : (e₁ ∩ e₂).card = 1 := h₁₂ ▸ hc₁₂
  have c₂₃ : (e₂ ∩ e₃).card = 1 := h₂₃ ▸ hc₂₃
  have c₃₁ : (e₃ ∩ e₁).card = 1 := by
    rw [Finset.inter_comm, h₁₃, Finset.inter_comm]
    exact hc₃₁
  apply hfree e₁ he₁ e₂ he₂ e₃ he₃
  refine ⟨ne_of_inter_card_one (hH e₁ he₁).1 c₁₂,
    ne_of_inter_card_one (hH e₂ he₂).1 c₂₃,
    ne_of_inter_card_one (hH e₃ he₃).1 c₃₁, c₁₂, c₂₃, c₃₁, ?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hv₁₂, hv₃⟩ := Finset.mem_inter.mp hv
  have hv₁ := (Finset.mem_inter.mp hv₁₂).1
  have hx₁₂ : v ∈ X₁ ∩ X₂ := h₁₂ ▸ hv₁₂
  have hx₁₃ : v ∈ X₁ ∩ X₃ := h₁₃ ▸ Finset.mem_inter.mpr ⟨hv₁, hv₃⟩
  have hx : v ∈ X₁ ∩ X₂ ∩ X₃ :=
    Finset.mem_inter.mpr ⟨hx₁₂, (Finset.mem_inter.mp hx₁₃).2⟩
  rw [hempty] at hx
  simp at hx

end KMV
