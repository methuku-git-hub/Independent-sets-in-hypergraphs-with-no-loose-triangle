module
public import KMV.Coloring
public import KMV.Trimming
public section
namespace KMV
open Finset

theorem large_independent_in_subset {n q : ℕ} {H : Hypergraph (Fin n)}
    (U : Finset (Fin n)) {color : Fin n → Fin q} (hp : ProperColoring H color) (hq : 0 < q) :
    ∃ I : Finset (Fin n), I ⊆ U ∧ Independent H I ∧ (U.card : ℝ)/q ≤ I.card := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have ht : (Finset.univ : Finset (Fin q)).Nonempty := ⟨⟨0,hq⟩,by simp⟩
  have hb : (Finset.univ : Finset (Fin q)).card • ((U.card : ℝ)/q) ≤ (U.card : ℝ) := by
    simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact le_of_eq (mul_div_cancel₀ _ hqr)
  obtain ⟨c,_,hc⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (f:=color) (fun _ _ => Finset.mem_univ _) ht hb
  refine ⟨U.filter (fun v => color v=c),filter_subset _ _,?_,hc⟩
  apply independent_mono (color_class_independent hp c)
  intro x hx
  exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩

/-- Keeping the original vertex type avoids relabeling the surviving set.
The color class is explicitly intersected with U before independence transfer. -/
theorem liPostle34_on_subset (hLP : LiPostle34) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (H : Hypergraph (Fin n)) (U : Finset (Fin n)),
    U.Nonempty → RankBounds (induced H U) 4 → TriangleFree (induced H U) →
    ∀ D₃ D₄ : ℝ, 8 ≤ D₃ → 8 ≤ D₄ →
    (∀ v, (sizeDegree (induced H U) 3 v : ℝ) ≤ D₃) →
    (∀ v, (sizeDegree (induced H U) 4 v : ℝ) ≤ D₄) →
    ∃ I : Finset (Fin n), I ⊆ U ∧ Independent H I ∧
      (U.card : ℝ)/(C * max (Real.rpow (D₃/Real.log D₃) (1/2 : ℝ))
        (Real.rpow (D₄/Real.log D₄) (1/3 : ℝ))) ≤ I.card := by
  obtain ⟨C,hC,hLP⟩ := hLP
  refine ⟨C,hC,?_⟩
  intro n H U hU hr ht D₃ D₄ h₃ h₄ hd₃ hd₄
  obtain ⟨q,color,hproper,hbound⟩ := hLP n (induced H U) hr ht D₃ D₄ h₃ h₄ hd₃ hd₄
  obtain ⟨v,hv⟩ := hU
  have hq : 0 < q := Nat.zero_lt_of_lt (color v).isLt
  obtain ⟨I,hIU,hI,hcard⟩ := large_independent_in_subset U hproper hq
  refine ⟨I,hIU,independent_induced_transfer hIU hI,?_⟩
  exact (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast hq) hbound).trans hcard

end KMV
