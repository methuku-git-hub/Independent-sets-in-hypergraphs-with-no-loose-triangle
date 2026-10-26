module
public import KMV.Statements
public import Mathlib.Combinatorics.Pigeonhole
public section
namespace KMV
open Finset

theorem color_class_independent {n q : ℕ} {H : Hypergraph (Fin n)}
    {color : Fin n → Fin q} (hp : ProperColoring H color) (c : Fin q) :
    Independent H (Finset.univ.filter fun v => color v = c) := by
  intro e he hsub
  obtain ⟨x, hx, y, hy, hxy⟩ := hp e he
  exact hxy ((Finset.mem_filter.mp (hsub hx)).2.trans
    (Finset.mem_filter.mp (hsub hy)).2.symm)

theorem large_independent_of_coloring {n q : ℕ} {H : Hypergraph (Fin n)}
    {color : Fin n → Fin q} (hp : ProperColoring H color) (hq : 0 < q) :
    ∃ I : Finset (Fin n), Independent H I ∧ (n : ℝ) / q ≤ (I.card : ℝ) := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have ht : (Finset.univ : Finset (Fin q)).Nonempty := ⟨⟨0, hq⟩, by simp⟩
  have hb : (Finset.univ : Finset (Fin q)).card • ((n : ℝ) / q) ≤
      ((Finset.univ : Finset (Fin n)).card : ℝ) := by
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_of_eq (mul_div_cancel₀ (n : ℝ) hqr)
  obtain ⟨c, _, hc⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (f := color) (fun _ _ => Finset.mem_univ _) ht hb
  exact ⟨_, color_class_independent hp c, hc⟩

/-- The elementary coloring-to-independence step needed after Li--Postle. -/
theorem independent_of_coloring_bound {n q : ℕ} {H : Hypergraph (Fin n)}
    (hn : 0 < n) {color : Fin n → Fin q} (hp : ProperColoring H color)
    {B : ℝ} (hB : (q : ℝ) ≤ B) :
    ∃ I : Finset (Fin n), Independent H I ∧ (n : ℝ) / B ≤ (I.card : ℝ) := by
  have hq : 0 < q := Nat.zero_lt_of_lt (color ⟨0, hn⟩).isLt
  obtain ⟨I, hI, hc⟩ := large_independent_of_coloring hp hq
  refine ⟨I, hI, le_trans ?_ hc⟩
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) (by exact_mod_cast hq) hB

/-- A checked consequence of the sole permitted external premise.
This is not the manuscript's main theorem: the cleaning argument is separate. -/
theorem liPostle34_independent (hLP : LiPostle34) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (H : Hypergraph (Fin n)), 0 < n →
    RankBounds H 4 → TriangleFree H →
    ∀ D₃ D₄ : ℝ, 8 ≤ D₃ → 8 ≤ D₄ →
    (∀ v, (sizeDegree H 3 v : ℝ) ≤ D₃) →
    (∀ v, (sizeDegree H 4 v : ℝ) ≤ D₄) →
    ∃ I : Finset (Fin n), Independent H I ∧
      (n : ℝ) / (C * max (Real.rpow (D₃ / Real.log D₃) (1 / 2 : ℝ))
        (Real.rpow (D₄ / Real.log D₄) (1 / 3 : ℝ))) ≤ (I.card : ℝ) := by
  obtain ⟨C, hC, hp⟩ := hLP
  refine ⟨C, hC, ?_⟩
  intro n H hn hr ht D₃ D₄ h₃ h₄ hd₃ hd₄
  obtain ⟨q, color, hproper, hbound⟩ := hp n H hr ht D₃ D₄ h₃ h₄ hd₃ hd₄
  exact independent_of_coloring_bound hn hproper hbound

end KMV
