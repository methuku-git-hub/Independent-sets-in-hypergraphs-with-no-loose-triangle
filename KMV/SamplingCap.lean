module
public import KMV.SamplingProducts
public section
namespace KMV.Sampling
open FiniteLaw Finset
variable {n : ℕ}
open scoped Classical

@[expose] def Prefix (S : Finset (Fin n)) (t : ℕ) (w : Fin n → ℝ) : Prop :=
  ∀ v ∈ S, v.val < t → w v = 1

theorem prefix_next_iff {G : Fin n → Fin n → Prop} {β : ℝ}
    (i : Fin n) (S : Finset (Fin n)) (w : Fin n → ℝ) (b : Bool) :
    Prefix S (i.val+1) (next G β i b w) ↔ Prefix S i.val w ∧ (i ∈ S → b = true) := by
  classical
  constructor
  · intro h
    refine ⟨fun v hv ht => ?_, ?_⟩
    · have he := h v hv (by omega)
      rwa [next_past ht b] at he
    · intro hi
      have he := h i hi (by omega)
      cases b <;> simp_all [next]
  · rintro ⟨h,hb⟩ v hv ht
    by_cases hvi : v = i
    · subst v
      simp [next, hb hv]
    · have hlt : v.val < i.val := by
        have hn : v.val ≠ i.val := fun h => hvi (Fin.ext h)
        omega
      rw [next_past hlt b]
      exact h v hv hlt

theorem prefix_succ_iff (i : Fin n) (S : Finset (Fin n)) (w : Fin n → ℝ) :
    Prefix S (i.val+1) w ↔ Prefix S i.val w ∧ (i ∈ S → w i = 1) := by
  constructor
  · intro h
    exact ⟨fun v hv ht => h v hv (by omega), fun hi => h i hi (by omega)⟩
  · rintro ⟨h,hi⟩ v hv ht
    by_cases he : v = i
    · subst v; exact hi hv
    · apply h v hv
      have hn : v.val ≠ i.val := fun h => he (Fin.ext h)
      omega

theorem step_prefix_bound {G : Fin n → Fin n → Prop} {β : ℝ} (hβ : 0 ≤ β)
    (i : Fin n) (S : Finset (Fin n)) (w : Fin n → ℝ) (hw : w i < 1) :
    (step G β i w).probability (Prefix S (i.val+1)) ≤
      (if Prefix S i.val w then 1 else 0) * (if i ∈ S then β else 1) := by
  classical
  by_cases ha : Active β (w i)
  · rw [step, ite_eq_left ha]
    simp only [FiniteLaw.probability, FiniteLaw.expect, prefix_next_iff]
    by_cases hi : i ∈ S <;> by_cases hp : Prefix S i.val w
    · simpa [hi, hp] using ha.2.le
    · simp [hi, hp]
    · simp [hi, hp]
    · simp [hi, hp]
  · rw [step, ite_eq_right ha]
    simp only [FiniteLaw.probability, FiniteLaw.expect, prefix_succ_iff]
    by_cases hi : i ∈ S <;> by_cases hp : Prefix S i.val w
    · simpa [hi, hp, ne_of_lt hw] using hβ
    · simp [hi, hp]
    · simp [hi, hp]
    · simp [hi, hp]

theorem filter_prefix_succ (i : Fin n) (S : Finset (Fin n)) :
    S.filter (fun v => v.val < i.val+1) =
      if i ∈ S then insert i (S.filter (fun v => v.val < i.val))
      else S.filter (fun v => v.val < i.val) := by
  classical
  split_ifs with hi
  · ext v
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨hv,ht⟩
      by_cases he : v = i
      · exact Or.inl he
      · exact Or.inr ⟨hv, by have : v.val ≠ i.val := fun h => he (Fin.ext h); omega⟩
    · rintro (rfl | ⟨hv,ht⟩)
      · exact ⟨hi, by omega⟩
      · exact ⟨hv, by omega⟩
  · ext v
    simp only [mem_filter]
    constructor
    · rintro ⟨hv,ht⟩
      have hn : v.val ≠ i.val := by intro h; have he := Fin.ext h; subst v; exact hi hv
      exact ⟨hv, by omega⟩
    · rintro ⟨hv,ht⟩; exact ⟨hv, by omega⟩

theorem run_prefix_bound {G : Fin n → Fin n → Prop} {β p : ℝ}
    (hβ : β ≤ 1/2) (hβ0 : 0 ≤ β) (hp : 0 ≤ p) (hp' : p < 1)
    (S : Finset (Fin n)) (t : ℕ) (ht : t ≤ n) :
    (run G β p t).probability (Prefix S t) ≤ β ^ (S.filter (fun v => v.val < t)).card := by
  classical
  induction t with
  | zero => simp [run, FiniteLaw.probability, FiniteLaw.expect, Prefix]
  | succ t ih =>
    have htn : t < n := by omega
    let i : Fin n := ⟨t,htn⟩
    have he := FiniteLaw.expect_mono (run_valid (G:=G) (p:=p) hβ t)
      (FiniteLaw.all_mono (run_bounded (G:=G) hβ hp hp' t (by omega))
        (fun w hw => step_prefix_bound (G:=G) hβ0 i S w (hw.2 i (le_refl _))))
    rw [FiniteLaw.expect_mul_const] at he
    have hind := mul_le_mul_of_nonneg_right (ih (by omega))
      (show 0 ≤ (if i ∈ S then β else 1) by split_ifs <;> positivity)
    change (run G β p (t+1)).expect (fun w => if Prefix S (t+1) w then 1 else 0) ≤ _
    rw [run, dite_eq_left htn, FiniteLaw.expect_bind]
    have hcomb := he.trans hind
    have hfilter := filter_prefix_succ i S
    change S.filter (fun v => v.val < t+1) = _ at hfilter
    rw [hfilter]
    by_cases hi : i ∈ S
    · simpa [hi, i, FiniteLaw.probability, pow_succ] using hcomb
    · simpa [hi, i, FiniteLaw.probability] using hcomb

theorem universal_inclusion {G : Fin n → Fin n → Prop} {β p : ℝ}
    (hβ : β ≤ 1/2) (hβ0 : 0 ≤ β) (hp : 0 ≤ p) (hp' : p < 1)
    (S : Finset (Fin n)) :
    (run G β p n).probability (fun w => S ⊆ selected w) ≤ β ^ S.card := by
  classical
  have he : Prefix S n = (fun w => S ⊆ selected w) := by
    funext w
    apply propext
    simp only [Prefix, selected, Finset.subset_iff, mem_filter, mem_univ, true_and]
    exact ⟨fun h v hv => h v hv v.isLt, fun h v hv _ => h hv⟩
  have hf : S.filter (fun v => v.val < n) = S := by
    ext v; simp [v.isLt]
  simpa only [he, hf] using run_prefix_bound (G:=G) hβ hβ0 hp hp' S n (le_refl _)

end KMV.Sampling
