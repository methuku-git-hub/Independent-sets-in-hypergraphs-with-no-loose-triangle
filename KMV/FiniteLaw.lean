module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public section
namespace KMV

/-- A finite probability tree. At a fork, the left branch has probability a.
Validity is a proved predicate, not an axiom or a hidden result assumption. -/
inductive FiniteLaw (α : Type*) where
  | pure (x : α)
  | fork (a : ℝ) (left right : FiniteLaw α)

namespace FiniteLaw
variable {α β : Type*}

@[expose] def Valid : FiniteLaw α → Prop
  | .pure _ => True
  | .fork a l r => 0 ≤ a ∧ a ≤ 1 ∧ l.Valid ∧ r.Valid

@[expose] def All (P : α → Prop) : FiniteLaw α → Prop
  | .pure x => P x
  | .fork _ l r => l.All P ∧ r.All P

@[expose] noncomputable def expect (f : α → ℝ) : FiniteLaw α → ℝ
  | .pure x => f x
  | .fork a l r => a * l.expect f + (1-a) * r.expect f

@[expose] def bind (d : FiniteLaw α) (k : α → FiniteLaw β) : FiniteLaw β :=
  match d with
  | .pure x => k x
  | .fork a l r => .fork a (l.bind k) (r.bind k)

theorem all_mono {d : FiniteLaw α} {P Q : α → Prop}
    (h : d.All P) (hpq : ∀ x, P x → Q x) : d.All Q := by
  induction d with
  | pure x => exact hpq x h
  | fork a l r il ir => exact ⟨il h.1, ir h.2⟩

theorem all_true (d : FiniteLaw α) : d.All (fun _ => True) := by
  induction d with
  | pure _ => trivial
  | fork _ _ _ il ir => exact ⟨il, ir⟩

theorem all_and {d : FiniteLaw α} {P Q : α → Prop}
    (hp : d.All P) (hq : d.All Q) : d.All (fun x => P x ∧ Q x) := by
  induction d with
  | pure x => exact ⟨hp, hq⟩
  | fork a l r il ir => exact ⟨il hp.1 hq.1, ir hp.2 hq.2⟩

theorem all_of_forall (d : FiniteLaw α) {P : α → Prop} (h : ∀ x, P x) : d.All P :=
  all_mono (all_true d) (fun x _ => h x)

theorem all_bind {d : FiniteLaw α} {k : α → FiniteLaw β} {P : α → Prop} {Q : β → Prop}
    (h : d.All P) (hk : ∀ x, P x → (k x).All Q) : (d.bind k).All Q := by
  induction d with
  | pure x => exact hk x h
  | fork a l r il ir => exact ⟨il h.1, ir h.2⟩

theorem valid_bind {d : FiniteLaw α} (hd : d.Valid) {k : α → FiniteLaw β}
    (hk : d.All (fun x => (k x).Valid)) : (d.bind k).Valid := by
  induction d with
  | pure x => exact hk
  | fork a l r il ir => exact ⟨hd.1, hd.2.1, il hd.2.2.1 hk.1, ir hd.2.2.2 hk.2⟩

theorem expect_bind (d : FiniteLaw α) (k : α → FiniteLaw β) (f : β → ℝ) :
    (d.bind k).expect f = d.expect (fun x => (k x).expect f) := by
  induction d with
  | pure x => rfl
  | fork a l r il ir => simp only [bind, expect, il, ir]

theorem expect_congr {d : FiniteLaw α} {f g : α → ℝ}
    (h : d.All (fun x => f x = g x)) : d.expect f = d.expect g := by
  induction d with
  | pure x => exact h
  | fork a l r il ir => simp only [expect, il h.1, ir h.2]

theorem expect_const (d : FiniteLaw α) (c : ℝ) : d.expect (fun _ => c) = c := by
  induction d with
  | pure x => rfl
  | fork a l r il ir => simp only [expect, il, ir]; ring

theorem expect_add (d : FiniteLaw α) (f g : α → ℝ) :
    d.expect (fun x => f x + g x) = d.expect f + d.expect g := by
  induction d with
  | pure x => rfl
  | fork a l r il ir => simp only [expect, il, ir]; ring

theorem expect_sub (d : FiniteLaw α) (f g : α → ℝ) :
    d.expect (fun x => f x - g x) = d.expect f - d.expect g := by
  induction d with
  | pure x => rfl
  | fork a l r il ir => simp only [expect, il, ir]; ring

theorem expect_mul_const (d : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    d.expect (fun x => f x * c) = d.expect f * c := by
  induction d with
  | pure x => rfl
  | fork a l r il ir => simp only [expect, il, ir]; ring

theorem expect_sum {ι : Type*} (d : FiniteLaw α) (S : Finset ι) (f : ι → α → ℝ) :
    d.expect (fun x => ∑ i ∈ S, f i x) = ∑ i ∈ S, d.expect (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [expect_const]
  | @insert i S hi ih => simp only [Finset.sum_insert hi, expect_add, ih]

theorem expect_mono {d : FiniteLaw α} (hd : d.Valid) {f g : α → ℝ}
    (h : d.All (fun x => f x ≤ g x)) : d.expect f ≤ d.expect g := by
  induction d with
  | pure x => exact h
  | fork a l r il ir =>
    exact add_le_add (mul_le_mul_of_nonneg_left (il hd.2.2.1 h.1) hd.1)
      (mul_le_mul_of_nonneg_left (ir hd.2.2.2 h.2) (sub_nonneg.mpr hd.2.1))

theorem expect_nonneg {d : FiniteLaw α} (hd : d.Valid) {f : α → ℝ}
    (h : d.All (fun x => 0 ≤ f x)) : 0 ≤ d.expect f := by
  simpa only [expect_const] using expect_mono hd h

/-- A leaf attaining at least the expectation; the predicate can carry all
deterministic invariants of the random construction. -/
theorem exists_ge_of_all {d : FiniteLaw α} (hd : d.Valid) {P : α → Prop}
    (hP : d.All P) (f : α → ℝ) : ∃ x, P x ∧ d.expect f ≤ f x := by
  induction d with
  | pure x => exact ⟨x, hP, le_refl _⟩
  | fork a l r il ir =>
    by_cases h : l.expect f ≤ r.expect f
    · obtain ⟨x, hx, hfx⟩ := ir hd.2.2.2 hP.2
      refine ⟨x, hx, le_trans ?_ hfx⟩
      dsimp [expect]
      nlinarith [mul_le_mul_of_nonneg_left h hd.1]
    · obtain ⟨x, hx, hfx⟩ := il hd.2.2.1 hP.1
      refine ⟨x, hx, le_trans ?_ hfx⟩
      dsimp [expect]
      nlinarith [mul_le_mul_of_nonneg_left (le_of_not_ge h) (sub_nonneg.mpr hd.2.1)]

@[expose] noncomputable def probability (d : FiniteLaw α) (P : α → Prop) : ℝ :=
  by classical exact d.expect (fun x => if P x then 1 else 0)

end FiniteLaw
end KMV
