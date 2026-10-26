module
public import KMV.Auxiliary
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V]

@[expose] def Matching (M : Hypergraph V) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

theorem exists_large_matching {L : Hypergraph V} {q D : ℕ}
    (hsize : ∀ e ∈ L, e.Nonempty ∧ e.card ≤ q)
    (hdeg : ∀ x, (L.filter (fun e => x ∈ e)).card ≤ D) :
    ∃ M : Hypergraph V, M ⊆ L ∧ Matching M ∧ L.card ≤ q*D*M.card := by
  classical
  let F := L.powerset.filter Matching
  have hF : F.Nonempty := ⟨∅, by simp [F, Matching]⟩
  obtain ⟨M,hM,hmax⟩ := Finset.exists_max_image F Finset.card hF
  obtain ⟨hsub,hm⟩ : M ⊆ L ∧ Matching M := by simpa [F] using hM
  have hmeet : ∀ e ∈ L, ∃ f ∈ M, (e ∩ f).Nonempty := by
    intro e he
    by_contra hn
    push Not at hn
    have hd : ∀ f ∈ M, Disjoint e f := fun f hf =>
      Finset.disjoint_iff_inter_eq_empty.mpr (hn f hf)
    have hem : e ∉ M := by
      intro hem
      obtain ⟨x,hx⟩ := (hsize e he).1
      exact Finset.disjoint_left.mp (hd e hem) hx hx
    have hmatch : Matching (insert e M) := by
      intro a ha b hb hab
      simp only [mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact False.elim (hab rfl)
      · exact hd b hb
      · exact (hd a ha).symm
      · exact hm a ha b hb hab
    have hh : insert e M ∈ F := by simp [F, insert_subset_iff, he, hsub, hmatch]
    have hc := hmax (insert e M) hh
    rw [card_insert_of_notMem hem] at hc
    omega
  have hcover : L ⊆ M.biUnion (fun e => e.biUnion (fun x => L.filter (fun f => x ∈ f))) := by
    intro f hf
    obtain ⟨e,he,x,hx⟩ := hmeet f hf
    exact mem_biUnion.mpr ⟨e,he,mem_biUnion.mpr ⟨x,(mem_inter.mp hx).2,
      mem_filter.mpr ⟨hf,(mem_inter.mp hx).1⟩⟩⟩
  refine ⟨M,hsub,hm,?_⟩
  calc
    L.card ≤ (M.biUnion (fun e => e.biUnion (fun x => L.filter (fun f => x ∈ f)))).card :=
      card_le_card hcover
    _ ≤ ∑ e ∈ M, (e.biUnion (fun x => L.filter (fun f => x ∈ f))).card := card_biUnion_le
    _ ≤ ∑ e ∈ M, q*D := by
      apply sum_le_sum
      intro e he
      calc
        _ ≤ ∑ x ∈ e, (L.filter (fun f => x ∈ f)).card := card_biUnion_le
        _ ≤ ∑ _x ∈ e, D := sum_le_sum (fun x _ => hdeg x)
        _ = e.card*D := by simp
        _ ≤ q*D := Nat.mul_le_mul_right D (hsize e (hsub he)).2
    _ = q*D*M.card := by simp [Nat.mul_comm]

/-- A transversal of pairwise disjoint nonempty finite sets. -/
theorem matching_transversal {M : Hypergraph V} (hm : Matching M)
    (hne : ∀ e ∈ M, e.Nonempty) :
    ∃ X : Finset V, X.card = M.card ∧ X ⊆ M.biUnion id ∧
      ∀ e ∈ M, (e ∩ X).card = 1 := by
  classical
  let f : {e // e ∈ M} → V := fun e => (hne e.val e.property).choose
  have hf : ∀ e, f e ∈ e.val := fun e => (hne e.val e.property).choose_spec
  have hinj : Function.Injective f := by
    intro e d hed
    apply Subtype.ext
    by_contra hne'
    exact Finset.disjoint_left.mp (hm e.val e.property d.val d.property hne')
      (hf e) (hed ▸ hf d)
  let X := M.attach.image f
  have hcard : X.card = M.card := by
    rw [Finset.card_image_of_injective _ hinj]
    exact Finset.card_attach
  have hsub : X ⊆ M.biUnion id := by
    intro x hx
    obtain ⟨e,_,rfl⟩ := mem_image.mp hx
    exact mem_biUnion.mpr ⟨e.val,e.property,hf e⟩
  refine ⟨X,hcard,hsub,?_⟩
  intro e he
  have heq : e ∩ X = {f ⟨e,he⟩} := by
    ext x
    simp only [mem_inter, mem_singleton]
    constructor
    · rintro ⟨hx,hX⟩
      obtain ⟨d,_,hfd⟩ := mem_image.mp hX
      have hde : d.val = e := by
        by_contra h
        exact Finset.disjoint_left.mp (hm d.val d.property e he h) (hf d) (hfd.symm ▸ hx)
      have hh : d = ⟨e,he⟩ := Subtype.ext hde
      simpa [hh] using hfd.symm
    · intro hx
      subst x
      exact ⟨hf ⟨e,he⟩, mem_image.mpr ⟨⟨e,he⟩,by simp,rfl⟩⟩
  simp [heq]

end KMV
