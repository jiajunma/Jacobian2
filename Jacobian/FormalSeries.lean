import Mathlib

open Classical

open Order

open Finset

open LinearOrder

open Module

noncomputable section

namespace Classical

instance unique {α : Type _} {p : α → Prop} (h : ∃! a : α, p a) : Unique {a : α // p a} := by
  have h1 : Nonempty (Unique (Subtype p)) := by
    rw [unique_subtype_iff_exists_unique]
    exact h
  exact Classical.choice h1

end Classical

namespace Finset

def spilt_finset {α : Type _} {T : Finset α} {S : Finset α} (hs : S ⊆ T)
    : S ∪ (T \ S) = T ∧ Disjoint S (T \ S) := by
  have h1 : S ∪ (T \ S) = T := by
    apply Finset.union_sdiff_of_subset hs
  have h2 : Disjoint S (T \ S) := by
    rw [disjoint_iff_inter_eq_empty, inter_comm]
    apply sdiff_inter_self
  simp [h1, h2]

lemma finset_sum_superset {α : Type _} {s : Finset α} {t : Finset α} (hs : s ⊆ t)
    {β : Type _} [AddCommMonoid β] {p : α → β} (hp : ∀ a : α, a ∈ t \ s → p a = 0) : ∑ a ∈ s, p a = ∑ a ∈ t, p a := by
  obtain ⟨hs1,hs2⟩ := spilt_finset hs
  rw [← hs1]
  rw [Finset.sum_union hs2]
  have h : ∑ a ∈ t \ s, p a = 0 := by
    have ht : ∀ a ∈ t \ s, p a = 0 := by
      intro a ht1
      apply hp
      exact ht1
    apply sum_eq_zero
    exact ht
  rw [h]
  simp

structure locally_finite (α : Type _) (β : Type _) (γ : Type _) [AddMonoid γ] where
  funs : α → (β → γ)
  locally_finite : ∀ x : β, {a : α | (funs a) x ≠ 0}.Finite

def hsum {α : Type _} {β : Type _} {γ : Type _} [AddCommMonoid γ]
  (fs : locally_finite α β γ) := fun x : β ↦ ∑ᶠ a : α, (fs.funs a) x

@[simp]
lemma hsum_eq {α : Type _} {β : Type _} {γ : Type _} [AddCommMonoid γ]
  (fs : locally_finite α β γ) : hsum fs = fun x : β
    ↦ ∑ a ∈ (fs.locally_finite x).toFinset, (fs.funs a) x := by
  ext x
  simp [hsum]
  apply finsum_eq_sum (fun a : α ↦ fs.funs a x)


end Finset

namespace ZeroMemClass

@[ext]
structure SubZero (T : Type _) [Zero T] where
  carrier : Set T
  isContaining_zero : 0 ∈ carrier

instance instSetLike (T : Type _) [Zero T] : SetLike (SubZero T) T where
  coe S := S.carrier
  coe_injective' := by
    intro A B h
    obtain ⟨a, ha⟩ := A
    obtain ⟨b, hb⟩ := B
    congr

instance toSubset {T : Type _} [Zero T] (R : SubZero T) : Set T := R.carrier

instance instZeroMemClass (T : Type _) [Zero T] : ZeroMemClass (SubZero T) T where
  zero_mem := by
    intro s
    apply s.isContaining_zero

instance toZero {T : Type _} [Zero T] {S : Type _} {R : S} [SetLike S T] [ZeroMemClass S T]
    : Zero R where
  zero := ⟨0, ZeroMemClass.zero_mem R⟩

@[simp]
lemma zero_coe_eq {T : Type _} [Zero T] {S : Type _} {R : S} [SetLike S T] [ZeroMemClass S T]
    : (0 : R).1 = 0 := by
  trivial

def SubZeroHom (T : Type _) [Zero T] {S : Type _} (R : S) [SetLike S T] [ZeroMemClass S T] : ZeroHom R T where
  toFun := fun a : R ↦ a.1
  map_zero' := zero_coe_eq

end ZeroMemClass

namespace HahnModule

variable {Γ : Type _} [OrderedCancelAddCommMonoid Γ] {α : Type _} {β : Type _} [Zero α] [AddCommMonoid β] [SMulWithZero α β]

theorem smul_coeff_superset {a : HahnSeries Γ α} {f : HahnModule Γ α β} {k : Γ}
  {s : Finset (Γ × Γ)} (hs : ∀ ij ∈ s, ij.1 + ij.2 = k) (hsub : (VAddAntidiagonal a.isPWO_support ((HahnModule.of α).symm (f : HahnSeries Γ β)).isPWO_support k) ⊆ s)
  : (a • f).coeff k = ∑ ij ∈ s, a.coeff ij.1 • ((HahnModule.of α).symm f).coeff ij.2 := by
  have h : (a • f).coeff k = ∑ ij ∈ VAddAntidiagonal a.isPWO_support ((HahnModule.of α).symm f).isPWO_support k,
        a.coeff ij.fst • ((HahnModule.of α).symm f).coeff ij.snd := by
    apply smul_coeff
  rw [h]
  apply Finset.finset_sum_superset hsub _
  simp
  intro i j hab hsupp
  let ij : Γ × Γ := (i,j)
  have hab1 : ij ∈ s := by apply hab
  have hab2 : ij.1 + ij.2 = k := by
    apply hs
    exact hab1
  simp at hab2
  simp [hab2] at hsupp
  by_cases hz : a.coeff i = 0
  ·
    rw [hz]
    apply SMulWithZero.zero_smul
  ·
    simp [hz] at hsupp
    rw [hsupp]
    apply SMulZeroClass.smul_zero

end HahnModule

namespace HahnSeries

variable {Γ : Type _} {T : Type _} [OrderedCancelAddCommMonoid Γ] {R : Type _}
    --[Semiring T] [Semiring R] --{comp : R →+* T}

section CoeViaComp

def coe_via_comp [Zero R] [Zero T] {F : Type _} [FunLike F R T] [ZeroHomClass F R T]
  (comp : F) (f : HahnSeries Γ R) : HahnSeries Γ T where
  coeff := comp ∘ f.coeff
  isPWO_support' := by
    have h : (comp ∘ f.coeff).support ⊆ f.coeff.support := by
      apply Function.support_comp_subset (ZeroHomClass.map_zero comp)
    apply Set.IsPWO.mono f.isPWO_support' h

@[simp]
lemma coe_via_comp_coeff [Zero R] [Zero T] {F : Type _} [FunLike F R T] [ZeroHomClass F R T]
  (comp : F) {f : HahnSeries Γ R} : (coe_via_comp comp f).coeff = comp ∘ f.coeff := by
  trivial

@[simp]
lemma coe_add_hom_via_comp [AddMonoid R] [AddMonoid T]
  {F : Type _} [FunLike F R T] [AddMonoidHomClass F R T]
  (comp : F) (f g : HahnSeries Γ R)
  : coe_via_comp comp (f + g) = coe_via_comp comp f + coe_via_comp comp g := by
  ext k
  simp

@[simp]
lemma coe_mul_hom_via_comp [Semiring T] [Semiring R]  {F : Type _} [FunLike F R T] [RingHomClass F R T]
  (comp : F)  (f g : HahnSeries Γ R)
  : coe_via_comp comp (f * g) = coe_via_comp comp f * coe_via_comp comp g := by
  ext k
  simp
  have hsupp : (addAntidiagonal (coe_via_comp comp f).isPWO_support (coe_via_comp comp g).isPWO_support k)
    ⊆ (addAntidiagonal f.isPWO_support g.isPWO_support k) := by
    intro ij hij
    simp at hij
    simp
    simp [hij.2.2]
    have h : f.coeff ij.1 ≠ 0 := by
      apply ne_zero_of_map hij.1
    have h1 : g.coeff ij.2 ≠ 0 := by
      apply ne_zero_of_map hij.2.1
    simp [h,h1]
  have hs : ∀ ij ∈ (addAntidiagonal f.isPWO_support g.isPWO_support k), ij.1 + ij.2 = k := by
    intro ij hij
    simp at hij
    exact hij.2.2
  have hr : ((coe_via_comp comp f) * (coe_via_comp comp g)).coeff k
      = ∑ ij ∈ (addAntidiagonal f.isPWO_support g.isPWO_support k), (coe_via_comp comp f).coeff ij.1 * (coe_via_comp comp g).coeff ij.2 := by
    apply HahnModule.smul_coeff_superset hs hsupp
  rw [hr]
  simp [mul_coeff]

@[simp]
def HahnSeries_hom_via_comp [Semiring T] [Semiring R] (comp : R →+* T) : (HahnSeries Γ R →+* HahnSeries Γ T) where
  toFun := coe_via_comp comp
  map_add' f g := coe_add_hom_via_comp comp.toAddMonoidHom f g
  map_mul' f g := coe_mul_hom_via_comp comp f g
  map_one' := by
    ext _
    simp
  map_zero' := by
    ext _
    simp

instance [Semiring T] [Semiring R] : Coe (R →+* T) (HahnSeries Γ R →+* HahnSeries Γ T) where
  coe comp := HahnSeries_hom_via_comp comp

instance instHahnSeriesAlgHom {α : Type _} [CommSemiring α] [Semiring T] [Semiring R] [Algebra α T] [Algebra α R]
  : Coe (R →ₐ[α] T) (HahnSeries Γ R →ₐ[α] HahnSeries Γ T) where
  coe comp := {HahnSeries_hom_via_comp comp with
  commutes' := by
    intro r
    simp [coe_via_comp]
    ext k
    simp [algebraMap, Algebra.toRingHom, single_coeff]
    by_cases h : k = 0
    · simp [if_pos h]
      apply comp.commutes
    · simp [if_neg h]
  }

@[simp]
lemma coe_eq [Zero R] [Zero T] {F : Type _} [FunLike F R T] [ZeroHomClass F R T]
  {comp : F} {f g : HahnSeries Γ R}
  : coe_via_comp comp f = coe_via_comp comp g ↔ comp ∘ f.coeff = comp ∘ g.coeff := by
  constructor
  ·
    intro hl
    simp [← coe_via_comp_coeff]
    exact hl
  ·
    intro hr
    simp [← coe_via_comp_coeff] at hr
    exact hr

lemma coe_inj [Zero R] [Zero T] {F : Type _} [FunLike F R T] [ZeroHomClass F R T]
  {comp : F} (hinj : Function.Injective comp) {f g : HahnSeries Γ R}
  (h : coe_via_comp comp f = coe_via_comp comp g) : f = g := by
  rw [coe_eq] at h
  ext k
  apply hinj
  have hf : (comp ∘ f.coeff) k = comp (f.coeff k) := by
    simp
  have hg : (comp ∘ g.coeff) k = comp (g.coeff k) := by
    simp
  rw [← hf, ← hg, h]


def resRange (comp : R → T)
    : R → Set.range comp := Set.rangeFactorization comp

@[simp]
lemma zero_in_range  [Zero R] [Zero T] {F : Type _} [FunLike F R T] [ZeroHomClass F R T]
  (comp : F) : 0 ∈ Set.range comp := by
  simp
  use 0
  apply ZeroHomClass.map_zero comp

def RangeOfZeroHom [Zero R] [Zero T] {F : Type _} [FunLike F R T] [ZeroHomClass F R T]
  (comp : F) : ZeroMemClass.SubZero T where
  carrier := Set.range comp
  isContaining_zero := zero_in_range comp

instance rangeOfZeroHomToZero  [Zero R] [Zero T] {F : Type _} [FunLike F R T] [ZeroHomClass F R T]
  {comp : F} :
    Zero (RangeOfZeroHom comp) where
  zero := ⟨0,zero_in_range comp⟩

lemma InvZeroHom [Zero R] [Zero T] {F : Type _} [FunLike F R T] [ZeroHomClass F R T]
  (comp : F)
  : ∃ inv : RangeOfZeroHom comp → R, inv 0 = 0 ∧ (resRange comp) ∘ inv = id := by
  have hs : Function.Surjective (resRange comp) := by
    apply Set.surjective_onto_range
  obtain ⟨rinv, hrinv⟩ := Function.Surjective.hasRightInverse hs
  let f : RangeOfZeroHom comp → R := fun x ↦ if x = 0 then 0 else rinv x
  have hzero : f 0 = 0 := by
    apply if_pos
    trivial
  have hnonz {x : RangeOfZeroHom comp} (hx : x ≠ 0) : f x = rinv x := by
    apply if_neg
    exact hx
  have hn : (resRange comp) ∘ f = id := by
    ext x
    by_cases hx : x = 0
    ·
      rw [hx]
      simp
      rw [hzero]
      apply ZeroHomClass.map_zero comp
    ·
      observe hxnz : x ≠ 0
      have h1 : ((resRange comp) ∘ f) x = x := by
        calc
          _ = (resRange comp) (f x) := by
            trivial
          _ = (resRange comp) (rinv x) := by
            rw [hnonz hxnz]
          _ = ((resRange comp) ∘ rinv) x := by trivial
          _ = id x := by
            apply hrinv
          _ = x := by trivial
      simp
      rw [Subtype.ext_iff] at h1
      exact h1
  use f

@[simp]
theorem range_of_comp [Zero R] [Zero T] {F : Type _} [FunLike F R T] [ZeroHomClass F R T]
  {comp : F} {f : HahnSeries Γ T}
  : f ∈ Set.range (coe_via_comp comp) ↔ ∀ k : Γ, f.coeff k ∈ Set.range comp := by
  constructor
  ·
    intro hl k
    obtain ⟨g, hg⟩ := hl
    simp
    use g.coeff k
    have h : (coe_via_comp comp g).coeff = comp ∘ g.coeff := by
      simp [coe_via_comp_coeff]
    rw [hg] at h
    simp [h]
  ·
    intro hr
    let new_coeff : Γ → RangeOfZeroHom comp := fun k ↦ ⟨f.coeff k, hr k⟩
    have hinj : Function.Injective (fun a : (RangeOfZeroHom comp) ↦ a.1) := by
      intro a b hab
      simp at hab
      exact hab
    have hcomp : (fun a : (RangeOfZeroHom comp) ↦ a.1) ∘ new_coeff = f.coeff := by
      trivial
    have hnew_supp : f.coeff.support = new_coeff.support := by
      have hz {k : (RangeOfZeroHom comp)} : (fun a : (RangeOfZeroHom comp) ↦ a.1) k = 0 ↔ k = 0 := by
        constructor
        ·
          intro hk
          apply hinj
          exact hk
        ·
          intro hr
          simp
          exact hr
      rw [← hcomp]
      apply Function.support_comp_eq
      exact hz
    have new_supp : new_coeff.support.IsPWO := by
      rw [← hnew_supp]
      apply f.isPWO_support

    obtain ⟨rinv, hrinv1, hrinv2⟩ := InvZeroHom comp
    let inv : ZeroHom (RangeOfZeroHom comp) R := ⟨rinv,hrinv1⟩
    let g := coe_via_comp inv ⟨ new_coeff,new_supp⟩
    use g
    ext k
    simp
    calc
      _ = comp (rinv (new_coeff k)) := by
        trivial
      _ = (comp ∘ rinv) (new_coeff k) := by
        trivial
      _ = id (new_coeff k) := by
        rw [← hrinv2]
        trivial
      _ = new_coeff k := by
        trivial

end CoeViaComp


end HahnSeries

namespace PowerSeries

open PowerSeries
open Polynomial
open MvPolynomial
open RingQuot

section InverseLimit

variable (α : Type _) [CommSemiring α]

instance : CommSemiring (α[X]) := Polynomial.commSemiring

def nrel_poly (n : ℕ) : α[X] → α[X] → Prop := fun (p : α[X]) ↦ fun (q : α[X]) ↦ ∀ k < n, p.coeff k = q.coeff k

def nrel_power (n : ℕ) (p q : α⟦X⟧) := ∀ k < n, coeff α k p = coeff α k q

lemma add_left_poly (n : ℕ) : ∀ ⦃a b c : α[X]⦄, nrel_poly α n a b → nrel_poly α n (a + c) (b + c) := by
  intro a b c hab
  intro k hk
  simp
  rw [hab k]
  exact hk

lemma mul_left_poly (n : ℕ) : ∀ ⦃a b c : α[X]⦄, nrel_poly α n a b → nrel_poly α n (a * c) (b * c) := by
  intro a b c hab
  intro k hk
  simp [Polynomial.coeff_mul]
  apply Finset.sum_congr
  simp
  intro ij hij
  simp at hij
  have h : ij.1 < n := by
    linarith
  have h1 : a.coeff ij.1 = b.coeff ij.1 := by
    apply hab
    exact h
  rw [h1]

lemma mul_right_poly (n : ℕ) : ∀ ⦃a b c : α[X]⦄, nrel_poly α n a b → nrel_poly α n (c * a) (c * b) := by
  intro a b c hab
  intro k hk
  simp [Polynomial.coeff_mul]
  apply Finset.sum_congr
  simp
  intro ij hij
  simp at hij
  have h : ij.2 < n := by
    linarith
  have h1 : a.coeff ij.2 = b.coeff ij.2 := by
    apply hab
    exact h
  rw [h1]

@[simp]
lemma rel_eq_poly (n : ℕ) : RingQuot.Rel (nrel_poly α n) = nrel_poly α n := by
  ext a b
  constructor
  · intro hl
    induction hl with
    | of h => exact h
    | add_left _ hplus => apply add_left_poly; exact hplus
    | mul_left _ hmul1 => apply mul_left_poly; exact hmul1
    | mul_right _ hmul2 => apply mul_right_poly; exact hmul2
  · intro hr
    apply RingQuot.Rel.of
    exact hr

@[simp]
lemma EqGen_eq_poly (n : ℕ) : EqvGen (nrel_poly α n) = nrel_poly α n := by
  ext a b
  constructor
  · intro hl
    induction hl with
    | rel _ _ h => exact h
    | refl _ => intro k _; rfl
    | symm _ _ _ h => intro k hk; apply Eq.symm; apply h; exact hk
    | trans _ _ _ _ _ hab hbc => intro k hk; apply Eq.trans; apply hab; exact hk; apply hbc; exact hk
  · intro hr
    apply EqvGen.rel
    exact hr

lemma trailingDegree_le_pow (p : α[X]) (n : ℕ) : n • p.trailingDegree ≤ (p ^ n).trailingDegree :=
  match n with
  | 0 => by simp
  | n + 1 => by
    simp only [pow_succ]
    have h : n • p.trailingDegree ≤ (p ^ n).trailingDegree := by
      apply trailingDegree_le_pow p n
    have h1 : (p ^n).trailingDegree + p.trailingDegree ≤ (p ^ n * p).trailingDegree := by
      apply Polynomial.le_trailingDegree_mul
    apply le_trans _ h1
    rw [add_smul]
    apply add_le_add
    exact h
    simp

@[simp]
lemma smul_le_ENat {a : ℕ∞} {n : ℕ} (h : 1 ≤ a) : n ≤ n • a :=
  match n with
  | 0 => by simp
  | n + 1 => by
    have h1 : (n + 1) • a = n • a + a := by
      simp [add_smul]
    rw [h1]
    simp only [ENat.coe_add]
    apply add_le_add
    apply smul_le_ENat h
    exact h

lemma comp_equiv (n : ℕ) {p : α[X]} (hp : 1 ≤ p.trailingDegree) {a : α[X]}
  : nrel_poly α (n + 1) (a.comp p) (∑ i ∈ range (n + 1), (a.coeff i) • (p ^ i)) := by
  intro k hk
  simp [Polynomial.comp, Polynomial.eval₂, Polynomial.sum]
  have h {i : ℕ} : n < i → (p ^ i).coeff k = 0 := by
    intro hl
    have h1 : i ≤ (p^i).trailingDegree := by
      apply le_trans _ (trailingDegree_le_pow α p i)
      apply smul_le_ENat
      exact hp
    apply Polynomial.coeff_eq_zero_of_lt_trailingDegree
    have h2 : k < i := by
      linarith
    have h3 : (k : ℕ∞) < (i : ℕ∞) := by
      simp
      exact h2
    apply lt_of_lt_of_le h3 h1
  have h1 : (fun t : ℕ ↦ a.coeff t * (p ^ t).coeff k).support ⊆ range (n + 1) := by
    intro t ht
    simp
    simp at ht
    by_contra!
    have h2 : n < t := by
      linarith
    have h3 : (p ^ t).coeff k = 0 := by
      apply h h2
    simp [h3] at ht
  have h2 : (fun t : ℕ ↦ a.coeff t * (p ^ t).coeff k).support ⊆ a.support := by
    intro t ht
    simp
    simp at ht
    by_contra!
    simp [this] at ht
  have h3 : (fun t : ℕ ↦ a.coeff t * (p ^ t).coeff k).support.Finite := by
    apply Set.Finite.subset _ h1
    apply Finset.finite_toSet
  have h1' : h3.toFinset ⊆ range (n + 1) := by
    rw [Set.Finite.toFinset_subset]
    exact h1
  have h2' : h3.toFinset ⊆ a.support := by
    rw [Set.Finite.toFinset_subset]
    exact h2
  have h4 : ∑ x ∈ h3.toFinset, a.coeff x * (p ^ x).coeff k
    = ∑ x ∈ a.support, a.coeff x * (p ^ x).coeff k := by
    apply Finset.sum_subset
    simp [h2']
    intro _ _ hx2
    simp at hx2
    exact hx2
  have h5 : ∑ x ∈ h3.toFinset, a.coeff x * (p ^ x).coeff k
    = ∑ x ∈ range (n + 1), a.coeff x * (p ^ x).coeff k := by
    apply Finset.sum_subset
    simp [h1']
    intro _ _ hx2
    simp at hx2
    exact hx2
  rw [← h4, h5]

lemma comp_equiv_of_equiv  (n : ℕ) {p : α[X]} (hp : 1 ≤ p.trailingDegree) {a b : α[X]}
  : nrel_poly α (n + 1) a b → nrel_poly α (n + 1) (a.comp p) (b.comp p) := by
  have ha : nrel_poly α (n + 1) (a.comp p) (∑ i ∈ range (n + 1), (a.coeff i) • (p ^ i)) := by
    apply comp_equiv
    exact hp
  have hb : nrel_poly α (n + 1) (b.comp p) (∑ i ∈ range (n + 1), (b.coeff i) • (p ^ i)) := by
    apply comp_equiv
    exact hp
  have hab : nrel_poly α (n + 1) (a.comp p) (b.comp p) ↔ nrel_poly α (n + 1)
    (∑ i ∈ range (n + 1), (a.coeff i) • (p ^ i)) (∑ i ∈ range (n + 1), (b.coeff i) • (p ^ i)) := by
    rw [← EqGen_eq_poly α (n + 1)]
    rw [← EqGen_eq_poly α (n + 1)] at ha hb
    constructor
    · intro hl
      apply EqvGen.trans _ _ _ ha.symm _
      apply EqvGen.trans _ _ _ hl hb
    · intro hr
      apply EqvGen.trans _ _ _ ha _
      apply EqvGen.trans _ _ _ hr hb.symm
  rw [hab]
  intro hl
  intro k _
  simp
  apply Finset.sum_congr
  trivial
  intro x hx
  simp at hx
  congr 1
  apply hl
  exact hx


abbrev QPoly (n : ℕ) := RingQuot (nrel_poly α n)

abbrev pi_poly (n : ℕ) := RingQuot.mkAlgHom α (nrel_poly α n)

abbrev pi_mn_poly {m n : ℕ} (h : m ≤ n) : QPoly α n →ₐ[α] QPoly α m := by
  have h1 : ∀ ⦃x y : α[X]⦄, (nrel_poly α n) x y → pi_poly α m x = pi_poly α m y := by
    intro a b hab
    simp [mkAlgHom_def, mkRingHom_def, Quot.eq]
    simp at hab
    intro k hk
    apply hab
    linarith
  apply RingQuot.liftAlgHom α ⟨(pi_poly α m), h1⟩


@[simp]
lemma pi_comp_poly {m n : ℕ} (h : m ≤ n) ⦃f : α[X]⦄ : pi_mn_poly α h (pi_poly α n f)
  = pi_poly α m f := by
  simp

@[simp]
lemma quot_eq_poly (n : ℕ) {a b : α[X]} : pi_poly α n a = pi_poly α n b ↔ nrel_poly α n a b := by
  have ha : pi_poly α n a = ⟨Quot.mk (RingQuot.Rel (nrel_poly α n)) a⟩ := by
    simp [mkAlgHom_def, mkRingHom_def]
  have hb : pi_poly α n b = ⟨Quot.mk (RingQuot.Rel (nrel_poly α n)) b⟩ := by
    simp [mkAlgHom_def, mkRingHom_def]
  simp [ha, hb, Quot.eq]

lemma add_left_power (n : ℕ) : ∀ ⦃a b c : α⟦X⟧⦄, nrel_power α n a b → nrel_power α n (a + c) (b + c) := by
  intro a b c hab
  intro k hk
  simp
  rw [hab k]
  exact hk

lemma mul_left_power (n : ℕ) : ∀ ⦃a b c : α⟦X⟧⦄, nrel_power α n a b → nrel_power α n (a * c) (b * c) := by
  intro a b c hab
  intro k hk
  simp [coeff_mul]
  apply Finset.sum_congr
  simp
  intro ij hij
  simp at hij
  have h : ij.1 < n := by
    linarith
  have h1 : coeff α ij.1 a = coeff α ij.1 b := by
    apply hab
    exact h
  rw [h1]

lemma mul_right_power (n : ℕ) : ∀ ⦃a b c : α⟦X⟧⦄, nrel_power α n a b → nrel_power α n (c * a) (c * b) := by
  intro a b c hab
  intro k hk
  simp [coeff_mul]
  apply Finset.sum_congr
  simp
  intro ij hij
  simp at hij
  have h : ij.2 < n := by
    linarith
  have h1 : coeff α ij.2 a = coeff α ij.2 b := by
    apply hab
    exact h
  rw [h1]

@[simp]
lemma rel_eq_power (n : ℕ) : RingQuot.Rel (nrel_power α n) = nrel_power α n := by
  ext a b
  constructor
  · intro hl
    induction hl with
    | of h => exact h
    | add_left _ hplus => apply add_left_power; exact hplus
    | mul_left _ hmul1 => apply mul_left_power; exact hmul1
    | mul_right _ hmul2 => apply mul_right_power; exact hmul2
  · intro hr
    apply RingQuot.Rel.of
    exact hr

@[simp]
lemma EqGen_eq_power (n : ℕ) : EqvGen (nrel_power α n) = nrel_power α n := by
  ext a b
  constructor
  · intro hl
    induction hl with
    | rel _ _ h => exact h
    | refl _ => intro k _; rfl
    | symm _ _ _ h => intro k hk; apply Eq.symm; apply h; exact hk
    | trans _ _ _ _ _ hab hbc => intro k hk; apply Eq.trans; apply hab; exact hk; apply hbc; exact hk
  · intro hr
    apply EqvGen.rel
    exact hr

@[simp]
lemma rel_eq (n : ℕ) {a b : α[X]} : nrel_poly α n a b ↔ nrel_power α n a b := by
  constructor
  · intro hl
    intro k hk
    apply hl
    simp
    exact hk
  · intro hr
    intro k hk
    have ha : a.coeff k = coeff α k a := by simp
    have hb : b.coeff k = coeff α k b := by simp
    rw [ha, hb]
    apply hr
    exact hk

abbrev QPower (n : ℕ) := RingQuot (nrel_power α n)

abbrev pi_power (n : ℕ) := RingQuot.mkAlgHom α (nrel_power α n)

abbrev pi_mn_power {m n : ℕ} (h : m ≤ n) : QPower α n →ₐ[α] QPower α m := by
  have h1 : ∀ ⦃x y : α⟦X⟧⦄, (nrel_power α n) x y → pi_power α m x = pi_power α m y := by
    intro a b hab
    simp [mkAlgHom_def, mkRingHom_def, Quot.eq]
    simp at hab
    intro k hk
    apply hab
    linarith
  apply RingQuot.liftAlgHom α ⟨(pi_power α m), h1⟩


@[simp]
lemma pi_comp_power {m n : ℕ} (h : m ≤ n) ⦃f : α⟦X⟧⦄ : pi_mn_power α h (pi_power α n f)
  = pi_power α m f := by
  simp

@[simp]
lemma quot_eq_power (n : ℕ) {a b : α⟦X⟧} : pi_power α n a = pi_power α n b ↔ nrel_power α n a b := by
  have ha : pi_power α n a = ⟨Quot.mk (RingQuot.Rel (nrel_power α n)) a⟩ := by
    simp [mkAlgHom_def, mkRingHom_def]
  have hb : pi_power α n b = ⟨Quot.mk (RingQuot.Rel (nrel_power α n)) b⟩ := by
    simp [mkAlgHom_def, mkRingHom_def]
  simp [ha, hb, Quot.eq]

irreducible_def quot_map_pre (n : ℕ) : α[X] →ₐ[α] (QPower α n)
  := AlgHom.comp (pi_power α n) (Polynomial.coeToPowerSeries.algHom α)

@[simp]
lemma quot_map_pre_ker (n : ℕ) (x y : α[X]) : nrel_poly α n x y ↔ quot_map_pre α n x = quot_map_pre α n y := by
  simp [quot_map_pre_def]

irreducible_def quot_map (n : ℕ) : (QPoly α n) →ₐ[α] (QPower α n) := by
  have h :  ∀ ⦃x y : α[X]⦄, nrel_poly α n x y → (quot_map_pre α n) x = (quot_map_pre α n) y := by
    intro a b hab
    apply (quot_map_pre_ker α n a b).mp hab
  apply RingQuot.liftAlgHom α ⟨(quot_map_pre α n), h⟩

@[simp]
lemma comm_diagram (n : ℕ) {f : α[X]} : (quot_map α n) ((pi_poly α n) f)
  = (pi_power α n) (Polynomial.coeToPowerSeries.algHom α f) := by
  simp [quot_map_def,quot_map_pre]

@[simp]
lemma comm_diagram_mn {m n : ℕ} (h : m ≤ n) {f : QPoly α n} : (quot_map α m) ((pi_mn_poly α h) f)
  = (pi_mn_power α h) ((quot_map α n) f) := by
  have hsur_poly : Function.Surjective (pi_poly α n) := by
    apply RingQuot.mkAlgHom_surjective
  obtain ⟨a, ha⟩ := hsur_poly f
  rw [← ha]
  simp

@[simp]
lemma quot_map_bijective (n : ℕ) : Function.Bijective (quot_map α n) := by
  have hinj : Function.Injective (quot_map α n) := by
    intro a b hab
    have hsur_poly : Function.Surjective (pi_poly α n) := by
      apply RingQuot.mkAlgHom_surjective
    obtain ⟨a1, ha1⟩ := hsur_poly a
    obtain ⟨b1, hb1⟩ := hsur_poly b
    rw [← ha1, ← hb1]
    rw [← ha1, ← hb1] at hab
    simp [quot_map_def] at hab
    simp [quot_map_pre_def] at hab
    simp [pi_poly, mkAlgHom_def, mkRingHom_def, Quot.eq]
    exact hab
  have hsurj : Function.Surjective (quot_map α n) := by
    intro a
    have hsur_power : Function.Surjective (pi_power α n) := by
      apply RingQuot.mkAlgHom_surjective
    obtain ⟨a1, ha1⟩ := hsur_power a
    let pre_a : α[X] := ∑ i ∈ Finset.range n, (coeff α i a1) • Polynomial.X ^ i
    use (pi_poly α n) pre_a
    rw [comm_diagram α n, ← ha1]
    simp
    intro k hk
    simp [pre_a]
    simp [hk]
  trivial

irreducible_def quot_iso (n : ℕ) : (QPoly α n) ≃ₐ[α] (QPower α n)
  := AlgEquiv.ofBijective (quot_map α n) (quot_map_bijective α n)

lemma local_eq {f g : α⟦X⟧} : f = g ↔ ∀ n : ℕ, pi_power α (n + 1) f = pi_power α (n + 1) g := by
  constructor
  · intro hl
    intro n
    simp [hl]
  · intro hr
    simp at hr
    ext k
    apply hr (k + 1)
    linarith

def toLocallyFinite {fs : ℕ → α⟦X⟧} (hfs : ∀ n : ℕ, n ≤ (fs n).order) : locally_finite ℕ ℕ α where
  funs := fun n : ℕ ↦ (fun i : ℕ ↦ coeff α i (fs n))
  locally_finite := by
    intro i
    have h : {a | (fun n i ↦ (coeff α i) (fs n)) a i ≠ 0} ⊆ {a | a ≤ i} := by
      intro n hn
      simp
      simp at hn
      have h1 : (fs n).order ≤ i := by
        apply PowerSeries.order_le
        trivial
      rw [← PartENat.coe_le_coe]
      apply le_trans (hfs n) h1
    observe h1 : {a | a ≤ i}.Finite
    apply Set.Finite.subset h1 h

end InverseLimit

open PartENat

section TruncatedFilter

def FPower (α : Type _) [CommSemiring α] (n : ℕ) : Ideal α⟦X⟧ where
  carrier := {f : α⟦X⟧ | n ≤ f.order}
  add_mem' := by
    intro a b ha hb
    simp at ha hb
    simp
    have h2 : min a.order b.order ≤ (a + b).order := by
      apply PowerSeries.le_order_add a b
    apply le_trans _ h2
    apply le_min ha hb
  zero_mem' := by
    simp
  smul_mem' := by
    intro c a ha
    simp
    simp at ha
    have h : c.order + a.order ≤ (c * a).order := by
      apply order_mul_ge
    apply le_trans _ h
    have h1 : (0 : PartENat) + (n : PartENat) ≤ c.order + a.order := by
      apply add_le_add
      simp
      apply ha
    apply le_trans _ h1
    simp

instance {α : Type _} [CommSemiring α] {n : ℕ} : AddCommMonoid (↑ {f : α⟦X⟧ | n ≤ f.order})
  := (FPower α n).addCommMonoid

instance instFPowerModule {α : Type _} [CommSemiring α] {n : ℕ} : Module α⟦X⟧ (↑ {f : α⟦X⟧ | n ≤ f.order})
  := Submodule.module (FPower α n)

instance {α : Type _} [CommSemiring α] {n : ℕ} : Mul (↑ {f : α⟦X⟧ | n ≤ f.order}) where
  mul f g := f.1 • g

@[simp]
lemma subtype_mul_eq_smul {α : Type _} [CommSemiring α] {n : ℕ} {f g : ↑ {f : α⟦X⟧ | n ≤ f.order}}
  : (f * g).1 = f.1 * g.1 := by
  trivial

end TruncatedFilter

variable {α : Type _} [CommSemiring α]

@[simp]
lemma order_pow_ge (p : α⟦X⟧) (n : ℕ) : n • p.order ≤ (p ^ n).order :=
  match n with
  | 0 => by simp
  | n + 1 => by
    simp [pow_succ]
    have h : n • p.order ≤ (p ^ n).order := by
      apply order_pow_ge p n
    have h1 : (n + 1) • p.order = n • p.order + p.order := by
      trivial
    rw [h1]
    have h2 : (p ^ n).order + p.order ≤ (p ^ n * p).order := by
      apply order_mul_ge
    apply le_trans _ h2
    apply add_le_add
    exact h
    trivial

@[simp]
lemma order_smul_ge (c : α) (p : α⟦X⟧) : p.order ≤ (c • p).order := by
  by_cases h : p.order = ⊤
  ·
    observe h1 : p = 0
    have h2 : (c • p) = 0 := by
      rw [h1]
      simp
    rw [h2, h1]
  ·
    observe h1 : p.order < ⊤
    have h2 : p.order.Dom := by
      apply PartENat.dom_of_lt h1
    let n := p.order.get h2
    have h3 : n = p.order := by
      simp [n]
    rw [← h3]
    apply PowerSeries.nat_le_order (c • p) n
    intro i hi
    simp
    have h4 : coeff α i p = 0 := by
      apply coeff_of_lt_order
      rw [← h3]
      simp [hi]
    simp [h4]

@[simp]
lemma smul_le {a : PartENat} {n : ℕ} (h : 1 ≤ a) : n ≤ n • a :=
  match n with
  | 0 => by simp
  | n + 1 => by
    simp
    have h1 : (n + 1) • a = n • a + a := by
      trivial
    rw [h1]
    apply add_le_add
    apply smul_le h
    exact h

def eval_pre (p : ↑ {f : α⟦X⟧ | 1 ≤ f.order}) (c : α⟦X⟧) : locally_finite ℕ ℕ α := by
  let fs := fun n : ℕ ↦ (coeff α n c) • (p.1 ^ n)
  have hfs : ∀ n : ℕ, n ≤ (fs n).order := by
    intro n
    simp [fs]
    have h : (p.1 ^ n).order ≤ ((coeff α n) c • p.1 ^ n).order := by
      simp
    apply le_trans _ h
    apply le_trans _ (order_pow_ge p.1 n)
    apply smul_le p.2
  apply toLocallyFinite α hfs

def eval_map (p : ↑ {f : α⟦X⟧ | 1 ≤ f.order}) (c : α⟦X⟧) : α⟦X⟧ := PowerSeries.mk (hsum (eval_pre p c))

@[simp]
lemma eval_coeff (p : ↑ {f : α⟦X⟧ | 1 ≤ f.order}) (c : α⟦X⟧) {n N : ℕ} (hmn : n < N) : coeff α n (eval_map p c)
  = ∑ i ∈ Finset.range N, (coeff α i c) * (coeff α n (p.1 ^ i)) := by
  simp [eval_map]
  have h : ((eval_pre p c).locally_finite n).toFinset ⊆ Finset.range N := by
    intro i hi
    simp at hi
    simp
    have h1 : coeff α n (p.1 ^ i) ≠ 0 := by
      by_contra!
      have h2 : (coeff α i) c * (coeff α n) (p ^ i) = 0 := by
        rw [this]
        simp
      contradiction
    have h2 : (p.1 ^ i).order ≤ n := by
      apply order_le
      exact h1
    have h3 : i ≤ (n : PartENat) := by
      apply le_trans _ h2
      apply le_trans _ (order_pow_ge p.1 i)
      apply smul_le p.2
    rw [PartENat.coe_le_coe] at h3
    linarith
  have h1 : ∑ a ∈ ((eval_pre p c).locally_finite n).toFinset, (eval_pre p c).funs a n
    = ∑ a ∈ Finset.range N, (eval_pre p c).funs a n := by
    apply Finset.sum_subset h
    intro _ _
    simp
  rw [h1]
  simp [eval_pre, toLocallyFinite]

lemma eval_coeff₂ (p : ↑ {f : α⟦X⟧ | 1 ≤ f.order}) (c : α⟦X⟧) {n : ℕ} : coeff α n (eval_map p c)
  = ∑ i ∈ Finset.range (n + 1), (coeff α i c) * (coeff α n (p.1 ^ i)) := by
  observe h : n < n + 1
  apply eval_coeff p c h

@[simp]
lemma eval_equiv_local_pre (p : ↑ {f : α⟦X⟧ | 1 ≤ f.order}) (c : α⟦X⟧) (n : ℕ)
  : pi_power α n (eval_map p c) = pi_power α n (∑ i ∈ Finset.range n, (coeff α i c) • (p.1 ^ i)) := by
  simp only [quot_eq_power]
  intro k hk
  simp
  apply eval_coeff p c _
  linarith

@[simp]
lemma eval_equiv_local (p : ↑ {f : α⟦X⟧ | 1 ≤ f.order}) (c : α⟦X⟧) (n : ℕ)
  : pi_power α n (eval_map p c)
  = quot_iso α n (pi_poly α n ((c.trunc n).comp (p.1.trunc n))) := by
  let pp := p.1.trunc n
  let cp := c.trunc n
  have h : cp.comp pp = ∑ i ∈ cp.support, (cp.coeff i) • (pp ^ i) := by
    simp [Polynomial.comp, Polynomial.eval₂, Polynomial.sum]
    apply sum_congr
    trivial
    intro i _
    ext k
    simp
  simp [h]
  simp [quot_iso]
  have h1 : cp.support ⊆ range n := by
    intro i hi
    simp [cp, PowerSeries.coeff_trunc] at hi
    simp
    linarith
  have h2 : ∑ x ∈ cp.support, cp.coeff x • (pi_power α n) ↑pp ^ x
    = ∑ x ∈ range n, cp.coeff x • (pi_power α n) ↑pp ^ x := by
    apply Finset.sum_subset h1
    intro i hi1 hi2
    simp at hi1 hi2
    simp [hi2]
  rw [h2]
  apply sum_congr
  trivial
  intro i hi
  simp at hi
  have h3 : (coeff α i) c = cp.coeff i := by
    simp [cp, PowerSeries.coeff_trunc, if_pos hi]
  rw [h3]
  congr 2
  simp
  intro k hk
  simp [pp, PowerSeries.coeff_trunc, if_pos hk]

def eval₂ (p : ↑ {f : α⟦X⟧ | 1 ≤ f.order}) : α⟦X⟧ →ₐ[α] α⟦X⟧ where
  toFun c := eval_map p c
  map_zero' := by
    ext n
    simp [eval_coeff₂]
    apply Finset.sum_eq_zero
    intro k _
    have h : (coeff α k) 0 = 0 := by
      have h1 : PowerSeries.C α (0 : α) = (0 : α⟦X⟧) := by
        simp
      rw [← h1]
      have h2 : (coeff α k) ((C α) 0) = if k = 0 then 0 else 0 := by
        apply PowerSeries.coeff_C k (0 : α)
      rw [h2]
      simp
    simp [h]

  map_one' := by
    ext k
    simp [eval_coeff₂]

  map_add' := by
    intro a b
    simp [local_eq]
    intro n
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr
    trivial
    intro k hk
    simp at hk
    apply add_smul

  map_mul' := by
    intro a b
    rw [local_eq]
    intro n
    simp only [eval_equiv_local]
    simp only [map_mul]
    simp only [eval_equiv_local]
    simp only [← map_mul]
    congr 1
    have h : ((trunc (n + 1) a) * (trunc (n + 1) b)).comp (trunc (n + 1) p)
        = (trunc (n + 1) a).comp (trunc (n + 1) p) * (trunc (n + 1) b).comp (trunc (n + 1) p) := by
      apply Polynomial.mul_comp
    rw [← h]
    simp only [quot_eq_poly]
    apply comp_equiv_of_equiv
    by_contra!
    have h1 : (trunc (n + 1) p.1).trailingDegree = 0 := by
      apply ENat.lt_one_iff_eq_zero.mp this
    rw [Polynomial.trailingDegree_eq_zero] at h1
    rw [PowerSeries.coeff_trunc] at h1
    simp [if_pos] at h1
    have h2 : (coeff α 0) p = 0 := by
      apply PowerSeries.coeff_of_lt_order
      apply lt_of_lt_of_le _ p.2
      simp
    simp at h2
    contradiction
    intro k hk
    rw [PowerSeries.coeff_trunc]
    simp [if_pos hk]
    rw [PowerSeries.coeff_mul]
    rw [Polynomial.coeff_mul]
    apply Finset.sum_congr
    trivial
    intro ij hij
    simp at hij
    rw [PowerSeries.coeff_trunc]
    rw [PowerSeries.coeff_trunc]
    have h3 : ij.1 < n + 1 := by
      linarith
    have h4 : ij.2 < n + 1 := by
      linarith
    simp [if_pos h3]
    simp [if_pos h4]


  commutes' := by
    intro r
    simp only [local_eq]
    intro n
    have h : Algebra.toRingHom r = (PowerSeries.C α r) := by
      trivial
    simp only [algebraMap]
    rw [h]
    simp only [eval_equiv_local]
    simp [quot_iso, comm_diagram]


lemma eval_coeff₃ (p : ↑ {f : α⟦X⟧ | 1 ≤ f.order}) (c : α⟦X⟧) {n : ℕ} : coeff α n (eval₂ p c)
  = ∑ᶠ i : ℕ, (coeff α i c) * (coeff α n (p.1 ^ i)) := by
  have h : coeff α n (eval₂ p c) = ∑ i ∈ Finset.range (n + 1), (coeff α i c) * (coeff α n (p.1 ^ i)) := by
    apply eval_coeff₂ p c
  rw [h]
  have h1 : ∑ᶠ i : ℕ, (coeff α i c) * (coeff α n (p.1 ^ i))
    = ∑ i ∈ Finset.range (n + 1), (coeff α i c) * (coeff α n (p.1 ^ i)) := by
    apply finsum_eq_finset_sum_of_support_subset
    intro k hk
    simp
    simp at hk
    have h1 : (coeff α n) (p ^ k) ≠ 0 := by
      by_contra!
      rw [this] at hk
      simp at hk
    have h2 : (p.1 ^ k).order ≤ n := by
      apply order_le
      exact h1
    have h3 : k ≤ (n : PartENat) := by
      apply le_trans _ h2
      apply le_trans _ (order_pow_ge p.1 k)
      apply smul_le p.2
    rw [PartENat.coe_le_coe] at h3
    linarith
  simp [h1]

lemma ringHom_preserve_order_pf {β : Type _} [CommSemiring β] (comp : α →+* β) {n : ℕ}
  (p : ↑ {f : α⟦X⟧ | n ≤ f.order}) : n ≤ (PowerSeries.map comp (p.1)).order := by
  apply PowerSeries.nat_le_order
  intro i hi
  simp
  have h : ∀ k : ℕ, k < n → coeff α k p.1 = 0 := by
    intro k hk
    apply PowerSeries.coeff_of_lt_order
    have h1 : (k : PartENat) < n := by
      simp
      exact hk
    apply lt_of_lt_of_le h1
    exact p.2
  have h1 : coeff α i p.1 = 0 := by
    apply h
    exact hi
  simp [h1]

def ringHom_preserve_order {β : Type _} [CommSemiring β] (comp : α →+* β) {n : ℕ}
  : ↑ {f : α⟦X⟧ | n ≤ f.order} → ↑ {f : β⟦X⟧ | n ≤ f.order}
  := fun p ↦ ⟨PowerSeries.map comp (p.1), ringHom_preserve_order_pf comp p⟩

lemma eval_comp_eq {β : Type _} [CommSemiring β] (comp : α →+* β) (p : ↑ {f : α⟦X⟧ | 1 ≤ f.order})
  : (PowerSeries.map comp) ∘ (eval₂ p)
    = (eval₂ (ringHom_preserve_order comp p)) ∘ (PowerSeries.map comp) := by
  funext f
  ext k
  simp [eval₂, eval_coeff₂]
  apply Finset.sum_congr
  trivial
  intro i hi
  simp at hi
  congr
  simp [ringHom_preserve_order]
  rw [← map_pow]
  simp only [PowerSeries.coeff_map]

@[simp]
lemma eval_constantCoeff (p : ↑ {f : α⟦X⟧ | 1 ≤ f.order}) (c : α⟦X⟧) : coeff α 0 (eval₂ p c) = coeff α 0 c := by
  simp only [eval₂]
  simp [eval_coeff₂ p c]

@[simp]
lemma eval_coeff_X  (p : ↑ {f : α⟦X⟧ | 1 ≤ f.order}) : eval₂ p X = p.1 := by
  simp only [eval₂]
  ext n
  simp [eval_coeff₂ p X]
  have h {i : ℕ} : (coeff α i) X = if i = 1 then 1 else 0 := by
    simp [PowerSeries.X_eq, PowerSeries.coeff_monomial]
  simp [h]
  intro hl
  rw [hl]
  have hr : (coeff α 0) p = 0 := by
    apply PowerSeries.coeff_of_lt_order
    simp
    apply lt_of_lt_of_le _ p.2
    simp
  simp [hr]

@[simp]
lemma eval_C {p : ↑ {f : α⟦X⟧ | 1 ≤ f.order}} {r : α} : eval₂ p (PowerSeries.C α r) = (PowerSeries.C α r) := by
  simp only [eval₂]
  ext n
  simp [eval_coeff₂]
  have h {i : ℕ} : (coeff α i) (PowerSeries.C α r) = if i = 0 then r else 0 := by
    rw [← PowerSeries.monomial_zero_eq_C_apply]
    apply PowerSeries.coeff_monomial
  simp [h]

lemma eval₂_inj_field {α : Type _} [Field α] (p : ↑ {f : α⟦X⟧ | 1 ≤ f.order}) (hp : p.1 ≠ 0)
  : Function.Injective (eval₂ p) := by
  rw [injective_iff_map_eq_zero]
  let rec h (n : ℕ) : ∀ k ≤ n, ∀ a : α⟦X⟧, eval₂ p a = 0 → coeff α k a = 0 := by
    by_cases hn : n = 0
    ·
      intro k hk a ha
      have h1 : k = 0 := by linarith
      rw [h1]
      rw [← eval_constantCoeff p]
      rw [ha]
      simp
    ·
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
      intro k hk a ha
      have h1 : coeff α 0 a = 0 := by
        apply h 0
        trivial
        exact ha
      simp at h1
      rw [← PowerSeries.X_dvd_iff] at h1
      obtain ⟨b, hb⟩ := h1
      have h2 : eval₂ p a = (eval₂ p X) * (eval₂ p b) := by
        simp [hb]
      rw [eval_coeff_X] at h2
      have h3 : (eval₂ p b) = 0 := by
        rw [ha] at h2
        apply eq_zero_of_ne_zero_of_mul_left_eq_zero hp
        simp [h2]
      have h4 : ∀ t ≤ m, coeff α t b = 0 := by
        intro t ht
        apply h m t ht b h3
      by_cases hh1 : k = 0
      · rw [hh1]
        apply h 0
        trivial
        exact ha
      ·
        obtain ⟨kk, hkk⟩ := Nat.exists_eq_succ_of_ne_zero hh1
        simp at hkk
        rw [hkk]
        rw [hb]
        simp
        apply h4 kk
        linarith

  intro a ha
  ext n
  simp
  apply h n n _ a ha
  trivial

lemma eval_inj {β : Type _} [Field β] [Algebra α β] (hmap : Function.Injective (algebraMap α β))
   (p : ↑ {f : α⟦X⟧ | 1 ≤ f.order}) (hp : p.1 ≠ 0)
  : Function.Injective (eval₂ p) := by
  intro a b hab
  have h : Function.Injective ((map (algebraMap α β))) := by
    intro f g hfg
    ext k
    apply hmap
    rw [← PowerSeries.coeff_map, ← PowerSeries.coeff_map]
    rw [hfg]
  have h1 : (map (algebraMap α β)) p.1 ≠ 0 := by
    have h2 : (map (algebraMap α β)) 0 = 0 := by
      simp
    rw [← h2]
    by_contra!
    have h3 : p.1 = 0 := by
      apply h
      exact this
    contradiction
  apply h
  apply eval₂_inj_field (ringHom_preserve_order (algebraMap α β) p) h1
  have h2a : (eval₂ (ringHom_preserve_order (algebraMap α β) p)) ((map (algebraMap α β)) a)
    =(eval₂ (ringHom_preserve_order (algebraMap α β) p) ∘ (map (algebraMap α β))) a := by
    simp
  have h2b : (eval₂ (ringHom_preserve_order (algebraMap α β) p)) ((map (algebraMap α β)) b)
    =(eval₂ (ringHom_preserve_order (algebraMap α β) p) ∘ (map (algebraMap α β))) b := by
    simp
  rw [← eval_comp_eq (algebraMap α β) p] at h2a h2b
  rw [h2a, h2b]
  simp only [Function.comp_apply]
  rw [hab]

end PowerSeries

namespace LaurentSeries


section Evaluation

open PowerSeries

open WithTop

open PartENat

variable {R : Type _} [CommSemiring R]

instance : Algebra R (LaurentSeries R) := HahnSeries.instAlgebra

def LowerTruncated (n : ℤ) (f : LaurentSeries R) := ∀ k < n, f.coeff k = 0

@[simp]
lemma lower_truncated_coeff {n : ℤ} {f : LaurentSeries R} (hf : LowerTruncated n f) : ∀ k : ℤ, f.coeff k ≠ 0 → n ≤ k := by
  intro k hk
  by_contra!
  have h : f.coeff k = 0 := by
    apply hf
    exact this
  contradiction

lemma lower_truncated_subset {m n : ℤ} (h : m ≤ n) {f : LaurentSeries R} : LowerTruncated n f → LowerTruncated m f := by
  intro hl
  intro k hk
  apply hl
  linarith

@[simp]
lemma lower_truncated_by_order {n : ℤ} {f : LaurentSeries R} : LowerTruncated n f ↔ n ≤ f.orderTop := by
  constructor
  · intro hl
    by_contra!
    obtain ⟨i, hi1, hi2⟩ := WithTop.lt_iff_exists_coe.mp this
    have h : f.coeff i ≠ 0 := by
      apply HahnSeries.coeff_orderTop_ne
      exact hi1
    have h1 : n ≤ i := by
      apply lower_truncated_coeff hl i h
    rw [WithTop.coe_lt_coe] at hi2
    linarith
  ·
    intro hr k hk
    have h : k < f.orderTop := by
      rw [← WithTop.coe_lt_coe] at hk
      apply lt_of_le_of_lt' hr hk
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop h

def order_coe_fun := (WithTop.map (fun t : ℕ ↦ (t : ℤ))) ∘ PartENat.withTopOrderIso

lemma order_coe_fun_le_iff : ∀ ⦃a b : PartENat⦄, order_coe_fun a ≤ order_coe_fun b ↔ a ≤ b := by
  intro a b
  simp [order_coe_fun]
  have h : StrictMono (WithTop.map (fun t : ℕ ↦ (t : ℤ))) := by
    apply StrictMono.withTop_map
    intro t1 t2 ht
    simp
    exact ht
  rw [StrictMono.le_iff_le h]
  rw [OrderIsoClass.map_le_map_iff PartENat.withTopOrderIso]

lemma order_coe_inj : Function.Injective order_coe_fun := by
  intro a b hab
  have h1 : order_coe_fun a ≤ order_coe_fun b := by simp [hab]
  have h2 : a ≤ b := by
    rw [← order_coe_fun_le_iff]
    exact h1
  have h3 : order_coe_fun b ≤ order_coe_fun a := by simp [hab]
  have h4 : b ≤ a := by
    rw [← order_coe_fun_le_iff]
    exact h3
  apply le_antisymm h2 h4

def order_coe : PartENat ↪o WithTop ℤ where
  toFun := order_coe_fun
  map_rel_iff' := by
    intro a b
    apply order_coe_fun_le_iff

  inj' := order_coe_inj


instance : Coe (PartENat) (WithTop ℤ) where
  coe := order_coe

@[simp]
lemma order_coe_top : order_coe ⊤ = ⊤ := by
  simp [order_coe, order_coe_fun]
  apply WithTop.map_top

@[simp]
lemma order_eq_natCast {n : ℕ} : order_coe n = n := by
  simp [order_coe, order_coe_fun, withTopOrderIso]
  have h : WithTop.map (fun t : ℕ ↦ (t : ℤ)) (n : ℕ∞) = (n : ℤ) := by
    apply WithTop.map_coe
  rw [h]
  simp

@[simp]
lemma ofPowerSeries_order_eq {f : R⟦X⟧} : f.order = (f : LaurentSeries R).orderTop := by
  by_cases h : f = 0
  · rw [h]
    simp
  ·
    have h1 : f.order.Dom := by
      apply PowerSeries.order_finite_iff_ne_zero.mpr
      simp [h]
    let natOrder := f.order.get h1
    have h2 : natOrder = f.order := by
      apply PartENat.natCast_get
    have h3 : PowerSeries.coeff R natOrder f ≠ 0 := by
      apply PowerSeries.coeff_order
    have h4 : ∀ i : ℕ, i < natOrder → PowerSeries.coeff R i f = 0 := by
      intro i hi
      apply PowerSeries.coeff_of_lt_order
      rw [← h2]
      simp
      exact hi
    have h5 : (f : LaurentSeries R).orderTop ≤ natOrder := by
      apply HahnSeries.orderTop_le_of_coeff_ne_zero
      simp
      exact h3
    have h6 : ∀ i : ℤ, i < natOrder → (f : LaurentSeries R).coeff i = 0 := by
      intro i hi
      by_cases h7 : 0 ≤ i
      ·
        have h8 : i.toNat = i := by
          simp [h7]
        rw [← h8]
        simp [HahnSeries.ofPowerSeries_apply_coeff]
        apply h4
        rw [← h8] at hi
        simp at hi
        exact hi
      ·
        simp [HahnSeries.ofPowerSeries]
        apply HahnSeries.embDomain_notin_range
        simp
        linarith
    have h7 : natOrder ≤ (f : LaurentSeries R).orderTop := by
      by_contra!
      have h8 : (f : LaurentSeries R).orderTop ≠ ⊤ := by
        apply ne_top_of_lt this
      let order? := WithTop.untop (f : LaurentSeries R).orderTop h8
      have h9 : order? = (f : LaurentSeries R).orderTop := by
        apply WithTop.coe_untop
      have h10 : (f : LaurentSeries R).coeff order? ≠ 0 := by
        apply HahnSeries.coeff_orderTop_ne
        simp [h9]
      rw [← h9] at this
      have h11 : order? < natOrder := by
        rw [← WithTop.coe_lt_coe]
        simp [this]
      have h12 : (f : LaurentSeries R).coeff order? = 0 := by
        apply h6
        exact h11
      contradiction
    have h8 : natOrder = (f : LaurentSeries R).orderTop := by
      apply le_antisymm h7 h5
    rw [← h8]
    rw [← h2]
    simp

@[simp]
lemma ofPowerSeries_order_le_iff_le {f : R⟦X⟧} {n : ℕ} : n ≤ f.order ↔ n ≤ (f : LaurentSeries R).orderTop := by
  constructor
  · intro hl
    rw [← ofPowerSeries_order_eq]
    rw [← order_eq_natCast]
    rw [order_coe.map_rel_iff]
    exact hl
  · intro hr
    rw [← order_coe.map_rel_iff]
    rw [order_eq_natCast]
    rw [ofPowerSeries_order_eq]
    exact hr

lemma in_range_ofPowerSeries_pre {f : LaurentSeries R} : LowerTruncated 0 f ↔ ∃ p : R⟦X⟧, p = f := by
  constructor
  · intro hl
    let p := PowerSeries.mk (fun n : ℕ ↦ f.coeff n)
    use p
    ext k
    by_cases hk : 0 ≤ k
    ·
      have h : k.toNat = k := by
        simp [hk]
      rw [← h]
      simp [HahnSeries.coeff_toPowerSeries]
      simp [p]
    · simp at hk
      have h : f.coeff k = 0 := by
        apply hl
        exact hk
      rw [h]
      apply HahnSeries.embDomain_notin_range
      simp
      exact hk
  · intro hr
    obtain ⟨p, hp⟩ := hr
    simp [lower_truncated_by_order]
    rw [← hp, ← ofPowerSeries_order_eq]
    have h : order_coe (0 : PartENat) = 0 := by
      simp [order_coe, order_coe_fun, withTopOrderIso]
    rw [← h]
    rw [order_coe.map_rel_iff]
    simp

lemma in_range_ofPowerSeries {f : LaurentSeries R} : LowerTruncated 0 f ↔ ∃! p : R⟦X⟧, p = f := by
  constructor
  ·
    intro hl
    obtain ⟨p, hp⟩ := in_range_ofPowerSeries_pre.mp hl
    use p
    simp [hp, ← local_eq]
    intro q hq
    rw [← hp] at hq
    have h : Function.Injective (HahnSeries.ofPowerSeries ℤ R) := by
      apply HahnSeries.ofPowerSeries_injective
    apply h
    exact hq
  · intro hr
    apply in_range_ofPowerSeries_pre.mpr
    obtain ⟨p, hp⟩ := hr
    use p
    simp [hp.1]

@[simp]
lemma ofPowerSeries_range : Set.range (HahnSeries.ofPowerSeriesAlg ℤ R)
  = {f : LaurentSeries R | LowerTruncated 0 f} := by
  ext f
  constructor
  · intro hl
    simp at hl
    simp
    obtain ⟨p, hp⟩ := hl
    have h : p.order = f.orderTop := by
      rw [← hp]
      apply ofPowerSeries_order_eq
    rw [← h]
    have h1 : order_coe (0 : PartENat) = 0 := by
      apply order_eq_natCast
    rw [← h1]
    rw [order_coe.map_rel_iff]
    simp
  · intro hr
    have h : LowerTruncated 0 f := by apply hr
    obtain ⟨p, hp⟩ := in_range_ofPowerSeries.mp h
    simp
    use p
    have h1 : (HahnSeries.ofPowerSeries ℤ R) p = f := by
      apply hp.1
    apply h1

@[simp]
lemma ofPowerSeriesAlg_coeff_pre {p : R⟦X⟧} {n : ℕ} : ((HahnSeries.ofPowerSeriesAlg ℤ R) p).coeff n
  = PowerSeries.coeff R n p := by
  have h : (HahnSeries.ofPowerSeriesAlg ℤ R) p = p := by
    trivial
  rw [h]
  simp [HahnSeries.ofPowerSeries_apply_coeff]

@[simp]
lemma ofPowerSeriesAlg_coeff_pre₂ {p : R⟦X⟧} {n : ℤ} (h : n < 0)
  : ((HahnSeries.ofPowerSeriesAlg ℤ R) p).coeff n = 0 := by
  have h1 : (HahnSeries.ofPowerSeriesAlg ℤ R) p = p := by
    trivial
  simp [h1]
  simp [HahnSeries.ofPowerSeries]
  apply HahnSeries.embDomain_notin_range
  simp [h]

@[simp]
lemma ofPowerSeriesAlg_coeff {p : R⟦X⟧} {n : ℤ}
  : ((HahnSeries.ofPowerSeriesAlg ℤ R) p).coeff n = if 0 ≤ n then PowerSeries.coeff R n.toNat p else 0 := by
  by_cases h : 0 ≤ n
  ·
    have h1 : n.toNat = n := by simp [h]
    simp only [if_pos h]
    rw [← h1]
    apply ofPowerSeriesAlg_coeff_pre
  · simp only [if_neg h]
    simp at h
    apply ofPowerSeriesAlg_coeff_pre₂ h

@[simp]
lemma ofPowerSeriesAlg_eq {p : R⟦X⟧} : HahnSeries.ofPowerSeriesAlg ℤ R p = HahnSeries.ofPowerSeries ℤ R p := by
  ext n
  rw [ofPowerSeriesAlg_coeff]
  by_cases h : 0 ≤ n
  ·
    have h1 : n.toNat = n := by simp [h]
    rw [← h1]
    simp [if_pos h]
  ·
    simp [if_neg h]
    have h1 : ((HahnSeries.ofPowerSeries ℤ R) p).coeff n = 0 := by
      simp [HahnSeries.ofPowerSeries]
      apply HahnSeries.embDomain_notin_range
      simp [h]
    simp [h1]

lemma in_range_ofPowerSeries_trunc {p : LaurentSeries R} {n : ℕ}
  : p ∈ {f : LaurentSeries R | LowerTruncated n f} ↔ ∃! g : R⟦X⟧, g = p ∧ n ≤ g.order := by
  constructor
  · intro hl
    have h : LowerTruncated 0 p := by
      apply lower_truncated_subset _ hl
      simp
    obtain ⟨⟨g, hg⟩, hhg⟩ := Classical.unique (in_range_ofPowerSeries.mp h)
    use g
    have h1 : ∀ (y : R⟦X⟧), (fun g ↦ (HahnSeries.ofPowerSeries ℤ R) g = p ∧ ↑n ≤ g.order) y → y = g := by
      intro y hy
      have h2 : (HahnSeries.ofPowerSeries ℤ R) y = (HahnSeries.ofPowerSeries ℤ R) g → y = g := by
        apply HahnSeries.ofPowerSeries_injective
      apply h2
      rw [hg, hy.1]
    have h2 :  (fun g ↦ (HahnSeries.ofPowerSeries ℤ R) g = p ∧ ↑n ≤ g.order) g := by
      simp [hg]
      simp at hl
      simp [hl]
    simp [h2]
    intro y hy hy1
    apply h1
    rw [hy]
    rw [ofPowerSeries_order_le_iff_le]
    trivial
  · intro hr
    obtain ⟨⟨g, hg⟩,hgg⟩ := Classical.unique hr
    simp
    rw [← hg.1]
    rw [← ofPowerSeries_order_le_iff_le]
    simp [hg.2]

@[simp]
lemma ofPowerSeries_range_trunc {n : ℕ} : (HahnSeries.ofPowerSeriesAlg ℤ R) '' {f : R⟦X⟧ | n ≤ f.order}
  = {f : LaurentSeries R | LowerTruncated n f} := by
  ext p
  constructor
  · intro hl
    simp at hl
    simp
    obtain ⟨g, hg1, hg2⟩ := hl
    rw [← hg2]
    simp [hg1]
  · intro hr
    simp
    obtain ⟨⟨g, hg1⟩, _⟩ := Classical.unique (in_range_ofPowerSeries_trunc.mp hr)
    use g
    simp [hg1.1]
    rw [← hg1.1]
    rw [← ofPowerSeries_order_le_iff_le]
    simp [hg1.2]

def ofPowerSeries₂ (R : Type _) [CommSemiring R] (f : R⟦X⟧) : ↑ {f : LaurentSeries R | LowerTruncated 0 f}
  := by
  use (HahnSeries.ofPowerSeriesAlg ℤ R) f
  rw [← ofPowerSeries_range]
  apply Set.mem_range_self

lemma ofPowerSeries₂_bijective (R : Type _) [CommSemiring R] : Function.Bijective
  (ofPowerSeries₂ R) := by
  rw [Function.bijective_iff_existsUnique]
  intro ⟨a, ha⟩
  have h : LowerTruncated 0 a := by apply ha
  rw [in_range_ofPowerSeries] at h
  obtain ⟨⟨g, hg1⟩, hg2⟩ := Classical.unique h
  use g
  simp [hg1, ofPowerSeries₂]
  intro y hy
  rw[← hg1] at hy
  apply HahnSeries.ofPowerSeries_injective hy

def ofPowerSeries_trunc (R : Type _) [CommSemiring R] (n : ℕ) (f : ↑ {f : R⟦X⟧ | n ≤ f.order})
  : ↑ {f : LaurentSeries R | LowerTruncated n f}
  := by
  use (HahnSeries.ofPowerSeriesAlg ℤ R) f.1
  rw [← ofPowerSeries_range_trunc]
  apply Set.mem_image_of_mem
  apply f.2

lemma ofPowerSeries_bijective_trunc (R : Type _) [CommSemiring R] (n : ℕ) : Function.Bijective
  (ofPowerSeries_trunc R n) := by
  rw [Function.bijective_iff_existsUnique]
  intro ⟨a, ha⟩
  rw [in_range_ofPowerSeries_trunc] at ha
  obtain ⟨⟨g, hg1, hg2⟩,hgg⟩ := Classical.unique ha
  use ⟨g, hg2⟩
  simp [hg1, ofPowerSeries_trunc]
  intro b _ hb2
  rw [← hg1] at hb2
  apply HahnSeries.ofPowerSeries_injective hb2


@[simp]
lemma lower_truncated_add {m n : ℤ} {f g : LaurentSeries R} (hf : LowerTruncated m f) (hg : LowerTruncated n g)
  : LowerTruncated (min m n) (f + g) := by
  intro k hk
  have h1 : k < m := by
    apply lt_of_lt_of_le hk
    simp
  have h2 : k < n := by
    apply lt_of_lt_of_le hk
    simp
  have hf : f.coeff k = 0 := by
    apply hf
    exact h1
  have hg : g.coeff k = 0 := by
    apply hg
    exact h2
  simp [hf, hg]

@[simp]
lemma lower_truncated_mul {m n : ℤ} {f g : LaurentSeries R} (hf : LowerTruncated m f) (hg : LowerTruncated n g)
  : LowerTruncated (m + n) (f * g) := by
  simp
  simp at hf hg
  have hr : f.orderTop + g.orderTop ≤ (f * g).orderTop := by
    apply HahnSeries.orderTop_add_orderTop_le_orderTop_mul
  apply le_trans _ hr
  apply add_le_add hf hg

@[simp]
lemma lower_truncated_pow {f : LaurentSeries R} (hf : LowerTruncated 1 f) (n : ℕ) : LowerTruncated (n : ℤ) (f^n) := by
  by_cases hn : n = 0
  · rw [hn]
    simp [← lower_truncated_by_order]
    intro _k hk
    observe h1 : _k ≠ 0
    simp [h1]
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [hm]
    have h : LowerTruncated m (f^m) := by
      have : m < n := by linarith
      apply lower_truncated_pow hf m
    simp only [pow_succ]
    apply lower_truncated_mul h hf

/-
def FLaurentSeries (R : Type _) [CommSemiring R] (n : ℤ) : Submodule R (LaurentSeries R) where
  carrier := {f : LaurentSeries R | LowerTruncated n f}
  add_mem' := by
    intro a b ha hb
    have h1 : min n n = n := by simp
    rw [← h1]
    apply lower_truncated_add ha hb
  zero_mem' := by
    simp
  smul_mem' := by
    intro c a ha
    intro k hk
    have h : (c • a).coeff k = c • a.coeff k := by
      simp
    rw [h]
    have h1 : a.coeff k = 0 := by
      apply ha
      exact hk
    rw [h1]
    simp


instance {n : ℤ} : AddCommMonoid (↑ {f : LaurentSeries R | LowerTruncated n f})
  := (FLaurentSeries R n).addCommMonoid

instance {n : ℤ} : Module R (↑ {f : LaurentSeries R | LowerTruncated n f})
  := Submodule.module (FLaurentSeries R n)
-/

open Subalgebra

def ofPowerSeries_ring (R : Type _) [CommSemiring R] : Subalgebra R (LaurentSeries R)
  := (HahnSeries.ofPowerSeriesAlg ℤ R).range

/-
where
  carrier := {f : LaurentSeries R | LowerTruncated 0 f}
  mul_mem' := by
    intro a b ha hb
    have h : LowerTruncated (0 + 0) (a * b) := by
      apply lower_truncated_mul ha hb
    trivial
  one_mem' := by
    intro k hk
    simp
    contrapose
    intro _
    linarith
  add_mem' := by
    intro a b ha hb
    have h : LowerTruncated (min 0 0) (a + b) := by
      apply lower_truncated_add ha hb
    trivial
  zero_mem' := by
    intro k _
    trivial
  algebraMap_mem' := by
    intro r
    simp [← lower_truncated_by_order]
    intro k hk
    simp [algebraMap, Algebra.toRingHom]
    simp [HahnSeries.single_coeff]
    contrapose
    intro _
    linarith
-/

@[simp]
lemma ofPowerSeries_ring_range : {f : LaurentSeries R | LowerTruncated 0 f} = ofPowerSeries_ring R := by
  ext f
  simp [ofPowerSeries_ring]

def ofPowerSeries_ring₂ (R : Type _) [CommSemiring R] : Subalgebra R (LaurentSeries R)
  := Subalgebra.copy (ofPowerSeries_ring R) {f : LaurentSeries R | LowerTruncated 0 f} ofPowerSeries_ring_range

instance : CommSemiring (↑ {f : LaurentSeries R | LowerTruncated 0 f}) := (ofPowerSeries_ring₂ R).toCommSemiring

instance instAlgLowTrunc : Algebra (R) (↑ {f : LaurentSeries R | LowerTruncated 0 f}) := (ofPowerSeries_ring₂ R).algebra

def ofPowerSeries_equiv (R : Type _) [CommSemiring R] : R⟦X⟧ ≃+* ↑ {f : LaurentSeries R | LowerTruncated 0 f}
  := {
    Equiv.ofBijective (ofPowerSeries₂ R) (ofPowerSeries₂_bijective R) with
    map_add' := by
      intro a b
      simp
      ext k
      have h : (ofPowerSeries₂ R a + ofPowerSeries₂ R b).1
        = (ofPowerSeries₂ R a).1 + (ofPowerSeries₂ R b).1 := by
        trivial
      rw [h]
      simp [HahnSeries.add_coeff]
      simp [ofPowerSeries₂]
    map_mul' := by
      intro a b
      simp
      ext k
      have h : (ofPowerSeries₂ R a * ofPowerSeries₂ R b).1
        = (ofPowerSeries₂ R a).1 * (ofPowerSeries₂ R b).1 := by
        trivial
      rw [h]
      simp [HahnSeries.mul_coeff]
      simp [ofPowerSeries₂]
      simp [HahnSeries.mul_coeff]
  }

def ofPowerSeries_equiv_algHom (R : Type _) [CommSemiring R] : R⟦X⟧ ≃ₐ[R] ↑ {f : LaurentSeries R | LowerTruncated 0 f}
  := {
    ofPowerSeries_equiv R with
    commutes' := by
      intro r
      ext k
      have h : ((algebraMap R ↑{f | LowerTruncated 0 f}) r).1 = (HahnSeries.single (0 : ℤ) r) := by
        trivial
      rw [h]
      simp [ofPowerSeries_equiv, ofPowerSeries₂]
      have h1 : (algebraMap R (HahnSeries ℤ R)) r = (HahnSeries.single (0 : ℤ) r) := by
        trivial
      rw [h1]
  }

@[simp]
lemma ofPowerSeries_equiv_algHom_eq {f : ↑ {f | LowerTruncated 0 f}}
  : (HahnSeries.ofPowerSeriesAlg ℤ R) ((ofPowerSeries_equiv_algHom R).symm.toAlgHom f) = f := by
  have h {g : R⟦X⟧} : (ofPowerSeries_equiv_algHom R) g = (HahnSeries.ofPowerSeriesAlg ℤ R) g := by
    trivial
  rw [← h]
  have h1 : ((ofPowerSeries_equiv_algHom R) ((ofPowerSeries_equiv_algHom R).symm.toAlgHom f)) = f := by
    apply AlgEquiv.coe_apply_coe_coe_symm_apply
  rw [h1]

@[simp]
lemma ofPowerSeries_equiv_algHom_eq₂
  : AlgHom.comp (HahnSeries.ofPowerSeriesAlg ℤ R) (ofPowerSeries_equiv_algHom R).symm.toAlgHom
  = (ofPowerSeries_ring₂ R).val := by
  apply AlgHom.ext_iff.mpr
  intro f
  rw [AlgHom.comp_apply]
  rw [ofPowerSeries_equiv_algHom_eq]
  have h : (ofPowerSeries_ring₂ R).val f = f.1 := by
    apply Subalgebra.val_apply
  exact h



instance instModuleOfPows : Module (↑ {f : LaurentSeries R | LowerTruncated 0 f}) (LaurentSeries R)
  := (ofPowerSeries_ring₂ R).module

instance : SMul (↑ {f : LaurentSeries R | LowerTruncated 0 f}) (LaurentSeries R)
  := instModuleOfPows.toSMul

@[simp]
lemma smul_mul_eq {c : ↑ {f : LaurentSeries R | LowerTruncated 0 f}} {a : LaurentSeries R}
  : c • a = c.1 * a := by
  trivial

def FLaurentSeries (R : Type _) [CommSemiring R] (n : ℤ)
  : Submodule (↑ {f : LaurentSeries R | LowerTruncated 0 f}) (LaurentSeries R) where
  carrier := {f : LaurentSeries R | LowerTruncated n f}
  add_mem' := by
    intro a b ha hb
    have h1 : min (n : ℤ) (n : ℤ) = n := by simp
    rw [← h1]
    apply lower_truncated_add ha hb
  zero_mem' := by
    simp
  smul_mem' := by
    intro c a ha
    simp only [smul_mul_eq]
    have h : LowerTruncated (0 + n) (c.1 * a) := by
      apply lower_truncated_mul c.2 ha
    simp at h
    simp
    exact h

instance {n : ℤ} : AddCommMonoid (↑ {f : LaurentSeries R | LowerTruncated n f})
  := (FLaurentSeries R n).addCommMonoid

instance {n : ℤ} : Module (↑ {f : LaurentSeries R | LowerTruncated 0 f})
  (↑ {f : LaurentSeries R | LowerTruncated n f})
  := Submodule.module (FLaurentSeries R n)

instance {n : ℕ} : Mul (↑ {f : LaurentSeries R | LowerTruncated n f}) where
  mul f g := by
    have h : LowerTruncated 0 f.1 := by
      apply lower_truncated_subset _ f.2
      simp
    let ff : ↑ {f : LaurentSeries R | LowerTruncated 0 f} := ⟨f.1, h⟩
    exact ff • g

@[simp]
lemma smul_mul_eq₂ {n : ℕ} {c : ↑ {f : LaurentSeries R | LowerTruncated 0 f}}
  {p : ↑ {f : LaurentSeries R | LowerTruncated n f}} : (c • p).1 = c.1 * p.1 := by
  trivial

def ofPowerSeries_equiv_trunc {n : ℕ} : ↑ {f : R⟦X⟧ | n ≤ f.order} ≃+* ↑ {f : LaurentSeries R | LowerTruncated n f}
  := {Equiv.ofBijective (ofPowerSeries_trunc R n) (ofPowerSeries_bijective_trunc R n) with
    map_add' := by
      intro a b
      simp
      ext k
      have h : (ofPowerSeries_trunc R n a + ofPowerSeries_trunc R n b).1
        = (ofPowerSeries_trunc R n a).1 + (ofPowerSeries_trunc R n b).1 := by
        trivial
      rw [h]
      simp [HahnSeries.add_coeff]
      simp [ofPowerSeries_trunc]
      have h1 : (a + b).1 = a.1 + b.1 := by
        trivial
      rw [h1]
      simp
    map_mul' := by
      intro a b
      simp
      ext k
      have h : (ofPowerSeries_trunc R n a * ofPowerSeries_trunc R n b).1
        = (ofPowerSeries_trunc R n a).1 * (ofPowerSeries_trunc R n b).1 := by
        trivial
      rw [h]
      simp [HahnSeries.mul_coeff]
      simp [ofPowerSeries_trunc]
      simp [HahnSeries.mul_coeff]
  }



instance {n : ℕ} : Coe ({f : R⟦X⟧ | n ≤ f.order}) ({f : LaurentSeries R | LowerTruncated n f}) where
  coe := ofPowerSeries_equiv_trunc

instance {n : ℕ} : Coe ({f : LaurentSeries R | LowerTruncated n f}) ({f : R⟦X⟧ | n ≤ f.order}) where
  coe := ofPowerSeries_equiv_trunc.symm

@[simp]
lemma ofPowerSeries_equiv_trunc_eq {n : ℕ} {p : ↑ {f : R⟦X⟧ | n ≤ f.order}}
  : (ofPowerSeries_equiv_trunc p).1 = HahnSeries.ofPowerSeriesAlg ℤ R p.1 := by
  simp [ofPowerSeries_equiv_trunc, ofPowerSeries_trunc]

@[simp]
lemma coe_eq_coe_trunc {n : ℕ} {p : ↑ {f : LaurentSeries R | LowerTruncated n f}}
  : ((p : ↑ {f : R⟦X⟧ | n ≤ f.order}) : ↑ {f : LaurentSeries R | LowerTruncated n f}) = p := by
  simp [← RingEquiv.invFun_eq_symm]

@[simp]
lemma coe_eq_coe_trunc₂ {n : ℕ} {p : ↑ {f : R⟦X⟧ | n ≤ f.order}}
  : ((p : ↑ {f : LaurentSeries R | LowerTruncated n f}) : ↑ {f : R⟦X⟧ | n ≤ f.order}) = p := by
  simp


@[simp]
lemma ofPowerSeries_equiv_trunc_map_zero {n : ℕ}
  : ofPowerSeries_equiv_trunc (0 : ↑ {f : R⟦X⟧ | n ≤ f.order}) = 0 := by
  simp
  have h : (0 : ↑ {f : LaurentSeries R | LowerTruncated n f}).1 = (0 : LaurentSeries R) := by
    trivial
  have h1 : (0 : ↑ {f : R⟦X⟧ | n ≤ f.order}).1 = (0 : R⟦X⟧) := by
    trivial
  ext k
  simp [h]
  simp [ofPowerSeries_equiv_trunc, ofPowerSeries_trunc]
  simp [h1]


lemma trunc_comp_range {R S : Type _} [CommSemiring R] [CommSemiring S] (comp : R →+* S) (n : ℤ)
  : (HahnSeries.HahnSeries_hom_via_comp comp) '' {f : LaurentSeries R | LowerTruncated n f}
    ⊆ {f : LaurentSeries S | LowerTruncated n f} := by
  intro f hf
  simp at hf
  intro k hk
  obtain ⟨g, hg1, hg2⟩ := hf
  rw [← hg2]
  have h : g.coeff k = 0 := by
    apply lower_truncated_by_order.mpr hg1
    exact hk
  simp [HahnSeries.coe_via_comp]
  have h1 : comp 0 = 0 := by
    apply map_zero
  rw [← h1]
  congr

lemma trunc_comp_range_apply {R S : Type _} [CommSemiring R] [CommSemiring S] (comp : R →+* S) (n : ℤ)
  (f : ↑ {f : LaurentSeries R | LowerTruncated n f})
  : (HahnSeries.HahnSeries_hom_via_comp comp) f ∈ {f : LaurentSeries S | LowerTruncated n f} := by
  apply trunc_comp_range comp
  apply Set.mem_image_of_mem
  exact f.2

def trunc_comp_map {R S : Type _} [CommSemiring R] [CommSemiring S] (comp : R →+* S) (n : ℤ)
  : ↑ {f : LaurentSeries R | LowerTruncated n f} → ↑ {f : LaurentSeries S | LowerTruncated n f}
  := fun f ↦ ⟨(HahnSeries.HahnSeries_hom_via_comp comp) f, trunc_comp_range_apply comp n f⟩

@[simp]
lemma trunc_comp_map_zero {R S : Type _} [CommSemiring R] [CommSemiring S] (comp : R →+* S) (n : ℤ)
  : trunc_comp_map comp n 0 = 0 := by
  simp [trunc_comp_map]
  have h0 : (0 : ↑ {f : LaurentSeries R | LowerTruncated n f}).1 = 0 := by
    trivial
  have h : HahnSeries.coe_via_comp comp (0 : ↑ {f : LaurentSeries R | LowerTruncated n f}).1 = 0 := by
    rw [h0]
    ext _
    simp
  simp [h]
  trivial

@[simp]
lemma trunc_comp_map_one {R S : Type _} [CommSemiring R] [CommSemiring S] (comp : R →+* S)
  : trunc_comp_map comp 0 1 = 1 := by
  simp only [trunc_comp_map]
  have h0 : (1 : ↑ {f : LaurentSeries R | LowerTruncated 0 f}).1 = 1 := by
    trivial
  have h : HahnSeries.coe_via_comp comp (1 : ↑ {f : LaurentSeries R | LowerTruncated 0 f}).1 = 1 := by
    rw [h0]
    ext _
    simp
  simp [h]
  trivial

@[simp]
lemma trunc_comp_map_add {R S : Type _} [CommSemiring R] [CommSemiring S] (comp : R →+* S) (n : ℤ)
  : ∀ (a b : ↑ {f : LaurentSeries R | LowerTruncated n f}),
  trunc_comp_map comp n (a + b) = trunc_comp_map comp n a + trunc_comp_map comp n b := by
  intro a b
  apply Subtype.coe_injective
  simp
  have h : (trunc_comp_map comp n a + trunc_comp_map comp n b).1
    = (trunc_comp_map comp n a).1 + (trunc_comp_map comp n b).1 := by
    trivial
  rw [h]
  simp only [trunc_comp_map]
  have h1 : (a + b).1 = a.1 + b.1 := by
    trivial
  rw [h1]
  apply map_add


@[simp]
lemma trunc_comp_map_mul {R S : Type _} [CommSemiring R] [CommSemiring S] (comp : R →+* S)
  : ∀ (a b : ↑ {f : LaurentSeries R | LowerTruncated 0 f}),
  trunc_comp_map comp 0 (a * b) = trunc_comp_map comp 0 a * trunc_comp_map comp 0 b := by
  intro a b
  apply Subtype.coe_injective
  simp
  have h : (trunc_comp_map comp 0 a * trunc_comp_map comp 0 b).1
    = (trunc_comp_map comp 0 a).1 * (trunc_comp_map comp 0 b).1 := by
    trivial
  rw [h]
  simp only [trunc_comp_map]
  have h1 : (a * b).1 = a.1 * b.1 := by
    trivial
  rw [h1]
  apply map_mul


@[simp]
lemma trunc_comp_map_smul {R S : Type _} [CommSemiring R] [CommSemiring S] (comp : R →+* S) (n : ℤ)
  : ∀ a : ↑ {f : LaurentSeries R | LowerTruncated 0 f}, ∀ b : ↑ {f : LaurentSeries R | LowerTruncated n f},
  trunc_comp_map comp n (a • b) = trunc_comp_map comp 0 a • trunc_comp_map comp n b := by
  intro a b
  apply Subtype.coe_injective
  simp
  have h : (trunc_comp_map comp 0 a • trunc_comp_map comp n b).1
    = (trunc_comp_map comp 0 a).1 • (trunc_comp_map comp n b).1 := by
    trivial
  rw [h]
  simp only [trunc_comp_map]
  have h1 : (a • b).1 = a.1 • b.1 := by
    trivial
  rw [h1]
  apply map_mul

def trunc_comp {R S : Type _} [CommSemiring R] [CommSemiring S] (comp : R →+* S)
  : ↑ {f : LaurentSeries R | LowerTruncated 0 f} →+* ↑ {f : LaurentSeries S | LowerTruncated 0 f}
  where
  toFun := trunc_comp_map comp 0
  map_zero' := trunc_comp_map_zero comp 0
  map_one' := trunc_comp_map_one comp
  map_add' := trunc_comp_map_add comp 0
  map_mul' := trunc_comp_map_mul comp

def trunc_comp_module {R S : Type _} [CommSemiring R] [CommSemiring S] (comp : R →+* S) {n : ℤ}
  : ↑ {f : LaurentSeries R | LowerTruncated n f}
    →ₛₗ[trunc_comp comp] ↑ {f : LaurentSeries S | LowerTruncated n f} where
  toFun := trunc_comp_map comp n
  map_add' := trunc_comp_map_add comp n
  map_smul' := trunc_comp_map_smul comp n


open HahnSeries
open HahnModule

instance : Module R (LaurentSeries R) := instBaseModule

@[simp]
lemma lower_trucated_by_smul {c : R} {n : ℤ} {f : LaurentSeries R} (h : LowerTruncated n f)
    : LowerTruncated n (c • f) := by
  intro k hk
  simp
  have h1 : f.coeff k = 0 := by
    apply h k hk
  simp [h1]


@[simp]
lemma integers_isPWO (n : ℤ) : {k : ℤ | n ≤ k}.IsPWO := by
  have h : (Set.univ : (Set ℕ)).IsWF := by
    apply WellFounded.isWF
    exact Nat.lt_wfRel.wf
  rw [Set.isWF_iff_isPWO] at h
  let f : ℕ → ℤ := fun i ↦ (i : ℤ) + n
  have hmono : MonotoneOn f Set.univ := by
    intro i _ j _ hij
    have ht : (i : ℤ) ≤ (j : ℤ) := by
      simp [hij]
    apply add_le_add
    exact ht
    trivial
  have hrange : {k : ℤ | n ≤ k} ⊆ f '' Set.univ := by
    intro a ha
    simp
    use (a - n).toNat
    have hr1 : 0 ≤ a - n := by
      simp
      exact ha
    have hr2 : (a - n).toNat = a - n := by
      simp [hr1]
    have hr3 : f (a - n).toNat = (a - n).toNat + n := by
      trivial
    rw [hr3, hr2]
    simp
  have h2 : (f '' Set.univ).IsPWO := by
    apply Set.IsPWO.image_of_monotoneOn h hmono
  apply Set.IsPWO.mono h2
  exact hrange


def power_summable {p : ℕ → LaurentSeries R} (hp : ∀ n : ℕ, LowerTruncated n (p n))
    : HahnSeries.SummableFamily ℤ R ℕ where
  toFun := fun n : ℕ ↦ p n
  isPWO_iUnion_support' := by
    have h {n : ℕ} : (p n).support ⊆ {_n : ℤ | n ≤ _n} := by
      intro k hk
      simp at hk
      have h2 : n ≤ k := by
        apply lower_truncated_coeff (hp n) _
        exact hk
      exact h2

    have hsupp : ⋃ n, (p n).support ⊆ {_n : ℤ | 0 ≤ _n} := by
      apply Set.iUnion_subset_iff.mpr
      have hn : ∀ n : ℕ, (p n).support ⊆ {_n : ℤ | 0 ≤ _n} := by
        intro n
        have hn1 : {_n : ℤ | n ≤ _n} ⊆ {_n : ℤ | 0 ≤ _n} := by
          simp
          intro k
          apply le_trans
          simp
        apply subset_trans h hn1
      exact hn

    apply Set.IsPWO.mono (integers_isPWO 0)
    exact hsupp

  finite_co_support' := by
    intro k
    simp
    have h : {a | ¬(p a).coeff k = 0} ⊆ {a : ℕ | a ≤ k} := by
      intro a ha
      simp
      simp at ha
      apply lower_truncated_coeff (hp a) k ha
    have h1 : {a : ℕ | a ≤ k.toNat}.Finite := by
      apply Set.finite_le_nat k.toNat
    have h2 : {a : ℕ | a ≤ k} ⊆ {a : ℕ | a ≤ k.toNat} := by
      intro a ha
      observe h3 : k ≤ k.toNat
      simp
      simp at ha
      linarith
    have h3 : {a | ¬(p a).coeff k = 0} ⊆ {a : ℕ | a ≤ k.toNat} := by
      apply subset_trans h h2
    apply Set.Finite.subset h1 h3

open PowerSeries
open Finset

def pre_eval (c : R⟦X⟧) (p : ↑ {f : LaurentSeries R | LowerTruncated 1 f}) : HahnSeries.SummableFamily ℤ R ℕ := by
  have hpn : ∀ n : ℕ, LowerTruncated (n : ℤ) (p.1 ^ n) := by
    intro n
    apply lower_truncated_pow p.2 n
  have hpn1 : ∀ n : ℕ, LowerTruncated (n : ℤ) ((PowerSeries.coeff R n c) • (p.1 ^ n)) := by
    intro n
    apply lower_trucated_by_smul (hpn n)
  exact power_summable hpn1

@[simp]
lemma pre_eval_i_factor (c : R⟦X⟧) (p : ↑ {f : LaurentSeries R | LowerTruncated 1 f}) {i : ℕ}
  : (pre_eval c p) i = (coeff R i c) • (p.1 ^ i) := by trivial

lemma eval_coeff (c : R⟦X⟧) (p : ↑ {f : LaurentSeries R | LowerTruncated 1 f}) {k : ℤ}
  : (pre_eval c p).hsum.coeff k = if 0 ≤ k then ∑ᶠ i : ℕ, (coeff R i c) * (p.1 ^ i).coeff k else 0 := by
  by_cases hk : 0 ≤ k
  ·
    simp [if_pos hk]
  · simp [if_neg hk]
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    have h : (p.1 ^ i).coeff k = 0 := by
      have h1 : LowerTruncated i (p.1 ^ i) := by
        apply lower_truncated_pow p.2
      apply h1
      linarith
    rw [h]
    simp

lemma eval_eq (c : R⟦X⟧) (p : ↑ {f : R⟦X⟧ | 1 ≤ f.order}) : (pre_eval c p).hsum
  = HahnSeries.ofPowerSeriesAlg ℤ R (PowerSeries.eval₂ p c) := by
  ext k
  simp only [ofPowerSeriesAlg_coeff]
  simp [eval_coeff]
  by_cases hk : 0 ≤ k
  · simp only [if_pos hk]
    have h : k.toNat = k := by
      simp [hk]
    rw [← h]
    simp [HahnSeries.ofPowerSeries_apply_coeff, eval_coeff₃]
    apply finsum_congr
    intro n
    congr
    simp [ofPowerSeries_equiv_trunc, ofPowerSeries_trunc]
    rw [← map_pow]
    apply ofPowerSeriesAlg_coeff
  · simp [if_neg hk]
    simp at hk
    apply finsum_eq_zero_of_forall_eq_zero
    intro n
    simp [ofPowerSeries_equiv_trunc, ofPowerSeries_trunc]
    have h1 : ((ofPowerSeriesAlg ℤ R) p.1 ^ n).coeff k = 0 := by
      rw [← map_pow]
      simp only [ofPowerSeriesAlg_coeff]
      apply if_neg
      linarith
    simp at h1
    rw [h1]
    simp

lemma eval_map_one (p : ↑ {f : LaurentSeries R | LowerTruncated 1 f})
  : (pre_eval 1 p).hsum = (1 : LaurentSeries R) := by
  let pp := (p : ↑ {f : R⟦X⟧ | 1 ≤ f.order})
  have h : p = (pp : ↑ {f : LaurentSeries R | LowerTruncated 1 f}) := by
    rw [coe_eq_coe_trunc]
  rw [h]
  rw [eval_eq]
  simp

lemma eval_map_zero (p : ↑ {f : LaurentSeries R | LowerTruncated 1 f})
  : (pre_eval 0 p).hsum = (0 : LaurentSeries R) := by
  let pp := (p : ↑ {f : R⟦X⟧ | 1 ≤ f.order})
  have h : p = (pp : ↑ {f : LaurentSeries R | LowerTruncated 1 f}) := by
    rw [coe_eq_coe_trunc]
  rw [h]
  rw [eval_eq]
  simp

lemma eval_map_add (p : ↑ {f : LaurentSeries R | LowerTruncated 1 f}) : ∀ ⦃a b : R⟦X⟧⦄, (pre_eval (a + b) p).hsum
  = (pre_eval a p).hsum + (pre_eval b p).hsum := by
  intro a b
  let pp := (p : ↑ {f : R⟦X⟧ | 1 ≤ f.order})
  have h : p = (pp : ↑ {f : LaurentSeries R | LowerTruncated 1 f}) := by
    rw [coe_eq_coe_trunc]
  rw [h]
  rw [eval_eq, eval_eq, eval_eq]
  simp

lemma eval_map_mul (p : ↑ {f : LaurentSeries R | LowerTruncated 1 f}) : ∀ ⦃a b : R⟦X⟧⦄, (pre_eval (a * b) p).hsum
  = (pre_eval a p).hsum * (pre_eval b p).hsum := by
  intro a b
  let pp := (p : ↑ {f : R⟦X⟧ | 1 ≤ f.order})
  have h : p = (pp : ↑ {f : LaurentSeries R | LowerTruncated 1 f}) := by
    rw [coe_eq_coe_trunc]
  rw [h]
  rw [eval_eq, eval_eq, eval_eq]
  simp

def eval (p : ↑ {f : LaurentSeries R | LowerTruncated 1 f}) : R⟦X⟧ →ₐ[R] LaurentSeries R where
  toFun f := (pre_eval f p).hsum
  map_one' := eval_map_one p
  map_zero' := eval_map_zero p
  map_add' := eval_map_add p
  map_mul' := eval_map_mul p
  commutes' := by
    intro r
    let pp := (p : ↑ {f : R⟦X⟧ | 1 ≤ f.order})
    have h : p = (pp : ↑ {f : LaurentSeries R | LowerTruncated 1 f}) := by
      rw [coe_eq_coe_trunc]
    rw [h]
    simp
    have h1 : (pre_eval ((algebraMap R R⟦X⟧) r) (ofPowerSeries_equiv_trunc pp)).hsum
      = HahnSeries.ofPowerSeriesAlg ℤ R (PowerSeries.eval₂ pp ((algebraMap R R⟦X⟧) r)) := by
      apply eval_eq
    simp at h1
    exact h1

instance instEvalAlgebra (p : ↑ {f : LaurentSeries R | LowerTruncated 1 f})
  : Algebra R⟦X⟧ (LaurentSeries R) := (eval p).toAlgebra

@[simp]
lemma eval_algHom_eq (p : ↑ {f : LaurentSeries R | LowerTruncated 1 f})
  : (ofPowerSeriesAlg ℤ R) ∘ (PowerSeries.eval₂ p) = eval p := by
  funext f
  let pp := (p : ↑ {f : R⟦X⟧ | 1 ≤ f.order})
  have h : p = (pp : ↑ {f : LaurentSeries R | LowerTruncated 1 f}) := by
    rw [coe_eq_coe_trunc]
  rw [h]
  simp
  simp [eval]
  have h : (pre_eval f (ofPowerSeries_equiv_trunc p)).hsum
    = HahnSeries.ofPowerSeriesAlg ℤ R (PowerSeries.eval₂ p f) := by
    apply eval_eq
  simp at h
  apply h.symm

def eval₂ (p : ↑ {f : LaurentSeries R | LowerTruncated 1 f})
  : ↑ {f : LaurentSeries R | LowerTruncated 0 f} →ₐ[R] LaurentSeries R
  := AlgHom.comp (eval p) (LaurentSeries.ofPowerSeries_equiv_algHom R).symm.toAlgHom

lemma eval_inj {T : Type _} [Field T] [Algebra R T] (hmap : Function.Injective (algebraMap R T))
   (p : ↑ {f : LaurentSeries R | LowerTruncated 1 f}) (hp : p.1 ≠ 0)
  : Function.Injective (eval p) := by
  intro a b hab
  let pp := (p : ↑ {f : R⟦X⟧ | 1 ≤ f.order})
  have h : p = (pp : ↑ {f : LaurentSeries R | LowerTruncated 1 f}) := by
    rw [coe_eq_coe_trunc]
  rw [h] at hab
  rw [← eval_algHom_eq] at hab
  simp only [Function.comp_apply] at hab
  have hpp : pp.1 ≠ 0 := by
    by_contra!
    have hpp0 : pp = 0 := by
      apply Subtype.coe_injective
      simp [this]
      trivial
    rw [hpp0] at h
    have hpp1 : ofPowerSeries_equiv_trunc (0 : ↑{f | ↑1 ≤ f.order})
      = (0 : ↑ {f : LaurentSeries R | LowerTruncated 1 f}) := by
      apply ofPowerSeries_equiv_trunc_map_zero
    rw [hpp1] at h
    have hpp2 : p.1 = 0 := by
      simp [h]
      trivial
    contradiction

  apply PowerSeries.eval_inj hmap pp hpp
  rw [ofPowerSeriesAlg_eq, ofPowerSeriesAlg_eq] at hab
  have h : Function.Injective (HahnSeries.ofPowerSeries ℤ R) := by
    apply HahnSeries.ofPowerSeries_injective
  apply h
  have h1 : ofPowerSeries_equiv_trunc.symm (ofPowerSeries_equiv_trunc pp) = pp := by
    simp
  rw [h1] at hab
  exact hab

lemma eval_inj_field {R : Type _} [Field R] (p : ↑ {f : LaurentSeries R | LowerTruncated 1 f}) (hp : p.1 ≠ 0)
  : Function.Injective (eval p) := by
  have h : Function.Injective (algebraMap R R) := by
    intro a b hab
    simp at hab
    exact hab
  apply eval_inj h p hp

def eval_lift {R : Type _} [Field R] (p : ↑ {f : LaurentSeries R | LowerTruncated 1 f}) (hp : p.1 ≠ 0)
  : LaurentSeries R →+* LaurentSeries R := IsFractionRing.lift (eval_inj_field p hp)

@[simp]
lemma eval_lift_eq {R : Type _} [Field R] (p : ↑ {f : LaurentSeries R | LowerTruncated 1 f}) (hp : p.1 ≠ 0)
  {f : ↑ {f : LaurentSeries R | LowerTruncated 0 f}}
  : eval_lift p hp f = eval p (f : ↑ {f : R⟦X⟧ | 0 ≤ f.order}).1 := by
  simp [eval_lift]
  let ff := (f : ↑ {f : R⟦X⟧ | 0 ≤ f.order})
  have h : ofPowerSeries_equiv_trunc ff = f := by
    apply coe_eq_coe_trunc
  rw [← h]
  have h1 : ofPowerSeries_equiv_trunc.symm f = ff := by
    rw [← h]
    apply coe_eq_coe_trunc₂
  rw [← h] at h1
  simp [h1]
  apply IsFractionRing.lift_algebraMap

def eval_fieldHom {R : Type _} [Field R] (p : ↑ {f : LaurentSeries R | LowerTruncated 1 f}) (hp : p.1 ≠ 0)
  : LaurentSeries R →ₐ[R] LaurentSeries R := {(eval_lift p hp) with
  commutes' := by
    intro r
    simp
    have h : (algebraMap R (LaurentSeries R)) r = r • 1 := by
      rw [← HahnSeries.C_eq_algebraMap]
      simp
      ext k
      simp [HahnSeries.single_coeff]
      by_cases h1 : k = 0
      · simp [if_pos h1]
      · simp [if_neg h1]
    rw [h]
    have h1 : eval p (PowerSeries.C R r) = (HahnSeries.C r) := by
      let pp := (p : ↑ {f : R⟦X⟧ | 1 ≤ f.order})
      have hpp : ofPowerSeries_equiv_trunc pp = p := by
        simp [pp]
        apply coe_eq_coe_trunc
      rw [← hpp]
      simp [eval]
      have h2 : (pre_eval ((PowerSeries.C R) r) (ofPowerSeries_equiv_trunc pp)).hsum
        = HahnSeries.ofPowerSeriesAlg ℤ R (PowerSeries.eval₂ p ((PowerSeries.C R) r)) := by
        apply eval_eq
      simp at h2
      rw [h2]
    have h2 : (HahnSeries.C r) = r • (1 : LaurentSeries R) := by
      simp
      ext k
      simp [HahnSeries.single_coeff]
      by_cases h3 : k = 0
      ·
        simp [if_pos h3]
      · simp [if_neg h3]
    rw [← h2]
    have h3 : LowerTruncated 0 (HahnSeries.C r) := by
      intro k hk
      simp
      apply HahnSeries.single_coeff_of_ne
      linarith
    let fr : ↑ {f : LaurentSeries R | LowerTruncated 0 f} := ⟨(HahnSeries.C r), h3⟩
    have h4 : fr.1 = HahnSeries.C r := by
      trivial
    rw [← h4]
    have h5 : (eval_lift p hp) fr.1 = eval p (fr : ↑ {f : R⟦X⟧ | 0 ≤ f.order}).1 := by
      apply eval_lift_eq
    rw [h5]
    rw [h4]
    have h6 : 0 ≤ ((PowerSeries.C R) r).order := by
      simp
    have h7 : fr = ofPowerSeries_equiv_trunc ⟨(PowerSeries.C R) r, h6⟩  := by
      ext k
      simp [ofPowerSeries_equiv_trunc, ofPowerSeries_trunc]
    rw [h7]
    simp
    apply h1
  }

end Evaluation

end LaurentSeries
