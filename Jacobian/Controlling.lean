import Jacobian.FormalSeries

open Real
open NNReal

noncomputable section

namespace Controlling

open HahnSeries
open LaurentSeries
open PowerSeries

def NNReal_toReal_alg : NNReal →ₐ[NNReal] ℝ
  := {
    NNReal.toRealHom with
    commutes' := by
      intro r
      simp
  }

abbrev CF_pre : Subalgebra NNReal (LaurentSeries ℝ)
  := AlgHom.range (NNReal_toReal_alg : (LaurentSeries NNReal →ₐ[NNReal] LaurentSeries ℝ))

@[simp]
lemma isCF_pre {f : LaurentSeries ℝ} : f ∈ CF_pre ↔ f ∈ {_f : LaurentSeries ℝ | ∀ k : ℤ, 0 ≤ _f.coeff k} := by
  have h : f ∈ CF_pre ↔ f ∈ Set.range (HahnSeries_hom_via_comp NNReal.toRealHom) := by
    simp [NNReal_toReal_alg]
  rw [h]
  have h1 : f ∈ Set.range (HahnSeries_hom_via_comp NNReal.toRealHom)
    ↔ f ∈ {_f : LaurentSeries ℝ | ∀ k : ℤ, _f.coeff k ∈ Set.range NNReal.toRealHom} := by
    apply range_of_comp
  rw [h1]
  simp
  constructor
  · intro hl k
    obtain ⟨a, ha⟩ := hl k
    rw [← ha]
    simp
  · intro hr k
    use ⟨f.coeff k, hr k⟩
    simp

lemma CF_pre_Carrier : CF_pre = {_f : LaurentSeries ℝ | ∀ k : ℤ, 0 ≤ _f.coeff k} := by
  simp
  ext f
  apply isCF_pre

abbrev CF := Subalgebra.copy CF_pre {_f : LaurentSeries ℝ | ∀ k : ℤ, 0 ≤ _f.coeff k} CF_pre_Carrier.symm

instance : CommSemiring (↑ {_f : LaurentSeries ℝ | ∀ k : ℤ, 0 ≤ _f.coeff k}) := CF.toCommSemiring

instance : Algebra NNReal (↑ {_f : LaurentSeries ℝ | ∀ k : ℤ, 0 ≤ _f.coeff k}) := CF.algebra

def eval_CF {p : LaurentSeries NNReal} (c : NNReal⟦X⟧)
  (hp : LowerTruncated 1 p) := (eval ⟨p, hp⟩ c)



end Controlling
