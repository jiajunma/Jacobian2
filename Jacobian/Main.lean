import Mathlib

open Classical

open MvPolynomial

open Complex

noncomputable section

inductive Var
| x : Var
| y : Var

abbrev R := MvPolynomial Var ℂ

abbrev x: R := X Var.x
abbrev y: R := X Var.y

abbrev C2 := ℂ × ℂ
abbrev C4 := C2 × C2


/-
The height of a point in (ℂ × ℂ) × (ℂ × ℂ)
is the sum of the absolute values of its coordinates.
-/

lemma _root_.Complex.abs_nonneg (c : ℂ): 0 ≤ abs c := by simp

def h (v : C4) := abs v.1.1 + abs v.1.2 + abs v.2.1 + abs v.2.2

lemma h_noneg (v : C4) : 0 ≤ h v := by
  rw [h]
  have := Complex.abs_nonneg v.1.1
  have := Complex.abs_nonneg v.1.2
  have := Complex.abs_nonneg v.2.1
  have := Complex.abs_nonneg v.2.2
  linarith


abbrev Ch (r:ℝ) := {v : C4 | h v ≥ r}

lemma Vh_inter (r s :ℝ) : Ch r ∩ Ch s = Ch (max r s) := by sorry

def Fh : Filter C4 where
  sets := {s | ∃ r : ℝ , Ch r ⊆ s}
  univ_sets := by
    use 0;simp
  sets_of_superset := by
    intro U V hU hV
    obtain ⟨r,hR⟩ := hU
    use r; exact subset_trans hR hV
  inter_sets := by
    intro U V hU hV
    obtain ⟨r,hr⟩ := hU
    obtain ⟨s,hs⟩ := hV
    use (max r s)
    rw [<-Vh_inter]
    exact Set.inter_subset_inter hr hs

/-
For complex number a b construct the point ((a,b) : Var → ℂ)
-/
def P (a b:ℂ) (v : Var) : ℂ  :=
  match v with
  | Var.x => a
  | Var.y => b

lemma P.a {a b :ℂ} : P a b Var.x = a := by rw [P]
lemma P.b {a b :ℂ} : P a b Var.y = b := by rw [P]


abbrev EV (F : R) (a b : ℂ) := eval (P a b) F
/-
The Jacobian of a pair (F,G) is
| F_x   F_y |
| G_x   G_y |
-/
def J (F G : R) := (pderiv Var.x F ) * (pderiv Var.y G) - (pderiv Var.y F) * (pderiv Var.x G)

/-
The pair (F, G) a Jacobian pair if J(F,G) equals to a non-zero constant
-/
def Jacobian (F G: R):=
  ∃ c : ℂ, J F G = C c ∧ c≠0

def Keller (F G : R) : C2 → C2 := fun x => ((EV F x.1 x.2),(EV G x.1 x.2))



/-
The set V defined in (1.3)
-/
def V (F G: R ):= {v : C4 | Keller F G v.1 = Keller F G v.2 ∧ v.1≠ v.2}

def Filter_V :Filter (V F G) := Filter.comap Subtype.val Fh

variable {F G : R}
local notation " σ " => Keller F G

theorem Jacobian' (H : (V F G).Nonempty) : ¬ Jacobian F G := by sorry

/-
The Key part of the Jacobian conjecture is
Theorem 1.1 of [Su]
-/
theorem Jacobian1   (H : Jacobian F G) : Function.Injective (Keller F G) := by
  contrapose H
  apply Jacobian'
  rw [Function.not_injective_iff] at H
  obtain ⟨a,b,h⟩ := H
  use (a,b); exact h

variable (F G) in
def Vh : (V F G) → ℝ  := h ∘ Subtype.val
variable (F G) in
def Vhy : (V F G) → ℝ := fun x => abs x.1.1.2 + abs x.1.2.2

/-
local notation " hpp " => (Vh F G)
local notation " ypp " => (Vhy F G)
-/

variable (F G) in
def Jbound := (Vhy F G)=o[Filter_V] (Vh F G)

theorem Theorem1_2 : ∃ φ : R ≃ₐ[ℂ] R, Jbound (φ F) (φ G) := by sorry

variable (F G) in
def pi1 : V F G→ C2 := fun v => (v.1.1.1,v.1.2.1)

local notation " π1 " => (pi1 F G)

/-
Theorem 1.3a: π1 is proper.
-/
theorem Theorem1_3a (HV : (V F G).Nonempty)
: IsProperMap  π1 := by sorry

/-
Theorem 1.3b: π1 is finite.
-/
theorem Theorem1_3b (HV : (V F G).Nonempty)
: ∀ c : C2,  Finite <| π1 ⁻¹' {c}:= by sorry

/-
Theorem 1.3b: π1 is surjective.
-/
theorem Theorem1_3c (HV : (V F G).Nonempty)
: Function.Surjective π1 := by sorry


#check x*y


end
