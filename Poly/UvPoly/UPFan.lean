/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Poly.UvPoly.Basic

noncomputable section

namespace CategoryTheory.UvPoly
open Limits CategoryTheory.UvPoly.PartialProduct

universe v u
variable {C : Type u} [Category.{v} C] [HasPullbacks C] [HasTerminal C] {E B : C}

/-- Universal property of the polynomial functor. The inverse laws follow from
partial-product hom extensionality and the two lift projection identities. -/
@[simps]
def equiv (P : UvPoly E B) (Γ : C) (X : C) :
    (Γ ⟶ P @ X) ≃ (b : Γ ⟶ B) × (pullback b P.p ⟶ X) where
  toFun := P.proj
  invFun u := P.lift (Γ := Γ) (X := X) u.1 u.2
  left_inv f := by
    refine P.hom_ext ?_ ?_
    · exact lift_fst (P := P) (b := (P.proj f).1) (e := (P.proj f).2)
    · change PartialProduct.comparison (P.lift (P.proj f).1 (P.proj f).2) ≫
        (fan P X).snd = _
      rw [lift_snd]
      congr 1
      exact (proj_snd (P := P)).trans
        (congrArg (fun k => k ≫ (fan P X).snd)
          (PartialProduct.comparison_pullback.map (c := fan P X) (f := f)).symm)
  right_inv := by
    intro ⟨b, e⟩
    apply Sigma.ext (lift_fst (P := P))
    have w := lift_snd (P := P) (b := b) (e := e)
    rw [PartialProduct.comparison_pullback.map] at w
    change (P.proj (P.lift b e)).2 = _ at w
    have transport {b' b : Γ ⟶ B} (h : b' = b)
        (e' : pullback b' P.p ⟶ X) (e : pullback b P.p ⟶ X)
        (w : e' = (pullback.congrHom h rfl).hom ≫ e) : HEq e' e := by
      cases h
      apply heq_of_eq
      simpa [pullback.congrHom] using w
    exact transport (lift_fst (P := P)) _ _ w

end CategoryTheory.UvPoly
