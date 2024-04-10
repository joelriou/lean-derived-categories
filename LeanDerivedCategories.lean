/-

This files accompanies the paper _Formalization of derived categories in Lean/Mathlib_
by Joël Riou.

-/

import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.SpectralSequence.Examples.Grothendieck
import Mathlib.CategoryTheory.Abelian.RefinementsExtra
import Mathlib.CategoryTheory.Localization.Prod

universe w v u

open CategoryTheory Limits

namespace FormalizationOfDerivedCategories

/-! # 2. Homology and diagram chasing in general abelian categories -/

/-! # 2.1 The homology refactor -/

-- Most of the new definitions are in the folder `Mathlib.Algebra.Homology.ShortComplex`
-- which is about "short complexes", i.e. diagrams `X₁ ⟶ X₂ ⟶ X₃` such that the
-- composition of the two maps is zero.

#check ShortComplex
#check ShortComplex.LeftHomologyData
#check ShortComplex.RightHomologyData
#check ShortComplex.HomologyData
#check ShortComplex.Exact
#check ShortComplex.Splitting
#check ShortComplex.Splitting.shortExact

#check HomologicalComplex.homology
#check HomologicalComplex.homologyFunctor

/-! ## 2.2 Diagram chasing -/

/-! ### 2.2.1 -/

-- In the category `Ab` of abelian groups, the exactness of `X₁ ⟶ X₂ ⟶ X₃`
-- can be tested concretely in terms of the elements in these groups:
example {X₁ X₂ X₃ : Ab} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (w : f ≫ g = 0) :
    (ShortComplex.mk f g w).Exact ↔
      ∀ (x₂ : X₂) (_hx₂ : g x₂ = 0), ∃ (x₁ : X₁), f x₁ = x₂ := by
  apply ShortComplex.ab_exact_iff

/-! ### 2.2.2 -/

#check epi_iff_surjective_up_to_refinements
#check ShortComplex.exact_iff_exact_up_to_refinements

/-! ## 2.2.3 -/
section

open Abelian.refinementsTopology

-- Lemma 2.2.3.1: Let `f : X ⟶ Y` be a morphism in an abelian category `C`.
-- Then, `f` is an epimorphism iff the morphism of sheaves `Hom(-,X) ⟶ Hom(-,Y)`
-- (for the refinements topology on `C`) is locally surjective,
-- and if `C` is a small category, this is equivalent to saying this
-- morphism of sheaves is an epimorphism.
#check epi_iff_isLocallySurjective_yoneda_map
#check epi_iff_epi_yoneda_map

end

/-! # 3. Localizaton of categories -/
section

variable {C C₁ C₂ D D₁ D₂ E : Type*} [Category C] [Category C₁] [Category C₂]
  [Category D] [Category D₁] [Category D₂] [Category E]

-- `MorphismProperty C` is the type of classes of morphisms
#check MorphismProperty -- introduced in mathlib by Andrew Yang in 2022

/-! ## 3.1 -/
-- The functor `W.Q : C ⥤ W.Localization` to the constructed localized category. -/
example (W : MorphismProperty C) : C ⥤ W.Localization := W.Q

/-! ## 3.2 -/
-- The functor `W.Q` satisfies the (strict) universal property of the localization.
#check Localization.strictUniversalPropertyFixedTargetQ

/-! ## 3.3 -/

-- The functor `W.Q` to the constructed localized category satisfies the (weaker)
-- predicate `Function.IsLocalization` which characterizes the localized
-- category up to equivalence
example (W : MorphismProperty C) : W.Q.IsLocalization W := inferInstance

/-! ## Lemma 3.4
If `L : C ⥤ D` is a localization functor for a class of morphisms `W`,
then for any category `E`, the composition with `L` induces an equivalence of categories
from the category of functors `D ⥤ E` into the full subcategory of `C ⥤ E`
consisting of functors which inverts `W`. -/
noncomputable example (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] :
    (D ⥤ E) ≌ W.FunctorsInverting E :=
  Localization.functorEquivalence L W E

/-! ## 3.5 Stability properties of localization functors -/

-- stability by taking the opposite category (Lemma 3.5.1)
example (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] :
    L.op.IsLocalization W.op := inferInstance

-- stability by products of categories (Lemma 3.5.2)
example (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁)
    (W₂ : MorphismProperty C₂) [W₁.ContainsIdentities] [W₂.ContainsIdentities]
    [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] :
    (L₁.prod L₂).IsLocalization (W₁.prod W₂) := inferInstance

-- The "proof" of two statements above are found automatically by
-- the type class inference system. The corresponding declarations are:
#check Functor.IsLocalization.op
#check Functor.IsLocalization.prod

-- stability by composition (Lemma 3.5.3)
#check Functor.IsLocalization.comp
-- the reciprocal statement of 3.5.3
#check Functor.IsLocalization.comp

/-! ## 3.6 Calculus of fractions -/

-- the types of left and right fractions
#check MorphismProperty.LeftFraction
#check MorphismProperty.RightFraction

-- the condition that a class of morphisms has a calculus of left/right fractions
#check MorphismProperty.HasLeftCalculusOfFractions
#check MorphismProperty.HasRightCalculusOfFractions

-- Lemma 3.6.1: Assuming there is a calculus of left fractions,
-- * Morphisms in the localized category can be represented by left fractions
#check Localization.exists_leftFraction
-- * Characterizations of tuples of left fractions which induce the
--   same morphism in the localized category
#check MorphismProperty.LeftFraction.map_eq_iff
-- * Characterization of tuples of morphisms in the original category which
--   induce the same morphism in the localized category
#check MorphismProperty.map_eq_iff_postcomp

/-! ## 3.7 Calculus of fractions -/

-- the localized category of a preadditive is preadditive when
-- there is a calculus of left fractions
noncomputable instance (W : MorphismProperty C) [Preadditive C]
    [W.HasLeftCalculusOfFractions] :
    Preadditive W.Localization := inferInstance
-- this preadditive structure is obtained thanks to the following declaration
#check Localization.preadditive

end
/-! ## 3.8 Universe issues -/
section

/-! ### 3.8.1 -/
variable {C : Type u} [Category.{v} C]

-- this means that we have a category `C`
-- * the type `C` of objects is in the universe `u`:
example : Type u := C
-- * the type of morphisms `X ⟶ Y` between two objects in `C` is in the universe `v`:
example (X Y : C) : Type v := X ⟶ Y

/-! ### 3.8.2 -/

variable (W : MorphismProperty C)

-- the type of the objects of the constructed localized category
-- `W.Localization` with respect to the class of morphisms `W`
-- is a type synonym for `C`: it is in the universe `u`:
example : Type u := W.Localization

-- however, the type of morphisms between two objects in `W.Localization`
-- is not in `max v` general, it is in the universe `max u v`:
example (X Y : W.Localization) : Type (max u v) := X ⟶ Y

-- the same problems happens when there is a calculus of fractions:
-- because of the intermediate object, the type of left fractions
-- from `X` to `Y` is in `Type (max u v)`:
example (X Y : C) : Type (max u v) := W.LeftFraction X Y

/-! ### 3.8.3
I formalized the fundamental lemma of homotopical algebra 3.8.3.1 in lean 3,
it appeard in the file `src/for_mathlib/algebraic_topology/homotopical_algebra`
in the project at https://github.com/joelriou/homotopical_algebra
-/

/-! ### 3.8.5 -/

-- We may introduce the assumption that we have chosen
-- a localized category such that the morphisms are in the universe `w` as follows.
variable [MorphismProperty.HasLocalization.{w} W]

-- this provides a localization functor `W.Q' : C ⥤ W.Localization'`
example : W.Q'.IsLocalization W := inferInstance
-- such that morphisms in `W.Localization'` are in the universe `w`
example (X Y : W.Localization') : Type w := X ⟶ Y

/-! ### 3.8.6
This is 3.8.5 in the particular case of derived categories. -/

variable [Abelian C] [HasDerivedCategory.{w} C]
example (X Y : DerivedCategory C) : Type w := X ⟶ Y

end

/-! # 4. The derived category -/
section

variable {C : Type u} [Category.{v} C] [Abelian C]

-- If we do not make any particular efforts, morphisms in the derived
-- category are going to be in `max u v`.
example : HasDerivedCategory.{max u v} C :=
  MorphismProperty.HasLocalization.standard _

-- In what follows, we assyme `[HasDerivedCategory.{w} C]` for a certain universe `w`.
variable [HasDerivedCategory.{w} C]

-- The main result of the paper is the formalization of the triangulated
-- structure on the derived category of any abelian category `C`.
example : IsTriangulated (DerivedCategory C) := inferInstance

/-! ## 4.1 Definitions -/

-- ## 4.1.1
-- The most important property of the cylinder is the following declaration:
#check HomologicalComplex.cylinder.desc

-- ## 4.1.2
-- the three functors between the categories of cochain complexes,
-- the homotopy category, and the derived category
example : CochainComplex C ℤ ⥤ HomotopyCategory C (ComplexShape.up ℤ) :=
  HomotopyCategory.quotient _ _
example : HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C :=
  DerivedCategory.Qh
example : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q

-- these functors form a commutative triangle (up to isomorphisms):
example : HomotopyCategory.quotient C _ ⋙ DerivedCategory.Qh ≅ DerivedCategory.Q :=
  DerivedCategory.quotientCompQhIso C

-- the derived category is the localized category of the category
-- of cochain complexes with respect to quasi-isomorphisms
example : DerivedCategory.Q.IsLocalization (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) :=
  inferInstance

-- the derived category is the localized category of the homotopy category
-- of cochain complexes with respect to quasi-isomorphisms
example : DerivedCategory.Qh.IsLocalization (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  inferInstance

end
/-! ## 4.2 Shifts -/

/-! ### 4.2.2 -/
-- definition of shifts by an additive monoid `A` on a category `C`
-- as `MonoidalFunctor (Discrete ℤ) (C ⥤ C)` introduced in mathlib
-- by Andrew Yang and Johan Commelin in 2021
#check HasShift

/-! ### 4.2.3
Improvement of automation for the verification of identities involving shifts.
See the file `CategoryTheory.Triangulated.Rotate`: it contains only three proofs,
the rest of the statements were obtained automatically.
-/

/-! ### 4.2.4/4.2.5 -/
-- Using only `shiftFunctorAdd`
#check shiftFunctorAdd
-- the pentagon diagram for the "associativity" involve `eqToHom`:
#check ShiftMkCore.assoc_hom_app

-- Using `shiftFunctorAdd'`
#check shiftFunctorAdd'
-- the "pentagon" no longer involve `eqToHom`:
#check shiftFunctorAdd'_assoc

/-! ### 4.2.6/4.2.7 The shift on cochain complexes and on the homotopy category -/
section

variable {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]

-- the shift on cochain complexes and on the homotopy category are defined in the file
-- `Algebra.Homology.HomotopyCategory.Shift`.
example : HasShift (CochainComplex C ℤ) ℤ := inferInstance
noncomputable example : HasShift (HomotopyCategory C (ComplexShape.up ℤ)) ℤ := inferInstance

/-! ### 4.2.8 Functors which commute to the shift. -/

variable (F : C ⥤ D) [F.Additive]

-- the functors induced by an additive functor on categories of cochain complex or
-- on homotopy categories commute to shift
example : (F.mapHomologicalComplex (ComplexShape.up ℤ)).CommShift ℤ := inferInstance
noncomputable example : (F.mapHomotopyCategory (ComplexShape.up ℤ)).CommShift ℤ := inferInstance

-- this not only means that up to isomorphisms, the these functors commute with the
-- shift by any `a : ℤ`, but also that these isomorphisms satisfy certain compatibilites:
#check Functor.CommShift.zero
#check Functor.CommShift.add

/-! ### 4.2.9 Quotient and localized shift  -/

-- the quotient and the localized shift are given by these declarations
#check HasShift.quotient
#check HasShift.localization

-- both rely on a more abstract construction
#check HasShift.induced

end
/-! ## 4.3 The triangulated structure on the homotopy category -/

/-! ### 4.3.1 -/
-- The axioms of pretriangulated categories were formalized
-- by Luke Kershaw in 2021
#check Pretriangulated
-- I added the octahedron axiom in 2022
#check IsTriangulated

/-! ### 4.3.2 -/
-- the standard triangle attached to a morphism in the category `CochainComplex C ℤ`
#check CochainComplex.mappingCone.triangle

/-! ### 4.3.3/4.3.4 Calculus of cochain/The octahedron axiom -/
section

open CochainComplex HomComplex

variable {C : Type*} [Category C] [Preadditive C] (K L M : CochainComplex C ℤ) (n : ℤ)
  [HasBinaryBiproducts C]

-- the type of cochain and of cocycles of a certain degree `n : ℤ`
-- between two cochain complexes
#check Cochain K L n
#check Cocycle K L n

-- morphisms and homotopies in `CochainComplex C ℤ` can be interpreted in terms of cochains
example : (K ⟶ L) ≃+ Cocycle K L 0 := Cocycle.equivHom K L
example (φ₁ φ₂ : K ⟶ L) :
    Homotopy φ₁ φ₂ ≃
      { z : Cochain K L (-1) // Cochain.ofHom φ₁ = δ (-1) 0 z + Cochain.ofHom φ₂ } :=
  Cochain.equivHomotopy _ _

variable (f : K ⟶ L)

-- the mapping cone of a morphism `f : K ⟶ L` of cochain complexes
noncomputable example (f : K ⟶ L)  :
    CochainComplex C ℤ :=
  mappingCone f

open mappingCone

-- the two "injections" and the two "projections" to/from the mapping cone,
-- either as a cochain, a cocycle or a morphism.
noncomputable example : Cochain K (mappingCone f) (-1) := inl f
noncomputable example : L ⟶ mappingCone f := inr f
noncomputable example : Cocycle (mappingCone f) K 1 := fst f
noncomputable example : Cochain (mappingCone f) L 0 := snd f

-- the composition of cochains of degrees `1` and `-1` may be a cochain of degree `1 + (-1)`
noncomputable example : Cochain (mappingCone f) (mappingCone f) (1 + (-1)) :=
  (fst f).1.comp (inl f) rfl

-- it may also be a cochain of degree `0`:
noncomputable example : Cochain (mappingCone f) (mappingCone f) 0 :=
  (fst f).1.comp (inl f) (by omega)

-- statement of the associativity of the composition of cochains
#check Cochain.comp_assoc

example (α : Cochain M K n) : (α.comp (inl f) rfl).comp (fst f).1 (by omega) = α := by
  simp -- replace by `simp?` to see the names of the lemmas that are automatically used

end


end FormalizationOfDerivedCategories
