/-

This files accompanies the paper _Formalization of derived categories in Lean/Mathlib_
by Joël Riou.

https://hal.science/hal-04546712

In VS code:
* Hover the pointer on names of definitions below to get the full statement
* Right-click + Go to Definition to see the code of the definition in context

-/

import Mathlib.Algebra.Homology.DerivedCategory.LargeExt
import Mathlib.Algebra.Homology.SpectralSequence.Examples.Grothendieck
import Mathlib.CategoryTheory.Abelian.RefinementsExtra
import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.Triangulated.Yoneda

universe w v u

open CategoryTheory Limits

namespace FormalizationOfDerivedCategories

/-! # 1. Introduction -/

-- These are the two main definitions in this project:
-- * the derived category of an abelian category
#check DerivedCategory
-- * the Grothendieck spectral sequence for the composition of right derived functors
#check DerivedCategory.Plus.grothendieckSpectralSequence

-- We use classical logic
#print axioms DerivedCategory.Plus.grothendieckSpectralSequence

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

/-! ### 2.2.3 -/
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

/-! ## 3.1 -/

-- `MorphismProperty C` is the type of classes of morphisms in a category `C`
#check MorphismProperty -- introduced in mathlib by Andrew Yang in 2022

-- The functor `W.Q : C ⥤ W.Localization` to the constructed localized category. -/
example (W : MorphismProperty C) : C ⥤ W.Localization := W.Q

-- the localization functor `W.Q` sends morphisms in `W` to isomorphisms
example (W : MorphismProperty C) : W.IsInvertedBy W.Q := W.Q_inverts

/-! ## 3.2 -/
-- The functor `W.Q` satisfies the (strict) universal property of the localization.
#check Localization.strictUniversalPropertyFixedTargetQ

/-! ## 3.3 -/

-- The functor `W.Q` to the constructed localized category satisfies the (weaker)
-- predicate `Functor.IsLocalization` which characterizes the localized
-- category up to equivalence
example (W : MorphismProperty C) : W.Q.IsLocalization W := inferInstance

/-! ## Lemma 3.4
If `L : C ⥤ D` is a localization functor for a class of morphisms `W`,
then for any category `E`, the composition with `L` induces an equivalence of categories
from the category of functors `D ⥤ E` to the full subcategory of `C ⥤ E`
consisting of functors which invert `W`. -/
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

-- The "proof" of the two statements above are found automatically by
-- the type class inference system. The corresponding declarations are:
#check Functor.IsLocalization.op
#check Functor.IsLocalization.prod

-- stability by composition (Lemma 3.5.3)
#check Functor.IsLocalization.comp
-- the reciprocal statement of 3.5.3
#check Functor.IsLocalization.of_comp

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

-- Moreover, we may characterize tuples of morphisms in the original category
-- which induce the same morphism in the localized category
#check MorphismProperty.map_eq_iff_postcomp

/-! ## 3.7 Preadditive structure -/

-- the existence of finite products in the localized category can be
-- deduced from the existence of finite products in the original category
-- under the condition that `W` contains identities and is stable
-- by finite products
instance (W : MorphismProperty C) [HasFiniteProducts C]
    [W.IsStableUnderFiniteProducts] [W.ContainsIdentities] :
    HasFiniteProducts W.Localization := inferInstance

-- the localized category of a preadditive category is preadditive when
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

-- The declaration of variables above means that we have a category `C` such that:
-- * the type `C` of objects is in the universe `u`:
example : Type u := C
-- * the type of morphisms `X ⟶ Y` between two objects in `C` is in the universe `v`:
example (X Y : C) : Type v := X ⟶ Y

/-! ### 3.8.2 -/

variable (W : MorphismProperty C)

-- The type of the objects of the constructed localized category
-- `W.Localization` with respect to the class of morphisms `W`
-- is a type synonym for `C`, then it is in the universe `u`:
example : Type u := W.Localization

-- However, the type of morphisms between two objects in `W.Localization`
-- is not in `max v` in general, it is in the universe `max u v`:
example (X Y : W.Localization) : Type (max u v) := X ⟶ Y

-- The same problems happens even when there is a calculus of fractions:
-- because of the data of an intermediate object, the type of left fractions
-- from `X` to `Y` is in `Type (max u v)`:
example (X Y : C) : Type (max u v) := W.LeftFraction X Y

/-! ### 3.8.3
I formalized the fundamental lemma of homotopical algebra 3.8.3.1 in lean 3, it appeared
in the file `src/for_mathlib/algebraic_topology/homotopical_algebra/fundamental_lemma`
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
-- category of `C` are going to be in `Type (max u v)`.
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

example : CochainComplex C ℤ ⥤ DerivedCategory C :=
  DerivedCategory.Q

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

-- The functor `CochainComplex C ℤ ⥤ HomotopyCategory C (ComplexShape.up ℤ)`
-- commutes with the shift
noncomputable example : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).CommShift ℤ :=
  inferInstance

-- this not only means that up to isomorphisms, this functor commute with the
-- shift by any `a : ℤ`, but also that these isomorphisms satisfy certain compatibilites:
#check Functor.CommShift.zero
#check Functor.CommShift.add

-- Another example: the functors induced by an additive functor on categories
-- of cochain complexes and on homotopy categories commute to the shift
example (F : C ⥤ D) [F.Additive] :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).CommShift ℤ := inferInstance
noncomputable example (F : C ⥤ D) [F.Additive] :
    (F.mapHomotopyCategory (ComplexShape.up ℤ)).CommShift ℤ := inferInstance

end
/-! ### 4.2.9 Quotient and localized shift  -/

-- the quotient and the localized shift are given by these declarations
#check HasShift.quotient
#check HasShift.localization

-- both rely on a more abstract construction
#check HasShift.induced

section

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

-- The functor `Q : CochainComplex C ℤ ⥤ DerivedCategory C` commutes with the shift
noncomputable instance : (DerivedCategory.Q (C := C)).CommShift ℤ := inferInstance

-- The natural isomorphism
-- `HomotopyCategory.quotient C _ ⋙ DerivedCategory.Qh ≅ DerivedCategory.Q`
-- between functors `CochainComplex C ℤ ⥤ DerivedCategory C`
-- commutes with the shift
example : NatTrans.CommShift (DerivedCategory.quotientCompQhIso C).hom ℤ :=
  inferInstance

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

/-! ### 4.3.3/4.3.4 Calculus of cochains/The octahedron axiom -/
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

-- given two composable morphisms `f` and `g` in the category of cochain complexes,
-- this is the main lemma in the proof that `mappingCone g` is a retract by deformation
-- of the mapping cone of `mappingCone f ⟶ mappingCone (f ≫ g)`
#check MappingConeCompHomotopyEquiv.homotopyInvHomId
-- in the proof, the lemmas `mappingCone.ext_to_iff` and `mappingCone.ext_from_iff`
-- are used in order to transform a goal involving an equality between morphisms
-- from the mapping cone of `mappingCone f ⟶ mappingCone (f ≫ g)` to itself
-- into a conjunction of multiple identities that are mostly handled by automation

end

/-! ## 4.4 The localization theorem for triangulated categories -/

section

variable {T : Type*} [Category T] [HasZeroObject T] [Preadditive T] [HasShift T ℤ]
  [∀ (n : ℤ), (shiftFunctor T n).Additive] [Pretriangulated T]

/-! ### 4.4.1 The localization theorem -/

example (W : MorphismProperty T) [W.HasLeftCalculusOfFractions]
    [W.IsCompatibleWithTriangulation] :
  Pretriangulated W.Localization := by infer_instance

example [IsTriangulated T] (W : MorphismProperty T) [W.HasLeftCalculusOfFractions]
    [W.HasRightCalculusOfFractions] [W.IsCompatibleWithTriangulation] :
  IsTriangulated W.Localization := by infer_instance

/-! ### 4.4.2 Triangulated subcategories -/

-- the notion of triangulated subcategory of a pretriangulated category
#check Triangulated.Subcategory

-- if `S` is a triangulated subcategory of a triangulated category `T`, then
-- the class `S.W : MorphismProperty T` of morphisms whose cone is
-- in `S` (at least up to isomorphism) satisfies the assumption of the theorem 4.4.1,
-- in which case the localized category with respect to `S.W` is the "Verdier quotient `T/S`"
example (S : Triangulated.Subcategory T) [IsTriangulated T] :
    IsTriangulated S.W.Localization := inferInstance

end
/-! ### 4.4.3 The derived category -/

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

-- The triangulated subcategory of the homotopy category of an abelian category
-- consisting of acyclic complexes
example : Triangulated.Subcategory (HomotopyCategory C (ComplexShape.up ℤ)) :=
  HomotopyCategory.subcategoryAcyclic C

-- the derived category identifies to the Verdier quotient of the homotopy category
-- by the triangulated subcategory of acyclic complexes
instance : DerivedCategory.Qh.IsLocalization (HomotopyCategory.subcategoryAcyclic C).W :=
  inferInstance
-- this follows from the fact that the class `(HomotopyCategory.subcategoryAcyclic C).W`
-- is the class of quasi-isomorphisms:
#check HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W
-- the proof of this lemma uses the fact that the homology functor on the homotopy
-- category is a homological functor:
example : (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).IsHomological :=
  inferInstance

end

/-! # 5. Ongoing works -/

/-! ## 5.1 Ext-groups -/

section

open DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

-- This is the functor which sends `X : C` to the cochain complex (seen in the derived
-- category) with `X` in degree `0`, and `0` in nonzero degrees
noncomputable example : C ⥤ DerivedCategory C := singleFunctor C 0

-- this functor `singleFunctor C 0` is fully faithful
noncomputable example (X Y : C) :
    (X ⟶ Y) ≃ ((singleFunctor C 0).obj X ⟶ (singleFunctor C 0).obj Y) :=
  equivOfFullyFaithful _

-- the group `Ext^n(X, Y)` could be redefined as:
example (X Y : C) (n : ℕ) : Type w :=
  (singleFunctor C 0).obj X ⟶ ((singleFunctor C 0).obj Y)⟦(n : ℤ)⟧

-- if `0 → X₁ → X₂ → X₃ → 0` is a short exact sequence in `C`, then there is
-- a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` in the derived category
-- (by abuse of notation, we identify object of `C` to their image by `singleFunctor C 0`)
#check ShortComplex.ShortExact.singleTriangle_distinguished

section

open Pretriangulated.Opposite

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

-- then the assertion that we have "covariant" and "contravariant" long
-- exact sequences of `Ext` is supported by the fact that in (pre)triangulated
-- categories, `Hom(-,Y)` and `Hom(X, -)` functors are homological:

instance (Y : C) : (preadditiveYoneda.obj Y).IsHomological := inferInstance

instance (X : Cᵒᵖ) : (preadditiveCoyoneda.obj X).IsHomological := inferInstance

end

end

/-! ## 5.2 t-structures -/

section

open Triangulated DerivedCategory.TStructure

-- the notion of t-structure on a triangulated category
#check TStructure

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

-- the canonical t-structure on the derived category `D(C)`
example : TStructure (DerivedCategory C) := t
-- the induced t-structure on the bounded below derived category `D^+(C)`
example : TStructure (DerivedCategory.Plus C) := DerivedCategory.Plus.TStructure.t

variable {T : Type*} [Category T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ (n : ℤ), (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T]

-- The type class assumption below `[t.HasHeart]` means that we have chosen
-- a *preadditive* category which identifies to the full subcategory of `T`
-- consisting of objects that are both ≤ 0 and ≥ 0. This instance
-- declared in the file `CategoryTheory.Triangulated.TStucture.Homology`
-- shows that the heart of the `t`-structure is an abelian category:
noncomputable example (t : TStructure T) [t.HasHeart] : Abelian t.Heart := inferInstance

-- A `HasHeart` instance was set on the canonical `t`-structure on the derived category of `C`:
-- by "definition", the heart of this `t`-structure is the category `C` itself!
example : (t : TStructure (DerivedCategory C)).Heart = C := rfl

/-! ### 5.2.3 -/

variable (t : TStructure T)

-- the truncation functors for a `t`-structure
noncomputable example (n : ℤ) : T ⥤ T := t.truncGE n
noncomputable example (n : ℤ) : T ⥤ T := t.truncLE n

-- if `a + 1 = b`, this is the distinguished triangle
-- `(t.truncLE a).obj X ⟶ X ⟶ (t.truncGE b).X ⟶ ((t.truncLE a).obj X)⟦1⟧`
variable (a b : ℤ) (h : a + 1 = b) (X : T) in
#check t.triangleLEGE_distinguished a b h X

-- the truncation functors commute:
noncomputable example (a b : ℤ) :
    t.truncLE b ⋙ t.truncGE a ≅ t.truncGE a ⋙ t.truncLE b :=
  t.truncGELEIsoLEGE a b

/-! ### 5.2.4 -/
-- Given an object `X : T` in a triangulated category `T` equipped with a `t`-structure,
-- all the truncations of `X` for this `t`-structure fit together in
-- a spectral object in `T` that is parametrized by the ordered set `ℤt` which is
-- `ℤ` with `+∞` and `-∞` added.
noncomputable example (X : T) : SpectralObject T ℤt := t.spectralObject X

end

/-! ## 5.3 Derived functors -/

/-! ### 5.3.1 -/
-- the notions of left Kan extension and of right derived functors
#check Functor.IsLeftKanExtension
#check Functor.IsRightDerivedFunctor

/-! ### 5.3.3 The right derived functor on bounded below derived categories -/

section

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
  [EnoughInjectives C]

-- the right derived functor of `F` as a functor `D^+(C) ⥤ D^+(D)`
-- on bounded below derived categories, when `C` has enough injectives
noncomputable example : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D :=
  F.rightDerivedFunctorPlus

-- the assertion that `F.rightDerivedFunctorPlus` is indeed a right derived functor
instance : F.rightDerivedFunctorPlus.IsRightDerivedFunctor
  F.rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C) := inferInstance

-- the bounded below derived category `D^+(C)` is equivalent to the homotopy category
-- of bounded below complexes of injective objects.
noncomputable instance :
    (((Injectives.ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)).IsEquivalence :=
  inferInstance

-- the existence of derived functor follows from the existence of
-- a right derivability structure, which is part of a very abstract framework
-- in order to construct and study derived functors
instance : (Injectives.localizerMorphism C).IsRightDerivabilityStructure := inferInstance
-- this notion involves the concept of Guitart exact squares:
#check TwoSquare.GuitartExact
-- apart from very abstract category theory, the injective derivability structure
-- relies on factorization lemmas in the category of cochain complexes, which
-- include the following lemma, which assert the existence of injective resolutions
-- of bounded below cochain complexes:
#check CochainComplex.exists_injective_resolution

end

/-! ### 5.3.4 The product derivability structure
See the file `CategoryTheory.Localization.DerivabilityStructure.Product` -/

/-! ## 5.4 Spectral sequences -/

/-! ### 5.4.1 Definitions -/

#check SpectralSequence

-- pages of cohomological spectral sequences are indexed by `ℤ × ℤ`,
-- and differentials are of bidegree `(r, 1 - r)`.
#check CohomologicalSpectralSequence
#check E₂CohomologicalSpectralSequence

-- for first quadrant spectral sequence, we can use the following definitions
-- for which the pages are indexed by `ℕ × ℕ`.
#check CohomologicalSpectralSequenceNat
#check E₂CohomologicalSpectralSequenceNat

/-! ### 5.4.2 Stabilization -/

#check SpectralSequence.HasPageInfinityAt

/-! ### 5.4.3 Convergence -/

#check SpectralSequence.StronglyConvergesTo

-- the 5-terms exact sequence in low degrees of a first
-- quadrant E₂-cohomological spectral sequence
#check CohomologicalSpectralSequenceNat.lowDegreesComposableArrows_exact

/-! ### 5.4.4 Construction of spectral sequences -/

-- the notions of spectral objects in triangulated categories and in abelian categories
#check Triangulated.SpectralObject
#check Abelian.SpectralObject

section

variable {C T : Type*} [Category C] [Abelian C]
  [Category T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ (n : ℤ), (shiftFunctor T n).Additive] [Pretriangulated T]

-- If `E` is a spectral object in a pretriangulated category `T` and `F : T ⥤ C`
-- is a homological functor, applying `F` in all degrees to `X` gives
-- a spectral object in the abelian category `C`.
-- (The assumption `F.ShiftSequence ℤ` is the data of shifted versions of `F` in
-- all degrees `n` which may have better definitional properties than the
-- functors which send `Y : T` to `F.obj (Y⟦n⟧)`. In some sense `F` is the `H^0`,
-- and the functors `F.shift n` given by the "shift sequence" are the `H^n`.)
noncomputable example (E : Triangulated.SpectralObject T ℤt) (F : T ⥤ C)
    [F.IsHomological] [F.ShiftSequence ℤ] :
  Abelian.SpectralObject C ℤt := E.mapHomologicalFunctor F

end

/-! ### 5.4.5 Examples of spectral sequences -/

section GrothendieckSpectralSequence

open DerivedCategory.Plus

-- Let `F : A ⥤ B` and `G : B ⥤ C` be additive functors between abelian categories.
-- We assume that `A` and `B` have enough injectives.
variable {A B C : Type*} [Category A] [Category B] [Category C]
  [Abelian A] [Abelian B] [Abelian C] [EnoughInjectives A] [EnoughInjectives B]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]

-- The canonical natural transformation `R(F ⋙ G) ⟶ RF ⋙ RG`:
noncomputable example :
    (F ⋙ G).rightDerivedFunctorPlus ⟶
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusCompNatTrans (Iso.refl _)

-- We assume that for any injective object `I` of `A`, `F(I)` is acyclic for `G`:
variable [∀ (I : Injectives A), IsIso (G.rightDerivedFunctorPlusUnit.app
  ((HomotopyCategory.Plus.singleFunctor B 0).obj (F.obj ((Injectives.ι A).obj I))))]

-- We now have an isomorphism `R(F ⋙ G) ≅ RF ⋙ RG`:
noncomputable example :
    (F ⋙ G).rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  asIso (Functor.rightDerivedFunctorPlusCompNatTrans (Iso.refl _))

-- Fix an object in `A`
variable (X : A)

-- This is the first quadrant E₂-cohomological spectral sequence of
-- composition of right derived functors (Grothendieck):
noncomputable example : E₂CohomologicalSpectralSequenceNat C :=
  grothendieckSpectralSequence F G X

open grothendieckSpectralSequence

-- `E₂^{p, q}` identifies to `(R^p G)(R^q F(X))`
noncomputable example (p q : ℕ) :
    ((grothendieckSpectralSequence F G X).page 2).X ⟨p, q⟩ ≅
      (G.rightDerived' p).obj ((F.rightDerived' q).obj X) := by
  apply page₂Iso

-- the spectral sequence converges to `R^{p + q}(F ⋙ G)(X)`
noncomputable example :
    (grothendieckSpectralSequence F G X).StronglyConvergesTo
      CohomologicalSpectralSequenceNat.stripes
      (fun n => ((F ⋙ G).rightDerived' n).obj X) := by
  apply stronglyConvergesTo

end GrothendieckSpectralSequence

end FormalizationOfDerivedCategories
