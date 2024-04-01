/-

This files accompanies the paper _Formalization of derived categories in Lean/Mathlib_
by Joël Riou.

-/

import Mathlib.Algebra.Homology.DerivedCategory.Basic

universe w v u

open CategoryTheory

namespace FormalizationOfDerivedCategories

/-! # 2. Homology and diagram chasing in general abelian categories -/

/-! # 2.1 The homology refactor -/

/-! # 2.2 Diagram chasing -/
section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! # 2.2.2 -/

#check epi_iff_surjective_up_to_refinements
#check ShortComplex.exact_iff_exact_up_to_refinements

end

/-! # 3. Localizaton of categories -/

/-- Lemma 3.4: If `L : C ⥤ D` is a localization functor for a class of morphisms `W`,
then for any category `E`, the composition with `L` induces an equivalence of categories
from the category of functors `D ⥤ E` into the full subcategory of `C ⥤ E`
consisting of functors which inverts `W`. -/
noncomputable example {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] :
    (D ⥤ E) ≌ W.FunctorsInverting E :=
  Localization.functorEquivalence L W E


end FormalizationOfDerivedCategories
