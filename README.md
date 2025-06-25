# Formalization of derived categories in Lean/mathlib

This project contains a Lean file [LeanDerivedCategories.lean](https://github.com/joelriou/lean-derived-categories/blob/main/LeanDerivedCategories.lean)
which accompanies the paper [Formalization of derived categories in Lean/Mathlib](https://hal.science/hal-04546712) by Joël Riou.
This file follows the same structure as the paper and is meant to facilitate the cross-references between the mathematical text and the corresponding definitions in the Lean code, which is part of the mathlib branch [jriou_localization](https://github.com/leanprover-community/mathlib4/pull/25848).

## Installation instructions

* [Get a working Lean installation](https://leanprover-community.github.io/get_started.html)
* `git clone https://github.com/joelriou/lean-derived-categories.git`
* `cd lean-derived-categories`
* `lake exe cache get` (if this does not work, do `lake build`, which shall take a certain amount of time)
* launch `VS code` on this directory
