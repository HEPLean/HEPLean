/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.StandardModel.Basic
/-!
# The Clifford Algebra

This file defines the Gamma matrices.

## TODO

- Prove that the algebra generated by the gamma matrices is ismorphic to the
  Clifford algebra assocaited with spacetime.
- Include relations for gamma matrices.
-/

namespace StandardModel
open Complex

noncomputable section diracRepresentation

def γ0 : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, -1]]

def γ1 : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0, 0, 0, 1], ![0, 0, 1, 0], ![0, -1, 0, 0], ![-1, 0, 0, 0]]

def γ2 : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0, 0, 0, - I], ![0, 0, I, 0], ![0, I, 0, 0], ![-I, 0, 0, 0]]

def γ3 : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0, 0, 1, 0], ![0, 0, 0, -1], ![-1, 0, 0, 0], ![0, 1, 0, 0]]

def γ5 : Matrix (Fin 4) (Fin 4) ℂ := I • (γ0 * γ1 * γ2 * γ3)

@[simp]
def γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := ![γ0, γ1, γ2, γ3]


namespace γ

open spaceTime

variable (μ ν : Fin 4)

@[simp]
def γSet : Set (Matrix (Fin 4) (Fin 4) ℂ) := {γ i | i : Fin 4}

lemma γ_in_γSet (μ : Fin 4) : γ μ ∈ γSet := by
  simp [γSet]

def diracAlgebra : Subalgebra ℝ (Matrix (Fin 4) (Fin 4) ℂ) :=
  Algebra.adjoin ℝ γSet

lemma γSet_subset_diracAlgebra : γSet ⊆ diracAlgebra :=
  Algebra.subset_adjoin

lemma γ_in_diracAlgebra (μ : Fin 4) : γ μ ∈ diracAlgebra :=
  γSet_subset_diracAlgebra (γ_in_γSet μ)

end γ

end diracRepresentation
end StandardModel
