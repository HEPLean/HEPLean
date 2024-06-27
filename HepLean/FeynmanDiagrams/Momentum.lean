/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.FeynmanDiagrams.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Rank
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.SesquilinearForm
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.RewriteSearch
/-!
# Momentum in Feynman diagrams

The aim of this file is to associate with each half-edge of a Feynman diagram a momentum,
and constrain the momentums based conservation at each vertex and edge.

The number of loops of a Feynman diagram is related to the dimension of the resulting
vector space.

## TODO

- Prove lemmas that make the calcuation of the number of loops of a Feynman diagram easier.

## Note

This section is non-computable as we depend on the norm on `F.HalfEdgeMomenta`.

-/


namespace FeynmanDiagram

open CategoryTheory
open PreFeynmanRule

variable {P : PreFeynmanRule} (F : FeynmanDiagram P) [IsFiniteDiagram F]

/-!

## Some aspects of graph theory

- TODO: Move this section.

-/

/-- The map from `Fin 2` to `Type` landing on `F.𝓔` and `F.𝓥`. -/
def graphVertexMap : Fin 2 → Type := fun i =>
  match i with
  | 0 => F.𝓔
  | 1 => F.𝓥

instance (i : Fin 2) : Fintype (graphVertexMap F i) :=
  match i with
  | 0 => IsFiniteDiagram.𝓔Fintype
  | 1 => IsFiniteDiagram.𝓥Fintype

noncomputable instance (i : Fin 2) : DecidableEq (graphVertexMap F i) :=
  match i with
  | 0 =>  IsFiniteDiagram.𝓔DecidableEq
  | 1 => IsFiniteDiagram.𝓥DecidableEq

/-- The type of all vertices (including centers of edges `F.𝓔`) and
  actual Feynman-diagram vertices `F.𝓥`. -/
def graphVertex : Type := Σ i, F.graphVertexMap i

instance : Fintype F.graphVertex := Sigma.instFintype

def graphVertexEquivSum : F.graphVertex ≃ F.𝓔 ⊕ F.𝓥 where
  toFun x := match x with
    | ⟨0, x⟩ => Sum.inl x
    | ⟨1, x⟩ => Sum.inr x
  invFun x := match x with
    | Sum.inl x => ⟨0, x⟩
    | Sum.inr x => ⟨1, x⟩
  left_inv a := by
    simp_all only
    split <;> rename_i x x_1 heq <;> rcases x <;>
       split at heq <;> simp_all only [Sum.inl.injEq, Sum.inr.injEq]
  right_inv a := by
    rcases a <;> simp_all only


/-- The incidence matrix for the `F.𝓔`-type vertices of a Feynman diagram. -/
def incidenceMatrix𝓔 : Matrix F.𝓱𝓔 F.𝓔 ℤ :=
  fun i j => if F.𝓱𝓔To𝓔.hom i = j then 1 else 0

/-- The incidence matrix for the `F.𝓥`-vertices of a Feynman diagram. -/
def incidenceMatrix𝓥 : Matrix F.𝓱𝓔 F.𝓥 ℤ :=
  fun i j => if F.𝓱𝓔To𝓥.hom i = j then 1 else 0

/-- The (unoriented) incidence matrix for a Feynman diagram, considered as an undirected graph. -/
def incidenceMatrix : Matrix F.𝓱𝓔 F.graphVertex ℤ := fun i j =>
  match j with
  | ⟨0, j'⟩ => F.incidenceMatrix𝓔 i j'
  | ⟨1, j'⟩ => F.incidenceMatrix𝓥 i j'


/--
 The matrix representing the adjacency matrix of the line graph of a Feynman diagram,
 plus 2 × the identity.

 The rank of this matrix is the same as the rank of the incidence matrix, however
 it is somewhat easier to deal with since it is indexed soely by half-edges.

 The rank of this matrix is related to the number of loops in a Feynman diagram.
 -/
def adjacencyLinePlus2I : Matrix F.𝓱𝓔 F.𝓱𝓔 ℤ := F.incidenceMatrix * F.incidenceMatrix.transpose

/-- Given an equivalence `F.𝓱𝓔 ≃ Fin n`, this converts `adjacencyLinePlus2I` into a
  string.

  This is provided so that the eigenvectors and eigenvalues of `adjacencyLinePlus2I` can be
  found using a computer algebra system (e.g. Mathematica), and then imported back into Lean.
  -/
def adjacencyLinePlus2IString {n : ℕ} (e : F.𝓱𝓔 ≃ Fin n) : String :=
  let M (r : F.𝓱𝓔) :=
    List.map (fun c => toString (F.adjacencyLinePlus2I r (e.symm c))) (Fin.list n)
  let X :=
    List.map (fun r => String.intercalate ", " $ M (e.symm r)) (Fin.list n)
  "{{" ++ String.intercalate "}, {" X++ "}}"



/-!

## Vector spaces associated with momenta in Feynman diagrams.

We define the vector space associated with momenta carried by half-edges,
outflowing momenta of edges, and inflowing momenta of vertices.

We define the direct sum of the edge and vertex momentum spaces.

-/

/-- The type which assocaites to each half-edge a `1`-dimensional vector space.
 Corresponding to that spanned by its momentum.  -/
abbrev HalfEdgeMomenta := EuclideanSpace ℝ F.𝓱𝓔


/-- The type which assocaites to each ege a `1`-dimensional vector space.
 Corresponding to that spanned by its total outflowing momentum.  -/
def EdgeMomenta : Type := F.𝓔 → ℝ

instance : AddCommGroup F.EdgeMomenta := Pi.addCommGroup

noncomputable instance : Module ℝ F.EdgeMomenta := Pi.module _ _ _
/-- The standard `Pi` basis on `F.EdgeMomenta`. -/
noncomputable def basisEdgeMomenta : Basis F.𝓔 ℝ F.EdgeMomenta := Pi.basisFun _ _

/-- The type which assocaites to each ege a `1`-dimensional vector space.
 Corresponding to that spanned by its total inflowing momentum.  -/
def VertexMomenta : Type := F.𝓥 → ℝ

instance : AddCommGroup F.VertexMomenta := Pi.addCommGroup

noncomputable instance : Module ℝ F.VertexMomenta := Pi.module _ _ _

/-- The standard `Pi` basis on `F.VertexMomenta`. -/
noncomputable def basisVertexMomenta : Basis F.𝓥 ℝ F.VertexMomenta := Pi.basisFun _ _

/-- The map from `Fin 2` to `Type` landing on `EdgeMomenta` and `VertexMomenta`. -/
def EdgeVertexMomentaMap : Fin 2 → Type := fun i =>
  match i with
  | 0 =>  F.EdgeMomenta
  | 1 =>  F.VertexMomenta

instance (i : Fin 2) : AddCommGroup (EdgeVertexMomentaMap F i) :=
  match i with
  | 0 => instAddCommGroupEdgeMomenta F
  | 1 => instAddCommGroupVertexMomenta F

noncomputable instance (i : Fin 2) : Module ℝ (EdgeVertexMomentaMap F i) :=
  match i with
  | 0 => instModuleRealEdgeMomenta F
  | 1 => instModuleRealVertexMomenta F

/-- The direct sum of `EdgeMomenta` and `VertexMomenta`.-/
def EdgeVertexMomenta : Type := ∀ i : Fin 2, (EdgeVertexMomentaMap F) i

instance : AddCommGroup F.EdgeVertexMomenta := Pi.addCommGroup

noncomputable instance : Module ℝ F.EdgeVertexMomenta := Pi.module _ _ _

noncomputable def basisEdgeVertexMomentaMap : (i : Fin 2) →
  Basis (F.graphVertexMap i) ℝ (F.EdgeVertexMomentaMap i) :=
  fun i => match i with
  | 0 => F.basisEdgeMomenta
  | 1 => F.basisVertexMomenta


noncomputable def basisEdgeVertexMomenta :
    Basis (Σ i, F.graphVertexMap i) ℝ F.EdgeVertexMomenta :=
    Pi.basis F.basisEdgeVertexMomentaMap


/-!

## Linear maps between the vector spaces.

We define various maps into `F.HalfEdgeMomenta`.

In particular, we define a map from `F.EdgeVertexMomenta` to `F.HalfEdgeMomenta`. This
map represents the space orthogonal (with respect to the standard Euclidean inner product)
to the allowed momenta of half-edges (up-to an offset determined by the
 external momenta).

The number of loops of a diagram is defined as the number of half-edges minus
the rank of this matrix.

-/

/-- The linear map from `F.EdgeMomenta` to `F.HalfEdgeMomenta` induced by
  the map `F.𝓱𝓔To𝓔.hom`. -/
def edgeToHalfEdgeMomenta : F.EdgeMomenta →ₗ[ℝ] F.HalfEdgeMomenta where
  toFun x := x ∘ F.𝓱𝓔To𝓔.hom
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

/-- The matrix corresponding to `edgeToHalfEdgeMomenta` in the standard basis. -/
@[simp]
noncomputable def edgeToHalfEdgeMomentaMatrix : Matrix F.𝓱𝓔 F.𝓔 ℝ :=
  (LinearMap.toMatrix F.basisEdgeMomenta
  (EuclideanSpace.basisFun F.𝓱𝓔 ℝ).toBasis) F.edgeToHalfEdgeMomenta

lemma edgeToHalfEdgeMomenta_eq_edgeToHalfEdgeℤ :
    F.edgeToHalfEdgeMomentaMatrix = F.incidenceMatrix𝓔.map (Int.cast : ℤ → ℝ) := by
  apply Matrix.ext
  intro i j
  simp only [edgeToHalfEdgeMomentaMatrix, LinearMap.toMatrix, basisEdgeMomenta,
    EuclideanSpace.basisFun, LinearIsometryEquiv.refl, OrthonormalBasis.coe_toBasis_repr,
    LinearEquiv.trans_apply, LinearMap.toMatrix'_apply, LinearEquiv.arrowCongr_apply,
    Basis.equivFun_symm_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, Matrix.map_apply, incidenceMatrix𝓔, Functor.const_obj_obj, Int.cast_ite,
    Int.cast_one, Int.cast_zero]
  erw [LinearEquiv.refl_apply, Pi.basisFun_apply]
  rw [LinearMap.stdBasis_apply, ← EuclideanSpace.single_apply]
  rfl

/-- The linear map from `F.VertexMomenta` to `F.HalfEdgeMomenta` induced by
  the map `F.𝓱𝓔To𝓥.hom`. -/
def vertexToHalfEdgeMomenta : F.VertexMomenta →ₗ[ℝ] F.HalfEdgeMomenta where
  toFun x := x ∘ F.𝓱𝓔To𝓥.hom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The matrix corresponding to `vertexToHalfEdgeMomenta` in the standard basis. -/
@[simp]
noncomputable def vertexToHalfEdgeMomentaMatrix : Matrix F.𝓱𝓔 F.𝓥 ℝ :=
  (LinearMap.toMatrix F.basisVertexMomenta
  (EuclideanSpace.basisFun F.𝓱𝓔 ℝ).toBasis) F.vertexToHalfEdgeMomenta

lemma vertexToHalfEdgeMomenta_eq_incidenceMatrix𝓥 :
    F.vertexToHalfEdgeMomentaMatrix = F.incidenceMatrix𝓥.map (Int.cast : ℤ → ℝ) := by
  apply Matrix.ext
  intro i j
  simp only [vertexToHalfEdgeMomentaMatrix, LinearMap.toMatrix, EuclideanSpace.basisFun,
    LinearIsometryEquiv.refl, OrthonormalBasis.coe_toBasis_repr, LinearEquiv.trans_apply,
    LinearMap.toMatrix'_apply, LinearEquiv.arrowCongr_apply, Basis.equivFun_symm_apply, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Matrix.map_apply,
    incidenceMatrix𝓥, Functor.const_obj_obj, Int.cast_ite, Int.cast_one, Int.cast_zero]
  erw [LinearEquiv.refl_apply, Pi.basisFun_apply]
  rw [LinearMap.stdBasis_apply, ← EuclideanSpace.single_apply]
  rfl

/-- The linear map from `F.EdgeVertexMomenta` to `F.HalfEdgeMomenta` induced by
   `F.edgeToHalfEdgeMomenta` and `F.vertexToHalfEdgeMomenta`. -/
noncomputable def edgeVertexToHalfEdgeMomenta : F.EdgeVertexMomenta →ₗ[ℝ] F.HalfEdgeMomenta :=
  (DirectSum.toModule ℝ (Fin 2) F.HalfEdgeMomenta
  (fun i => match i with | 0 => F.edgeToHalfEdgeMomenta | 1 => F.vertexToHalfEdgeMomenta))
  ∘ₗ (DirectSum.linearEquivFunOnFintype ℝ (Fin 2) F.EdgeVertexMomentaMap).symm.toLinearMap

lemma edgeVertexToHalfEdgeMomenta_apply_𝓔 (v : F.EdgeMomenta) :
  F.edgeVertexToHalfEdgeMomenta (Pi.single 0 v) = F.edgeToHalfEdgeMomenta v := by
  rw [← DirectSum.linearEquivFunOnFintype_lof ℝ ]
  rw [edgeVertexToHalfEdgeMomenta]
  simp only [LinearEquiv.coe_coe, LinearMap.coe_comp,
    Function.comp_apply]
  erw [LinearEquiv.symm_apply_apply ]
  exact DirectSum.toModule_lof _ _ _

lemma edgeVertexToHalfEdgeMomenta_apply_𝓥 (v : F.VertexMomenta) :
  F.edgeVertexToHalfEdgeMomenta (Pi.single 1 v) = F.vertexToHalfEdgeMomenta v := by
  rw [← DirectSum.linearEquivFunOnFintype_lof ℝ ]
  rw [edgeVertexToHalfEdgeMomenta]
  simp only [LinearEquiv.coe_coe, LinearMap.coe_comp,
    Function.comp_apply]
  erw [LinearEquiv.symm_apply_apply ]
  exact DirectSum.toModule_lof _ _ _


/-- The matrix corresponding to `edgeVertexToHalfEdgeMomentaMatrix` in the standard basis. -/
@[simp]
noncomputable def edgeVertexToHalfEdgeMomentaMatrix : Matrix F.𝓱𝓔 F.graphVertex ℝ  :=
  (LinearMap.toMatrix F.basisEdgeVertexMomenta
  (EuclideanSpace.basisFun F.𝓱𝓔 ℝ).toBasis) F.edgeVertexToHalfEdgeMomenta


lemma edgeVertexToHalfEdgeMomentaMatrix_on_𝓔 (i : F.𝓱𝓔) (j : F.𝓔) :
    F.edgeVertexToHalfEdgeMomentaMatrix i ⟨0, j⟩ = F.edgeToHalfEdgeMomentaMatrix i j := by
  simp only [edgeVertexToHalfEdgeMomentaMatrix, edgeToHalfEdgeMomentaMatrix]
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  simp only [EuclideanSpace.basisFun, basisEdgeVertexMomenta,
    OrthonormalBasis.coe_toBasis_repr_apply, LinearIsometryEquiv.coe_refl, id_eq, basisEdgeMomenta]
  erw [Pi.basis_apply]
  rw [← edgeVertexToHalfEdgeMomenta_apply_𝓔]
  rfl

lemma edgeVertexToHalfEdgeMomentaMatrix_on_𝓥 (i : F.𝓱𝓔) (j : F.𝓥) :
    F.edgeVertexToHalfEdgeMomentaMatrix i ⟨1, j⟩ = F.vertexToHalfEdgeMomentaMatrix i j := by
  simp only [edgeVertexToHalfEdgeMomentaMatrix, vertexToHalfEdgeMomentaMatrix]
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  simp only [EuclideanSpace.basisFun, basisEdgeVertexMomenta,
    OrthonormalBasis.coe_toBasis_repr_apply, LinearIsometryEquiv.coe_refl, id_eq, basisEdgeMomenta]
  erw [Pi.basis_apply]
  rw [← edgeVertexToHalfEdgeMomenta_apply_𝓥]
  rfl

lemma edgeVertexToHalfEdgeMomentaMatrix_eq_incidenceMatrix :
    F.edgeVertexToHalfEdgeMomentaMatrix = F.incidenceMatrix.map (Int.cast : ℤ → ℝ) := by
  apply Matrix.ext
  intro i ⟨j1, j2⟩
  fin_cases j1
  erw [edgeVertexToHalfEdgeMomentaMatrix_on_𝓔]
  rw [edgeToHalfEdgeMomenta_eq_edgeToHalfEdgeℤ]
  rfl
  erw [edgeVertexToHalfEdgeMomentaMatrix_on_𝓥]
  rw [vertexToHalfEdgeMomenta_eq_incidenceMatrix𝓥]
  rfl

lemma edgeVertexToHalfEdgeMomentaMatrix_mul_transpose_eq_adjacencyLinePlus2I :
    F.edgeVertexToHalfEdgeMomentaMatrix * F.edgeVertexToHalfEdgeMomentaMatrix.transpose
    = F.adjacencyLinePlus2I.map (Int.cast : ℤ → ℝ) := by
  rw [edgeVertexToHalfEdgeMomentaMatrix_eq_incidenceMatrix]
  refine Matrix.ext ?_
  intro i j
  rw [Matrix.map_apply]
  rw [Matrix.mul_apply, adjacencyLinePlus2I, Matrix.mul_apply, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Matrix.map_apply, Matrix.transpose_apply, Int.cast_mul]



/-!

## Submodules

We define submodules of `F.HalfEdgeMomenta` which correspond to
the orthogonal space to allowed momenta (up-to an offset), and the space of
allowed momenta.

-/

/-- The submodule of `F.HalfEdgeMomenta` corresponding to the range of
 `F.edgeVertexToHalfEdgeMomenta`. -/
noncomputable def orthogHalfEdgeMomenta : Submodule ℝ F.HalfEdgeMomenta :=
  LinearMap.range F.edgeVertexToHalfEdgeMomenta

/-- The submodule of `F.HalfEdgeMomenta` corresponding to the allowed momenta. -/
noncomputable def allowedHalfEdgeMomenta : Submodule ℝ F.HalfEdgeMomenta :=
  F.orthogHalfEdgeMomentaᗮ

/-!

## Number of loops

We define the number of loops of a Feynman diagram as the dimension of the
allowed space of half-edge momenta.

-/

/-- The number of loops of a Feynman diagram. Defined as the dimension
  of the space of allowed Half-loop momenta. -/
noncomputable def numberOfLoops : ℕ := FiniteDimensional.finrank ℝ F.allowedHalfEdgeMomenta

/-!

## Lemmas regarding `numberOfLoops`

We now give a series of lemmas which be used to help calculate the number of loops
for specific Feynman diagrams.

The lemma `numberOfLoops_eigenvectors` is particularly useful in calculating the number
of loops for a given diagram.


-/

lemma numberOfLoops_eq_finrank_sub :
    F.numberOfLoops = Fintype.card F.𝓱𝓔 - FiniteDimensional.finrank ℝ F.orthogHalfEdgeMomenta := by
  apply Nat.eq_sub_of_add_eq
  rw [numberOfLoops, allowedHalfEdgeMomenta, add_comm, Submodule.finrank_add_finrank_orthogonal]
  exact finrank_euclideanSpace

lemma numberOfLoops_eq_card_sub_rank :
    F.numberOfLoops = Fintype.card F.𝓱𝓔 - F.edgeVertexToHalfEdgeMomentaMatrix.rank := by
  rw [numberOfLoops_eq_finrank_sub, orthogHalfEdgeMomenta]
  rw [Matrix.rank_eq_finrank_range_toLin _ (EuclideanSpace.basisFun F.𝓱𝓔 ℝ).toBasis
    F.basisEdgeVertexMomenta]
  erw [Matrix.toLin_toMatrix]

lemma numberOfLoops_of_adjacencyLinePlus2I_rank :
    F.numberOfLoops = Fintype.card F.𝓱𝓔 - (F.adjacencyLinePlus2I.map (Int.cast : ℤ → ℝ)).rank := by
  rw [numberOfLoops_eq_card_sub_rank, ← Matrix.rank_self_mul_transpose,
  edgeVertexToHalfEdgeMomentaMatrix_mul_transpose_eq_adjacencyLinePlus2I]



/-!

## Category theory

### TODO

- Complete this section.


-/

end FeynmanDiagram
