/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.FeynmanDiagrams.Momentum
import HepLean.FeynmanDiagrams.Display
/-!
# Feynman diagrams in Phi^4 theory

The aim of this file is to start building up the theory of Feynman diagrams in the context of
Phi^4 theory.


-/


namespace PhiFour
open CategoryTheory
open FeynmanDiagram
open PreFeynmanRule

/-- The pre-Feynman rules for `Phi^4` theory. -/
@[simps!]
def phi4PreFeynmanRules : PreFeynmanRule where
  /- There is only 1 type of `half-edge`. -/
  HalfEdgeLabel := Fin 1
  /- There is only 1 type of `edge`. -/
  EdgeLabel := Fin 1
  /- There are two types of `vertex`, external `0` and internal `1`. -/
  VertexLabel := Fin 2
  edgeLabelMap x :=
    match x with
    | 0 => Over.mk ![0, 0]
  vertexLabelMap x :=
    match x with
    | 0 => Over.mk ![0]
    | 1 => Over.mk ![0, 0, 0, 0]

instance (a : ℕ) : OfNat phi4PreFeynmanRules.EdgeLabel a where
  ofNat := (a : Fin _)

instance (a : ℕ) : OfNat phi4PreFeynmanRules.HalfEdgeLabel a where
  ofNat := (a : Fin _)

instance (a : ℕ) : OfNat phi4PreFeynmanRules.VertexLabel a where
  ofNat := (a : Fin _)


instance : IsFinitePreFeynmanRule phi4PreFeynmanRules where
  edgeLabelDecidable :=  instDecidableEqFin _
  vertexLabelDecidable := instDecidableEqFin _
  halfEdgeLabelDecidable := instDecidableEqFin _
  vertexMapFintype := fun v =>
    match v with
    | 0 => Fin.fintype _
    | 1  => Fin.fintype _
  edgeMapFintype := fun v =>
    match v with
    | 0 => Fin.fintype _
  vertexMapDecidable := fun v =>
    match v with
    | 0 => instDecidableEqFin _
    | 1  => instDecidableEqFin _
  edgeMapDecidable := fun v =>
    match v with
    | 0 => instDecidableEqFin _

/-!

## The figure eight diagram

This section provides an example of the use of Feynman diagrams in HepLean.

-/
section Example

/-- The figure eight Feynman diagram. -/
abbrev figureEight : FeynmanDiagram phi4PreFeynmanRules :=
  mk'
    ![0, 0] -- edges
    ![1] -- one internal vertex
    ![⟨0, 0, 0⟩, ⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 1, 0⟩] -- four half-edges
    (by decide) -- the condition to form a Feynman diagram.

/-- `figureEight` is connected. We can get this from
  `#eval Connected figureEight`. -/
lemma figureEight_connected : Connected figureEight := by decide

/-- The symmetry factor of `figureEight` is 8. We can get this from
  `#eval symmetryFactor figureEight`. -/
lemma figureEight_symmetryFactor : symmetryFactor figureEight = 8 := by decide

/--
  The number of loop of the `figureEight` Feynman diagram is `2`.
  To prove this we use the matrix obtained from
  `#eval figureEight.adjacencyLinePlus2IString (Equiv.refl _)`
  and find its eigenvectors and eigenvalues in a computer algebra system
  (such as Mathematica).
  These eigvectors and eigenvalues are then put into the theory
  `figureEight.numberOfLoops_eigenvectors` in the order
  - eigenvectors with zero eigenvalues
  - eigenvectors with non-zero eigenvalues
  - corresponding non-zero eigenvalues.

-/
lemma figureEight_numberOfLoops : figureEight.numberOfLoops = 2 := by
  rw [figureEight.numberOfLoops_eigenvectors ![![0, 0, -1, 1], ![-1, 1, 0, 0]]
    ![![1, 1, 1, 1], ![-1, -1, 1, 1]] ![6, 2] (by decide) (by decide)]
  decide

/-
A Feynman diagram can be displayed using e.g.:

`#html figureEight.toDOTHTML (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)`

-/

end Example
/-!

## A more complicated example


-/

section Example

abbrev propogator : FeynmanDiagram phi4PreFeynmanRules :=
  mk'
    ![0, 0, 0, 0]
    ![1, 1]
    ![⟨0, 0, 0⟩, ⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 1, 1⟩, ⟨0, 2, 0⟩, ⟨0, 2, 1⟩, ⟨0, 3, 1⟩, ⟨0, 3, 1⟩]
    (by decide)


#eval propogator.adjacencyLinePlus2IString (Equiv.refl _)

def feynmanDiagramExample2 : FeynmanDiagram phi4PreFeynmanRules :=
  mk'
    ![0, 0, 0, 0, 0, 0, 0]
    ![0, 0, 1, 1, 1]
    ![⟨0, 0, 0⟩, ⟨0, 0, 1⟩,  ⟨0, 1, 2⟩, ⟨0, 1, 2⟩,
    ⟨0, 2, 2⟩, ⟨0, 2, 3⟩, ⟨0, 3, 2⟩, ⟨0, 3, 3⟩, ⟨0, 4, 3⟩, ⟨0, 4, 3⟩,
    ⟨0, 5, 4⟩, ⟨0, 5, 4⟩, ⟨0, 6, 4⟩, ⟨0, 6, 4⟩]
    (by decide)

instance : IsFiniteDiagram feynmanDiagramExample2 :=
  FeynmanDiagram.instIsFiniteDiagramMk'OfFintypeOfDecidableEq _ _ _ _


/-- `feynmanDiagramExample2` is not connected. We can get this from
  `#eval Connected figureEight`. -/
lemma feynmanDiagramExample2_connected : ¬ Connected feynmanDiagramExample2 := by decide



end Example


end PhiFour
