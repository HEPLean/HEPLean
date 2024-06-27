/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.FeynmanDiagrams.Basic
import ProofWidgets.Component.HtmlDisplay
import Lean.Widget.UserWidget
import ProofWidgets.Data.Html
open scoped ProofWidgets.Jsx
/-!

# Display of Feynman diagrams

This file provides a way to display Feynman diagrams.

The aim is to create a `DOT` file from the Feynman diagram.
This is then displayed using an api for `Graphviz`.

## TODO

- This currently only gives a very rough version of the diagram (no directed lines etc.).
  We should improve this based on the labels associated to each edge, and those
  associated to each vertex.
-/
namespace FeynmanDiagram

open CategoryTheory
open PreFeynmanRule

variable {P : PreFeynmanRule} (F : FeynmanDiagram P) [IsFiniteDiagram F]

/-- The Feynman diagram as a graph represented in the Dot format. -/
def toDOTString (I𝓱𝓔 : Fin (Fintype.card F.𝓱𝓔) ≃ F.𝓱𝓔 )(I𝓔 : Fin (Fintype.card F.𝓔) ≃ F.𝓔 )
    (I𝓥 : Fin (Fintype.card F.𝓥) ≃ F.𝓥) : String :=
  let Elist := List.map (fun r =>  "E" ++ toString r ++ "[shape=point, color = lightgrey];")
    (Fin.list (Fintype.card F.𝓔))
  let Estring := String.intercalate " " Elist
  let Vlist := List.map (fun r =>  "V" ++ toString r ++ "[shape=point];")
    (Fin.list (Fintype.card F.𝓥))
  let Vstring := String.intercalate " " Vlist
  let HEList := List.map (fun r =>  "E" ++ toString (I𝓔.symm (F.𝓱𝓔To𝓔.hom (I𝓱𝓔 r)))++ "--"
  ++ "V" ++ toString (I𝓥.symm (F.𝓱𝓔To𝓥.hom (I𝓱𝓔 r)))++ ";") (Fin.list (Fintype.card F.𝓱𝓔))
  let HEstring := String.intercalate " " HEList
  "{" ++ Estring ++ Vstring ++ HEstring ++ "}"

/-- The webaddress for the API showing the Feynman diagram. This uses `quickchart.io`. -/
def toDOTWebAddress (I𝓱𝓔 : Fin (Fintype.card F.𝓱𝓔) ≃ F.𝓱𝓔 )
  (I𝓔 : Fin (Fintype.card F.𝓔) ≃ F.𝓔 ) (I𝓥 : Fin (Fintype.card F.𝓥) ≃ F.𝓥 ) : String :=
   "https://quickchart.io/graphviz?layout=neato&graph=graph" ++ F.toDOTString I𝓱𝓔 I𝓔 I𝓥 ++ ""

/-- A turn the Feynman diagram into html. This can (usually) be viewed using
`#html F.toDOTHTML (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)` -/
def toDOTHTML (I𝓱𝓔 : Fin (Fintype.card F.𝓱𝓔) ≃ F.𝓱𝓔 )
  (I𝓔 : Fin (Fintype.card F.𝓔) ≃ F.𝓔 ) (I𝓥 : Fin (Fintype.card F.𝓥) ≃ F.𝓥 ) : ProofWidgets.Html :=
  <iframe src={F.toDOTWebAddress I𝓱𝓔 I𝓔 I𝓥 } width="100%" height="500px" frameborder="0"></iframe>



end FeynmanDiagram
