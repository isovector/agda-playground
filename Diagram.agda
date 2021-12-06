{-# OPTIONS --type-in-type #-}

module Diagram where

open import Cat
open import Embed
open import Data.Vec using (Vec; []; _∷_)
open import Data.Nat
open import Data.Graph.Acyclic
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

Wire : (A : Set) → {{Embed A}} → Set → Set
Wire _ {{ea}} B = Vec B (Embed.size ea)

record Diagram (A B : Σ Set Embed) : Set where
  constructor diagram
  field
     wires : Wire (proj₁ A) {{proj₂ A}} ℕ → Wire (proj₁ B) {{proj₂ B}} ℕ

instance
  CatDiagram : Cat Diagram
  Cat.id CatDiagram = diagram (λ x → x)
  (CatDiagram Cat.∘ diagram g) (diagram f) = diagram (\wa → g (f wa))
  Cat._≈_ CatDiagram = _≡_
  Cat.idᴸ CatDiagram = refl
  Cat.idᴿ CatDiagram = refl
  Cat.∘-assoc CatDiagram = refl
  Equiv.≈-refl (Cat.≈-equiv CatDiagram) = refl
  Equiv.≈-sym (Cat.≈-equiv CatDiagram) = sym 
  Equiv.≈-trans (Cat.≈-equiv CatDiagram) = trans


