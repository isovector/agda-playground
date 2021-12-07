{-# OPTIONS --type-in-type #-}

module Diagram where

open import Cat
open import Embed
open import Data.Vec using (Vec; []; _∷_; _++_)
open import Data.Nat
open import Data.Graph.Acyclic
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_ ; _∎; _≡⟨⟩_; step-≡)

Wire : (A : Set) → {{Embed A}} → Set → Set
Wire _ {{ea}} B = Vec B (Embed.size ea)

record Diagram (A B : Σ Set Embed) : Set where
  constructor diagram
  field
     wires : Wire (proj₁ A) {{proj₂ A}} ℕ → Wire (proj₁ B) {{proj₂ B}} ℕ

CatDiagram : Cat 
Cat.obj CatDiagram = Σ Set Embed
Cat._⇒_ CatDiagram = Diagram
Cat.id CatDiagram = diagram (λ x → x)
(CatDiagram Cat.∘ diagram g) (diagram f) = diagram (\wa → g (f wa))
Cat._≈_ CatDiagram = _≡_
Cat.idᴸ CatDiagram = refl
Cat.idᴿ CatDiagram = refl
Cat.∘-assoc CatDiagram = refl
Equiv.≈-refl (Cat.≈-equiv CatDiagram) = refl
Equiv.≈-sym (Cat.≈-equiv CatDiagram) = sym 
Equiv.≈-trans (Cat.≈-equiv CatDiagram) = trans

open ProductCat 

ProductCatDiagram : ProductCat
cat ProductCatDiagram = CatDiagram
(ProductCatDiagram ProductCat.× (Afst , Asnd)) (Bfst , Bsnd) = (Afst Data.Product.× Bfst) , ProdEmbed {_} {_} {{Asnd}} {{Bsnd}}
_&&&_ ProductCatDiagram = λ { (diagram f) (diagram g) → diagram λ x → f x ++ g x }
fst ProductCatDiagram = diagram (λ x → take x)
snd ProductCatDiagram = diagram (λ x → drop x)
ump ProductCatDiagram {f = f} {g} {h} fproof gproof = sym (
  begin
     (ProductCatDiagram &&& f) g
    ≡⟨ cong (λ v → (ProductCatDiagram &&& v) g) (sym fproof) ⟩
      (ProductCatDiagram &&& (ProductCatDiagram ∘ fst ProductCatDiagram) h) g
    ≡⟨ cong (λ v → (ProductCatDiagram &&& (ProductCatDiagram ∘ fst ProductCatDiagram) h) v) (sym gproof) ⟩
      (ProductCatDiagram &&& (ProductCatDiagram ∘ fst ProductCatDiagram) h) ((ProductCatDiagram ∘ snd ProductCatDiagram) h)
    ≡⟨⟩
      refl


    -- ≡⟨ cong (λ x → (ProductCatDiagram &&& (diagram (λ wa → take (Diagram.wires h wa)))) x) (sym gproof)⟩
    --   (ProductCatDiagram &&& (diagram (λ wa → take (Diagram.wires h wa)))) (diagram (λ wa → drop (Diagram.wires h wa)))
    -- ≡⟨⟩
    --   refl
      )

