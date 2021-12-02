{-# OPTIONS --type-in-type #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)

record Equiv {obj : Set} (_≈_ : obj → obj → Set) : Set where
  field
    ≈-refl : ∀ {f} → f ≈ f 
    ≈-sym : ∀ {f g} → f ≈ g → g ≈ f
    ≈-trans : ∀ {f g h} → f ≈ g → g ≈ h → f ≈ h

record Cat {obj : Set} (_⇒_ : obj → obj → Set) : Set where
  infixr 9 _∘_
  infixr 5 _≈_
  field
    id : {a : obj} → a ⇒ a
    _∘_ : {a b c : obj} → (b ⇒ c) → (a ⇒ b) → (a ⇒ c)
    _≈_ : {a b : obj} → (f g : a ⇒ b) → Set

    idᴸ : {a b : obj} → {f : a ⇒ b} → id ∘ f ≈ f
    idᴿ : {a b : obj} → {f : a ⇒ b} → f ≈ f ∘ id
    ∘-assoc : {a b c d : obj} → {f : a ⇒ b} → {g : b ⇒ c} → {h : c ⇒ d} → h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f

    ≈-equiv : ∀ {x y} → Equiv (_≈_ {x} {y})

data _⇛_  : Set → Set → Set where
  free-id : {a : Set} → a ⇛ a
  comp : {a b c : Set} → (b ⇛ c) → (a ⇛ b) → (a ⇛ c)

eval : {A B C : Set} → (B ⇛ C) → (A ⇛ B) → (A ⇛ C)
eval free-id f = f
eval (comp h g) f = eval h (eval g f)

normalize : ∀ {A B} → (A ⇛ B) → (A ⇛ B)
normalize f = eval f free-id

record _≅_ {A B : Set} (f g : A ⇛ B) : Set where
  constructor norm-refl
  field
    nf-eq : normalize f ≡ normalize g
      

⇛-cat : Cat _⇛_ 
⇛-cat = record
  { id = free-id
  ; _∘_ = comp
  ; _≈_ = _≅_
  ; idᴸ = norm-refl refl
  ; idᴿ = norm-refl refl
  ; ∘-assoc = norm-refl refl
  ; ≈-equiv = record
    { ≈-refl = norm-refl refl
    ; ≈-sym = λ (norm-refl x) → norm-refl (sym x)
    ; ≈-trans = λ (norm-refl f) (norm-refl g) → norm-refl (Eq.trans f g)
    }
  }

