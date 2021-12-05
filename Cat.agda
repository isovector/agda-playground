{-# OPTIONS --type-in-type #-}

module Cat where

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
