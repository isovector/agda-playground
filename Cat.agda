{-# OPTIONS --type-in-type #-}

module Cat where

record Equiv {obj : Set} (_≈_ : obj → obj → Set) : Set where
  field
    ≈-refl : ∀ {f} → f ≈ f 
    ≈-sym : ∀ {f g} → f ≈ g → g ≈ f
    ≈-trans : ∀ {f g h} → f ≈ g → g ≈ h → f ≈ h

record Cat : Set where
  infixr 9 _∘_
  infixr 5 _≈_
  infixr 1 _⇒_
  field
    obj : Set
    _⇒_ : obj → obj → Set

    id : {a : obj} → a ⇒ a
    _∘_ : {a b c : obj} → (b ⇒ c) → (a ⇒ b) → (a ⇒ c)
    _≈_ : {a b : obj} → (f g : a ⇒ b) → Set

    idᴸ : {a b : obj} → {f : a ⇒ b} → id ∘ f ≈ f
    idᴿ : {a b : obj} → {f : a ⇒ b} → f ≈ f ∘ id
    ∘-assoc : {a b c d : obj} → {f : a ⇒ b} → {g : b ⇒ c} → {h : c ⇒ d} → h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f

    ≈-equiv : ∀ {x y} → Equiv (_≈_ {x} {y})


record ProductCat : Set where
  infix 6 _×_
  infix 6 _&&&_
  field
    cat : Cat
  open Cat cat public
  field
    _×_ : obj → obj → obj 
    _&&&_ : ∀ {A B C} → (A ⇒ B) → (A ⇒ C) → (A ⇒ B × C)
    fst : ∀ {A B} → A × B ⇒ A
    snd : ∀ {A B} → A × B ⇒ B
    ump : ∀ {A B C} {f g} {h : A ⇒ B × C} → (fst ∘ h ≈ f) → (snd ∘ h ≈ g) → (h ≈ f &&& g)


module _ {cat : ProductCat} where
  open ProductCat cat

  swap : ∀ {A B} → A × B ⇒ B × A
  swap = snd &&& fst

  reassoc : ∀ {A B C} → (A × B) × C ⇒ A × (B × C)
  reassoc = fst ∘ fst &&& (snd ∘ fst &&& snd)

  reassoc' : ∀ {A B C} → A × (B × C) ⇒ (A × B) × C
  reassoc' = (fst &&& fst ∘ snd) &&& snd ∘ snd

