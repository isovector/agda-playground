{-# OPTIONS --type-in-type #-}

import Data.Nat
import Data.Product
import Data.Sum
import Data.Bool
import Data.Vec as Vec
import Relation.Binary.PropositionalEquality as Eq
import Data.Unit
open Data.Unit
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open Data.Nat
open Data.Bool using (Bool; true; false)
open Data.Product
open Data.Sum
open Vec using (Vec; _∷_; [])
import Data.Nat.Properties
open Data.Nat.Properties using (⊔-comm; +-comm)

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


record Embed (A : Set) : Set where
  field
    size : ℕ
    embed : A → Vec Bool size
    reify : Vec Bool size → A
    reify-embed : (x : A) → reify (embed x) ≡ x

take : ∀ {A} {m n} → Vec A (m + n) → Vec A m
take {m = zero} v = []
take {m = suc m} (x ∷ v) = x ∷ take v

drop : ∀ {A} {m n} → Vec A (m + n) → Vec A n
drop {m = zero} v = v
drop {m = suc m} (x ∷ v) = drop v


vec-take : ∀ {A} {m n} → {v2 : Vec A n} → (v1 : Vec A m) → take (v1 Vec.++ v2) ≡ v1
vec-take [] = refl
vec-take {m = suc m} {v2 = v2} (x ∷ v) =
  begin
      take ((x ∷ v) Vec.++ v2)
    ≡⟨⟩
      take (x ∷ (v Vec.++ v2))
    ≡⟨⟩
      x ∷ take (v Vec.++ v2)
    ≡⟨ cong (x ∷_) (vec-take v)⟩
      x ∷ v
    ∎


vec-drop : ∀ {A} {m n} → {v2 : Vec A n} → (v1 : Vec A m) → drop (v1 Vec.++ v2) ≡ v2
vec-drop [] = refl
vec-drop {m = suc m} {v2 = v2} (x ∷ v) =
  begin
      drop ((x ∷ v) Vec.++ v2)
    ≡⟨⟩
      drop (v Vec.++ v2)
    ≡⟨ vec-drop v ⟩
      v2
    ∎



instance 
  -- SumEmbed : ∀ {A B} → {{ea : Embed A}} → {{eb : Embed B}} → Embed (A ⊎ B)
  -- Embed.size (SumEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) = 1 + (Embed.size ea ⊔ Embed.size eb)
  -- Embed.embed (SumEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) (inj₁ x) rewrite ⊔-comm (Embed.size ea) (Embed.size eb) = false ∷ fill (Embed.size eb) (Embed.embed ea x) false
  -- Embed.embed (SumEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) (inj₂ y) = true ∷ fill (Embed.size ea) (Embed.embed eb y) false
  -- Embed.reify (SumEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) (false ∷ x) = inj₁ (Embed.reify ea (enough (Embed.size ea) x))
  -- Embed.reify (SumEmbed ⦃ ea = ea ⦄ {{ eb }}) (true ∷ y) rewrite ⊔-comm (Embed.size ea) (Embed.size eb) = inj₂ (Embed.reify eb (enough (Embed.size eb) y))
  -- Embed.reify-embed (SumEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) (inj₁ x) = {!!}
  -- Embed.reify-embed (SumEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) (inj₂ y) = 
  --   begin
  --     Embed.reify SumEmbed (Embed.embed SumEmbed (inj₂ y))
  --   ≡⟨⟩
  --     Embed.reify SumEmbed (true ∷ fill (Embed.size ea) (Embed.embed eb y) false)
  --   ≡⟨ {!!} ⟩
  --     inj₂ y
  --   ∎

  UnitEmbed : Embed ⊤
  UnitEmbed =
    record { size = 0
           ; embed = λ x → []
           ; reify = λ x → tt
           ; reify-embed = λ x → refl 
           }

  BoolEmbed : Embed Bool
  BoolEmbed =
    record { size = 1
           ; embed = _∷ []
           ; reify = Vec.head
           ; reify-embed = λ x → refl 
           }

  open Embed
  ProdEmbed : ∀ {A B} → {{ea : Embed A}} → {{eb : Embed B}} → Embed (A × B)
  size (ProdEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) = size ea + size eb
  embed (ProdEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) = λ (a , b) → embed ea a Vec.++ embed eb b 
  reify (ProdEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) = λ v → reify ea (take v) , reify eb (drop v)
  reify-embed (ProdEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) (a , b) =
    let v = embed ea a Vec.++ embed eb b
        embeda = embed ea a 
        embedb = embed eb b
    in
    begin
      reify ProdEmbed (embed ProdEmbed (a , b))
    ≡⟨⟩
      reify ProdEmbed v
    ≡⟨⟩
      reify ea (take v) , reify eb (drop v)
    ≡⟨ cong (λ x → reify ea x , reify eb (drop v) ) (vec-take embeda) ⟩
      reify ea embeda , reify eb (drop v)
    ≡⟨ cong (λ x → reify ea embeda , reify eb x) (vec-drop embeda) ⟩
      reify ea embeda , reify eb embedb
    ≡⟨ cong (Data.Product._, (reify eb embedb)) (reify-embed ea a) ⟩
      a , reify eb embedb
    ≡⟨ cong (a Data.Product.,_) (reify-embed eb b) ⟩
      a , b
    ∎
