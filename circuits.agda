{-# OPTIONS --type-in-type #-}

import Data.Nat
import Data.Product
import Data.Sum
import Data.Bool
import Data.Vec as Vec
import Relation.Binary.PropositionalEquality as Eq
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

fill : {A : Set} → {n : ℕ} → (m : ℕ) → Vec A n → A → Vec A (m ⊔ n)
fill zero v a = v
fill {n = zero} (suc m) v a rewrite ⊔-comm (suc m) zero = Vec.replicate a
fill {n = suc n} (suc m) (x ∷ v) a = x ∷ fill m v a

enough : {A : Set} → {n : ℕ} → (m : ℕ) → Vec A (m ⊔ n) → Vec A (m)
enough {n = zero} m v rewrite ⊔-comm m zero = v
enough {n = suc n} zero v = []
enough {n = suc n} (suc m) (x ∷ v) = x ∷ enough m v



record Embed (A : Set) : Set where
  field
    size : ℕ
    embed : A → Vec Bool size
    reify : Vec Bool size → A
    reify-embed : (x : A) → reify (embed x) ≡ x

take≤ : ∀ {A} {m n} → m ≤ n → Vec A n → Vec A m
take≤ z≤n v = []
take≤ (s≤s mltn) (x ∷ v) = x ∷ take≤ mltn v

drop≤ : ∀ {A} {m n} → m ≤ n → Vec A n → Vec A (n ∸ m)
drop≤ z≤n v = v
drop≤ (s≤s nltm) (x ∷ v) = drop≤ nltm v


vec-take : ∀ {A} {m n} → {v2 : Vec A n} → (v1 : Vec A m) → Vec.take m (v1 Vec.++ v2) ≡ v1
vec-take [] = refl
vec-take {m = suc m} {v2 = v2} (x ∷ v) =
  begin
      Vec.take (suc m) ((x ∷ v) Vec.++ v2)
    ≡⟨⟩
      Vec.take (suc m) (x ∷ (v Vec.++ v2))
    ≡⟨ {!!} ⟩
      x ∷ Vec.take m (v Vec.++ v2)
    ≡⟨ cong (x ∷_) (vec-take v)⟩
      x ∷ v
    ∎


vec-drop : ∀ {A} {m n} → {v2 : Vec A n} → (v1 : Vec A m) → Vec.drop m (v1 Vec.++ v2) ≡ v2
vec-drop [] = refl
vec-drop (x ∷ v) = cong _ (vec-drop v)


instance 
  SumEmbed : ∀ {A B} → {{ea : Embed A}} → {{eb : Embed B}} → Embed (A ⊎ B)
  Embed.size (SumEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) = 1 + (Embed.size ea ⊔ Embed.size eb)
  Embed.embed (SumEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) (inj₁ x) rewrite ⊔-comm (Embed.size ea) (Embed.size eb) = false ∷ fill (Embed.size eb) (Embed.embed ea x) false
  Embed.embed (SumEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) (inj₂ y) = true ∷ fill (Embed.size ea) (Embed.embed eb y) false
  Embed.reify (SumEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) (false ∷ x) = inj₁ (Embed.reify ea (enough (Embed.size ea) x))
  Embed.reify (SumEmbed ⦃ ea = ea ⦄ {{ eb }}) (true ∷ y) rewrite ⊔-comm (Embed.size ea) (Embed.size eb) = inj₂ (Embed.reify eb (enough (Embed.size eb) y))
  Embed.reify-embed (SumEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) (inj₁ x) = {!!}

  Embed.reify-embed (SumEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) (inj₂ y) = 
    begin
      Embed.reify SumEmbed (Embed.embed SumEmbed (inj₂ y))
    ≡⟨⟩
      Embed.reify SumEmbed (true ∷ fill (Embed.size ea) (Embed.embed eb y) false)
    ≡⟨ {!!} ⟩
      inj₂ y
    ∎

  BoolEmbed : Embed Bool
  BoolEmbed =
    record { size = 1
           ; embed = _∷ []
           ; reify = Vec.head
           ; reify-embed = λ x → refl 
           }

  ProdEmbed : ∀ {A B} → {{ea : Embed A}} → {{eb : Embed B}} → Embed (A × B)
  Embed.size (ProdEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) = Embed.size ea + Embed.size eb
  Embed.embed (ProdEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) = λ (a , b) → Embed.embed ea a Vec.++ Embed.embed eb b 
  Embed.reify (ProdEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) = λ v →
                   let size = Embed.size ea
                       a = Vec.take size v
                       b = Vec.drop size v
                     in Embed.reify ea a , Embed.reify eb b
  Embed.reify-embed (ProdEmbed ⦃ ea = ea ⦄ ⦃ eb ⦄) (a , b) =
    begin
      Embed.reify ProdEmbed (Embed.embed ProdEmbed (a , b))
    ≡⟨⟩
      Embed.reify ProdEmbed (Embed.embed ea a Vec.++ Embed.embed eb b)
    ≡⟨⟩
      let v = Embed.embed ea a Vec.++ Embed.embed eb b
       in Embed.reify ea (Vec.take (Embed.size ea) v) , Embed.reify eb (Vec.drop (Embed.size ea) v)
    ≡⟨ cong _ (vec-take (Embed.embed ea a)) ⟩
      let v = Embed.embed ea a Vec.++ Embed.embed eb b
       in Embed.reify ea (Embed.embed ea a) , Embed.reify eb (Vec.drop (Embed.size ea) v)
    ≡⟨ cong _ (vec-drop (Embed.embed eb b)) ⟩
      Embed.reify ea (Embed.embed ea a) , Embed.reify eb (Embed.embed eb b)  
    ≡⟨ cong (_, _) (Embed.reify-embed ea _) ⟩
      a , Embed.reify eb (Embed.embed eb b)  
    ≡⟨ cong (_ ,_) (Embed.reify-embed eb b) ⟩
      a , b
      ∎


