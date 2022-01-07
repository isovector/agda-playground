{-# OPTIONS --type-in-type #-}

module AddArrows where

import Data.Product
open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin; zero; suc; combine)
open import Cat2 using (COMMA; SET; ID=>; _[_>>_]; _[_,_])
open import Relation.Binary.PropositionalEquality public renaming (_≡_ to _==_; [_] to [[_]])
open import Tactic.Rewrite public using (cong!)
open import Function

infix 3 _done
infixr 2 _=[]_ step-=
infix 1 begin_

begin_ : {A : Set} -> A -> A
begin_ x = x

_=[]_ : {A : Set} (x : A) -> {y : A} -> x == y -> x == y
_=[]_ _ x = x

step-= : {A : Set} (x : A) -> {y z : A} -> y == z -> x == y -> x == z
step-= _ yz xy = trans xy yz

syntax step-= x yz xy = x =[ xy ] yz

_done : {A : Set} -> (x : A) -> x == x
_done _ = refl


open Cat2.COMMA {Cat2.SET} Cat2.ID=> Cat2.ID=>

toN : {n : Nat} -> Fin n -> Nat
toN zero = 0
toN (suc f) = 1 + toN f


infixr 3 _×_
infixr 3 _,_
record _×_ (A : Set) (B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

Nat2 : Set
Nat2 = Nat × Nat

Fin2 : Nat2 -> Set
Fin2 (m , n) = Fin m × Fin n

toN2 : {(m , n) : Nat2} -> Fin2 (m , n) -> Nat2
toN2 (fst , snd) = toN fst , toN snd

<+> : Nat2 -> Nat
<+> (x , y) = x + y

n+suc : (n m : Nat) -> n + suc m == suc (n + m)
n+suc zero m = refl
n+suc (suc n) m rewrite n+suc n m = refl

weaken : ∀ {m} {n} (y : Fin n) → Fin (m + n)
weaken {zero} y = y
weaken {suc m} zero = zero
weaken {suc m} {suc n} (suc y) rewrite n+suc m n = suc (weaken y)

infixl 5 _+F_
_+F_ : {m n : Nat} -> Fin (suc m) -> Fin n -> Fin (m + n)
_+F_ {m} zero y = weaken y
_+F_ {suc _} (suc x) y = suc (x +F y)

<+F> : {m n : Nat} -> Fin2 (suc m , n) -> Fin (m + n)
<+F> (x , y) = x +F y

postulate
  extensionality : {S : Set}{T : S -> Set}
                   {f g : (x : S) -> T x} ->
                   ((x : S) -> f x == g x) ->
                   f == g

infix 1 _=o=_
_=o=_ : {A B : Set} -> (A -> B) -> (A -> B) -> Set
_=o=_ {A} f g = (x : A) -> f x == g x

toN-weaken : {m n : Nat} ->  (y : Fin n) → toN (weaken {m} y) == toN y
toN-weaken {zero} y = refl
toN-weaken {suc m} zero = refl
toN-weaken {suc m} (suc y) = {!!}

toN-+F : ∀ {(m , n) : Nat2} -> toN {m + n} ∘ <+F> =o= <+> ∘ toN2 {suc m , n}
toN-+F {zero , n} (zero , y) = refl
toN-+F {suc m , n} (zero , y) rewrite toN-+F {m , n} (zero , y) | toN-weaken {suc m} y = refl
toN-+F {suc m , n} (suc x , y) rewrite toN-+F {m , n} (x , y) = refl


infix 0 _=>>_
_=>>_ : ∀ {σ1 τ1 : Set}
          {σ2 τ2 : Set}
    → (σ1  ->  σ2) → (τ1  ->  τ2) → Set
g =>> h = CommaArr (comma-obj g) (comma-obj h)

+=>> : {(m , n) : Nat × Nat} -> toN2 { suc m , n } =>> toN { m + n }
+=>> = comma-hom <+F> <+> $ extensionality toN-+F

transpose : {A B : CommaObj} ((comma-hom f g _) : CommaArr A B) -> f =>> g
transpose {comma-obj h} {comma-obj h'} (comma-hom f g p) = comma-hom h h' (sym p)


Nat3 : Set
Nat3 = Nat × Nat2

Fin3 : Nat3 -> Set
Fin3 (m , n) = Fin m × Fin2 n

toN3 : {(c , m , n) : Nat3} -> Fin3 (c , m , n) -> Nat3
toN3 (c , mn) = toN c , toN2 mn

addN : Nat3 -> Nat
addN (c , a , b) = c + a + b

addF : {(m , n) : Nat2} -> Fin3 (2 , m , n) -> Fin (m + n)
addF (c , a , b) = c +F a +F b

toN-addF : ∀ {mn@(m , n) : Nat2} →
     SET [ addF >> toN ] =o= SET [ toN3 >> addN ]
toN-addF {mn} (c , a , b) rewrite toN-+F {mn} (c +F a , b) | toN-+F (c , a) = refl

add=>>0 : {(m , n) : Nat2} -> toN3 {2 , m , n} =>> toN {m + n}
add=>>0 = comma-hom addF addN $ extensionality toN-addF

carryIn : Nat3 -> Nat2
carryIn (c , a , b) = c + a , b

addN=>> : carryIn =>> id {A = Nat}
addN=>> = comma-hom addN <+> refl

_×C_ : Cat2.Category.Obj Comma -> Cat2.Category.Obj Comma -> Cat2.Category.Obj Comma
_×C_ (comma-obj {A1} {B1} f) (comma-obj {A2} {B2} g) =
  comma-obj {A1 × A2} {B1 × B2} λ { (x , y) → (f x , g y) }

do-first : {A B X : Set} -> (A -> B) -> A × X -> B × X
do-first f = (λ { (a , x) → f a , x })

first :  {A B X : Cat2.Category.Obj Comma} -> Comma [ A , B ] -> Comma [ (A ×C X) , (B ×C X) ]
first {A} {B} {X = comma-obj xf} (comma-hom f g p) =
  comma-hom (do-first f) (do-first g) $ cong (\k (a , x) -> k a , xf x) p

reassoc : {A B C : Set} -> A × (B × C) -> (A × B) × C
reassoc = (λ { (a , b , c) → (a , b) , c })

assoc : {A B X : Cat2.Category.Obj Comma} -> Comma [ A ×C (B ×C X) , (A ×C B) ×C X ]
assoc = comma-hom reassoc reassoc {!!}

assoc=>> : {A B C : Set} -> id {A = A × B × C} =>> id {A = (A × B) × C}
assoc=>> = comma-hom reassoc reassoc refl

addF=>> : {(m , n) : Nat2} -> toN3 {2 , m , n} =>> toN {m + n}
addF=>> = Comma [ Comma [ assoc >> first +=>> ] >> +=>> ]


record Iso (A B : Set) : Set where
  constructor iso
  field
    forward : A -> B
    backward : B -> A
    forward-backward : backward ∘ forward == id
    backward-forward : forward ∘ backward == id

open Iso


iso-ext
    : {X Y : Set}
   -> {tau psi : Iso X Y}
   -> tau .forward == psi .forward
   -> tau .backward == psi .backward
   -> tau == psi
iso-ext {tau = iso f-> f<- fp-> fp<- } {iso g-> g<- gp-> gp<- } f-eq g-eq
  rewrite f-eq | g-eq | Cat2.uip fp-> gp-> | Cat2.uip fp<- gp<- = refl

open Cat2.Category hiding (id)

isoCat : Cat2.Category
Cat2.Category.Obj isoCat = Set
Cat2.Category._~>_ isoCat = Iso
Cat2.Category.id isoCat = iso id id refl refl
Cat2.Category._>>_ isoCat f g = iso (SET [ forward f >> forward g ]) (SET [ backward g >> backward f ]) {!!} {!!}
Cat2.Category.id-l isoCat f rewrite id-l SET (forward f) | id-l SET (backward f) = refl
Cat2.Category.id-r isoCat f rewrite id-r SET (forward f) | id-r SET (backward f) = refl
Cat2.Category.>>-assoc isoCat f g h rewrite >>-assoc SET (forward f) (forward g) (forward h) | >>-assoc SET (backward h) (backward g) (backward f) = refl


CarryIn : Nat -> Set
CarryIn m = Fin3 (2 , m , m)

CarryOut : Nat -> Set
CarryOut m = Fin2 (m , 2)

n+zero : (n : Nat) -> n + zero == n
n+zero zero = refl
n+zero (suc n) rewrite n+zero n = refl

2*m==m+m : (m : Nat) -> (2 * m) == m + m
2*m==m+m zero = refl
2*m==m+m (suc m) rewrite 2*m==m+m m | n+zero m | n+suc m m = refl

cast : {m n : Nat} -> (m == n) -> Fin m -> Fin n
cast p rewrite p = id

-- cast : {m : Nat} -> Fin (m + m) -> Fin (2 * m)
-- cast {m} rewrite sym (2*m==m+m m) = id

puzzle1 : {m : Nat}
      -> Comma [ comma-obj {CarryIn m}   {CarryIn m}   id
               , comma-obj {Fin (2 * m)} {Fin (m + m)} (cast $ 2*m==m+m m)
               ]
puzzle1 {m} =
  comma-hom
    (SET [ addF >> cast $ sym $ 2*m==m+m m ])
    addF
    {!!}

comb : {m n : Nat} -> Fin2 (m , n) -> Fin (n * m)
comb (f1 , f2) = combine f2 f1

remQuot : {n : Nat} -> (k : Nat) -> Fin (n * k) -> Fin k × Fin n
remQuot {n} k f with Data.Fin.remQuot {n} k f
... | (Data.Product._,_ a b) = b , a

addCarry : {m : Nat} -> SET [ CarryIn m , CarryOut m ]
addCarry {m} = SET [ SET [ addF >> cast (sym (2*m==m+m m)) ] >> remQuot {2} m ]

puzzle2 : {m : Nat}
      -> Comma [ comma-obj {CarryIn m}  {CarryIn m}   id
               , comma-obj {CarryOut m} {Fin (2 * m)} comb
               ]
puzzle2 {m} =
  comma-hom
    addCarry
    (SET [ addF >> cast (sym (2*m==m+m m)) ])
    {!!}

puzzle : {m : Nat} -> id =>> (cast (2*m==m+m m) ∘ comb {m} {2})
puzzle = transpose $ Comma [ transpose puzzle2 >> transpose puzzle1 ]

data Bool : Set where
  true : Bool
  false : Bool

bval : Bool -> Fin 2
bval true = suc zero
bval false = zero

DIn : Set -> Set
DIn t = Bool × t × t

DOut : Set -> Set
DOut t = t × Bool

bimap : {A A' B B' : Set} -> (A -> A') -> (B -> B') -> (A × B -> A' × B')
bimap f g (a , b) = f a , g b

record Adder {t : Set} {m : Nat} (μ : t -> Fin m) : Set where
  constructor _-|_
  field
    addD : DIn t -> DOut t
    is-adder : SET [ addD >> bimap μ bval ]
            == SET [ bimap bval (bimap μ μ) >> addCarry ]

Adder=>> : {t : Set} {m : Nat} {μ : t -> Fin m}
        -> Adder μ
        -> bimap bval (bimap μ μ) =>> bimap μ bval
Adder=>> (addD -| proof) = comma-hom addD addCarry proof


and : Bool -> Bool -> Bool
and true b = b
and false b = false

or : Bool -> Bool -> Bool
or true b = true
or false b = b

xor : Bool -> Bool -> Bool
xor true true = false
xor true false = true
xor false true = true
xor false false = false

full-add : DIn Bool -> DOut Bool
full-add (cin , a , b) =
  let o = xor a b
   in xor o cin , or (and a b) (and o cin)

BitAdder : Adder bval
BitAdder = full-add -| extensionality
  \ { (false , false , false) -> refl
    ; (false , false , true) -> refl
    ; (false , true , false) -> refl
    ; (false , true , true) -> refl
    ; (true , false , false) -> refl
    ; (true , false , true) -> refl
    ; (true , true , false) -> refl
    ; (true , true , true) -> refl
    }

tensorμ
    : {tm tn : Set}
   -> {m n : Nat}
   -> (tm -> Fin m)
   -> (tn -> Fin n)
   -> (tm × tn -> Fin (n * m))
tensorμ μm μn (tm , tn) = comb $ μm tm , μn tn

tensorAdd : {m n : Set} -> (DIn m -> DOut m) -> (DIn n -> DOut n) -> (DIn (m × n) -> DOut (m × n))
tensorAdd addm addn (cin , (ma , na) , (mb , nb)) =
  let (m , cin') = addm $ cin  , ma , mb
      (n , cout) = addn $ cin' , na , nb
   in (m , n) , cout

adder22 : Adder (tensorμ bval bval)
adder22 = tensorAdd full-add full-add -| extensionality
  \ { (false , (false , false) , (false , false)) → refl
    ; (false , (false , false) , (false , true)) → refl
    ; (false , (false , false) , (true , false)) → refl
    ; (false , (false , false) , (true , true)) → refl
    ; (false , (false , true) , (false , false)) → refl
    ; (false , (false , true) , (false , true)) → refl
    ; (false , (false , true) , (true , false)) → refl
    ; (false , (false , true) , (true , true)) → refl
    ; (false , (true , false) , (false , false)) → refl
    ; (false , (true , false) , (false , true)) → refl
    ; (false , (true , false) , (true , false)) → refl
    ; (false , (true , false) , (true , true)) → refl
    ; (false , (true , true) , (false , false)) → refl
    ; (false , (true , true) , (false , true)) → refl
    ; (false , (true , true) , (true , false)) → refl
    ; (false , (true , true) , (true , true)) → refl
    ; (true , (false , false) , (false , false)) → refl
    ; (true , (false , false) , (false , true)) → refl
    ; (true , (false , false) , (true , false)) → refl
    ; (true , (false , false) , (true , true)) → refl
    ; (true , (false , true) , (false , false)) → refl
    ; (true , (false , true) , (false , true)) → refl
    ; (true , (false , true) , (true , false)) → refl
    ; (true , (false , true) , (true , true)) → refl
    ; (true , (true , false) , (false , false)) → refl
    ; (true , (true , false) , (false , true)) → refl
    ; (true , (true , false) , (true , false)) → refl
    ; (true , (true , false) , (true , true)) → refl
    ; (true , (true , true) , (false , false)) → refl
    ; (true , (true , true) , (false , true)) → refl
    ; (true , (true , true) , (true , false)) → refl
    ; (true , (true , true) , (true , true)) → refl
    }

data One : Set where
  one : One

oneval : One -> Fin 1
oneval one = zero

trivial-add : DIn One -> DOut One
trivial-add (b , _ , _) = one , b

adder12 : Adder (tensorμ oneval bval)
adder12 = tensorAdd trivial-add full-add -| extensionality
  \ {
      (c , (m1 , n1) , (m2 , n2)) -> ?
    }


μOf : {A : Set} {m : Nat} {μ : A -> Fin m} -> Adder μ -> A -> Fin m
μOf {μ = μ} _ = μ

Adder=>>N : Cat2.CommaArr.f
              (Comma [
               Comma [ Comma [ transpose (Adder=>> adder22) >> transpose puzzle ]
               >> transpose addF=>> ]
               >> transpose addN=>> ]) =>> Cat2.CommaArr.g
                       (Comma [
                        Comma [ Comma [ transpose (Adder=>> adder22) >> transpose puzzle ]
                        >> transpose addF=>> ]
                        >> transpose addN=>> ])
Adder=>>N = transpose $
  Comma
    [ Comma
    [ Comma
    [ transpose (Adder=>> adder22)
   >> transpose puzzle ]
   >> transpose addF=>> ]
   >> transpose addN=>> ]


arrowOf : {A B : CommaObj} -> CommaArr A B -> CommaObj × CommaObj
arrowOf {A} {B} _ = A , B

debug : {A B C D : Set} -> {f : A -> B} -> {g : C -> D} -> f =>> g -> A -> D
debug arr x =
  let (_ , comma-obj y) = arrowOf arr
      (comma-hom f _ _) = arr
  in y (f x)

debug' : Nat
debug' = debug Adder=>>N (false , (true , false) , (true , false))

tensorAdder
    : {tm tn : Set} {m n : Nat} {μm : tm -> Fin m} {μn : tn -> Fin n}
   -> Adder μm
   -> Adder μn
   -> Adder (tensorμ μm μn)
tensorAdder (addm -| pm) (addn -| pn) =
  tensorAdd addm addn -| {!!}

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if_then_else_ true a _ = a
if_then_else_ false _ a = a

speculate : {A C : Set} -> (Bool × A -> C) -> (Bool × A -> C)
speculate f (b , a) = if b then f (true , a) else f (false , a)

spec
    : {t : Set} {m : Nat} {μ : t -> Fin m}
   -> Adder μ
   -> Adder μ
spec (adder -| proof) = speculate adder -| ?

data Vec : Set -> Nat -> Set where
  nil : {A : Set} -> Vec A zero
  cons : {A : Set} {n : Nat} -> A -> Vec A n -> Vec A (suc n)

loop : {A B S : Set} -> {n : Nat} -> (S × A -> B × S) -> S × Vec A n -> Vec B n × S
loop {n = zero} f (s , nil) = nil , s
loop {n = suc n} f (s , cons a v) = let b , s' = f (s , a) in bimap (cons b) id (loop f (s' , v))


