{-# OPTIONS --type-in-type #-}

module Cat2 where

open import Relation.Binary.PropositionalEquality renaming (_≡_ to _==_; [_] to [[_]])
open import Tactic.Rewrite using (cong!)

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




postulate
  extensionality : {S : Set}{T : S -> Set}
                   {f g : (x : S) -> T x} ->
                   ((x : S) -> f x == g x) ->
                   f == g



record Category : Set where
  infix 6 _~>_
  field
    Obj : Set
    _~>_ : (A B : Obj) → Set

    id : {A : Obj} → A ~> A
    _>>_ : {A B C : Obj} → A ~> B → B ~> C → A ~> C

    id-l : {A B : Obj} (f : A ~> B) → id >> f == f
    id-r : {A B : Obj} (f : A ~> B) → f >> id == f
    >>-assoc : {A B C D : Obj} (f : A ~> B) → (g : B ~> C) → (h : C ~> D) → f >> (g >> h) == (f >> g) >> h


infix 5 _[_,_]
_[_,_] : (C : Category) -> Category.Obj C -> Category.Obj C -> Set
C [ X , Y ] = Category._~>_ C X Y

infix 5 _[_>>_]
_[_>>_] : (C : Category) -> {X Y Z : Category.Obj C} -> C [ X , Y ] -> C [ Y , Z ] -> C [ X , Z ]
C [ f >> g ] = Category._>>_ C f g


SET : Category
SET = record
        { Obj = Set
        ; _~>_ = \ S T → S → T
        ; id = \ x → x
        ; _>>_ = λ f g x →  g (f x)
        ; id-l = \f -> refl
        ; id-r = \f -> refl
        ; >>-assoc = \f g h -> refl
        }


module FUNCTOR where
    open Category

    infix 6 _=>_
    record _=>_ (C : Category) (D : Category) : Set where
      field
        F-Obj : Obj C → Obj D
        F-map : {A B : Obj C} → C [ A , B ] → D [ F-Obj A , F-Obj B ]

        F-map-id : (A : Obj C) → F-map (id C {A}) == id D {F-Obj A}
        F-map->> : {X Y Z : Obj C} (f : C [ X ,  Y ]) → (g : C [ Y ,  Z ]) → (F-map ( C [ f >> g ])) == (D [ F-map f >> F-map g ])



open FUNCTOR

ID=> : {C : Category} → C => C
ID=> = record
     { F-Obj = λ x → x
     ; F-map = λ x → x
     ; F-map-id = \a → refl
     ; F-map->> = \f g -> refl
     }

data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

MAYBE : SET => SET
MAYBE = record
  { F-Obj = Maybe
  ; F-map = λ { f (just x) → just (f x) ; f nothing → nothing }
  ; F-map-id = \a -> extensionality λ { (just x) → refl ; nothing → refl }
  ; F-map->> = \f g -> extensionality λ { (just x) → refl ; nothing → refl }
  }

infixr 10 _,-_
data List (A : Set) : Set where
  [] : List A
  _,-_ : A → List A → List A

list : {A B : Set} → (A → B) → List A → List B
list f [] = []
list f (x ,- xs) = f x ,- list f xs

LIST : SET => SET
LIST = record
  { F-Obj = List
  ; F-map =  list
  ; F-map-id = \a -> extensionality help
  ; F-map->> = \f g -> extensionality λ { x → yelp f g x }
  }
  where
    help : {A : Set} (x : List A) → list (λ x → x) x == x
    help [] = refl
    help (x ,- xs) rewrite help xs = refl

    yelp : ∀ {X} {Y} {Z} (f : SET [ X , Y ]) (g : SET [ Y , Z ])
         (x : List X) → list (SET [ f >> g ]) x == (SET [ list f >> list g ]) x
    yelp f g [] = refl
    yelp f g (x ,- xs) rewrite yelp f g xs = refl



module NAT-TRANS where
  open Category
  open _=>_
  record _~~>_ {C D : Category} (F G : C => D) : Set where
    field
        hoist : (X : Obj C) →  D [ F-Obj F X , F-Obj G X ]
        nat : {X Y : Obj C} {f : C [ X , Y ]} →  D [ hoist X >> F-map G f ] == D [ F-map F f >> hoist Y ]

open NAT-TRANS

LIST-TO-MAYBE : LIST ~~> MAYBE
LIST-TO-MAYBE = record
  { hoist = λ { X [] → nothing ; X (x ,- _) → just x }
  ; nat = extensionality λ { [] → refl ; (x ,- x₁) → refl }
  }

infix 4 _,_,_
record Sg2 (A B : Set) (C : A -> B -> Set) : Set where
  constructor _,_,_
  field
    fst : A
    snd : B
    sg2 : C fst snd

module COMMA where
  open Category
  open _=>_

  {-# TERMINATING #-}
  Comma : {A B C : Category} -> (A => C) -> (B => C) -> Category
  Category.Obj (Comma {A} {B} {C} S T)
    = Sg2 (Obj A) (Obj B) (\a b -> C [ F-Obj S a , F-Obj T b ])
  Category._~>_ (Comma {A} {B} {C} S T) (a , b , h) (a' , b' , h')
    = Sg2 (A [ a , a' ]) (B [ b , b' ]) \ f g -> C [ F-map S f >> h' ]
                                              == C [ h >> F-map T g ]
  Category.id (Comma {A} {B} {C} S T) {A = ( a , b , h )}
    = id A {a}
    , id B {b}
    , ( begin
          C [ F-map S (id A {a}) >> h ]  =[ cong! (F-map-id S a) ]
          C [ id C {F-Obj S a} >> h ]    =[ cong! (id-l C h) ]
          h                              =[ cong! (sym (id-r C h)) ]
          C [ h >> id C {F-Obj T b} ]    =[ cong! (sym (F-map-id T b)) ]
          C [ h >> F-map T (id B {b}) ]
        done
      )
  Category._>>_ (Comma {A} {B} {C} S T) {A = (a1 , b1 , f)}
                                        {B = (a2 , b2 , g)}
                                        {C = (a3 , b3 , h)}
                                        (a , b , p)
                                        (a' , b' , p')
    = A [ a >> a' ]
    , B [ b >> b' ]
    , ( begin
          C [ F-map S (A [ a >> a' ]) >> h ]        =[ cong! (F-map->> S a a') ]
          C [ C [ F-map S a >> F-map S a' ] >> h ]  =[ sym (>>-assoc C (F-map S a) (F-map S a') h) ]
          C [ F-map S a >> C [ F-map S a' >> h ] ]  =[ cong (\x -> C [ F-map S a >> x ] ) p' ]
          C [ F-map S a >> C [ g >> F-map T b' ] ]  =[ >>-assoc C (F-map S a) g (F-map T b') ]
          C [ C [ F-map S a >> g ] >> F-map T b' ]  =[ cong (\x -> C [ x >> F-map T b' ] ) p ]
          C [ C [ f >> F-map T b ] >> F-map T b' ]  =[ sym (>>-assoc C f (F-map T b) (F-map T b')) ]
          C [ f >> C [ F-map T b >> F-map T b' ] ]  =[ cong! (sym (F-map->> T b b')) ]
          C [ f >> F-map T (B [ b >> b' ]) ]
        done
      )
  Category.id-l (Comma {A} {B} {C} S T) {A = a1 , b1 , sa->tb1} {B = a2 , b2 , sa->tb2} (f , g , proof) =
    begin
      Comma S T [ (id (Comma S T)) >> (f , g , proof) ]
    =[]
      Comma S T [ (id A , id B , ?) >> (f , g , proof) ]
    =[ ? ]
      ?
    --   Comma S T [ (id A , id B , sg2 ?) >> (f , g , proof) ]
    -- =[]
    --   (A [ id A >> f ] , B [ id B >> g ] , _)
    -- =[ cong (\x -> x , B [ id B >> g ] , _) (id-l A f) ]
    --   (f , B [ id B >> g ] , ?)
    -- =[ cong (\x -> f , x , _) (id-l B g) ]
    --   f , g , proof
    -- done
  Category.id-r (Comma {A} {B} {C} S T) = {!!}
  Category.>>-assoc (Comma {A} {B} {C} S T) = {!!}


