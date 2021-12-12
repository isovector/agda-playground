{-# OPTIONS --type-in-type #-}

module Cat2 where


infix 1 _==_
data _==_ {A : Set} : A → A → Set where
  refl : (a : A) → a == a
{-# BUILTIN EQUALITY _==_ #-}


cong : forall {f g a b} -> f == g -> a == b -> a f == g b
cong fg ab rewrite fg | ab = refl _


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

    id-l : {A B : Obj} {f : A ~> B} → id >> f == f
    id-r : {A B : Obj} {f : A ~> B} → f >> id == f
    >>-assoc : {A B C D : Obj} {f : A ~> B}{g : B ~> C}{h : C ~> D} → f >> (g >> h) == (f >> g) >> h


_[_,_] : (C : Category) -> Category.Obj C -> Category.Obj C -> Set
C [ X , Y ] = Category._~>_ C X Y

_[_>>_] : (C : Category) -> {X Y Z : Category.Obj C} -> C [ X , Y ] -> C [ Y , Z ] -> C [ X , Z ]
C [ f >> g ] = Category._>>_ C f g


SET : Category
SET = record
        { Obj = Set
        ; _~>_ = \ S T → S → T
        ; id = \ x → x
        ; _>>_ = λ f g x →  g (f x)
        ; id-l = refl _
        ; id-r = refl _
        ; >>-assoc = refl _
        }


module FUNCTOR where
    open Category

    infix 6 _=>_
    record _=>_ (C : Category) (D : Category) : Set where
      field
        F-Obj : Obj C → Obj D
        F-map : {A B : Obj C} → C [ A , B ] → D [ F-Obj A , F-Obj B ]

        F-map-id : {A : Obj C} → F-map (id C {A}) == id D
        F-map->> : {X Y Z : Obj C} {f : C [ X ,  Y ]} {g : C [ Y ,  Z ]} → F-map ( C [ f >> g ]) == D [ F-map f >> F-map g ]


open FUNCTOR

ID=> : {C : Category} → C => C
ID=> = record
     { F-Obj = λ x → x
     ; F-map = λ x → x
     ; F-map-id = refl (Category.id _)
     ; F-map->> = refl _
     }

data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

MAYBE : SET => SET
MAYBE = record
  { F-Obj = Maybe
  ; F-map = λ { f (just x) → just (f x) ; f nothing → nothing }
  ; F-map-id = extensionality λ { (just x) → refl _ ; nothing → refl _ }
  ; F-map->> = extensionality λ { (just x) → refl _ ; nothing → refl _ }
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
  ; F-map-id = extensionality help
  ; F-map->> = extensionality λ { x → yelp x }
  }
  where
    help : {A : Set} (x : List A) → list (λ x → x) x == x
    help [] = refl _
    help (x ,- xs) rewrite help xs = refl (x ,- xs)

    yelp : ∀ {X} {Y} {Z} {f : SET [ X , Y ]} {g : SET [ Y , Z ]}
         (x : List X) → list (SET [ f >> g ]) x == (SET [ list f >> list g ]) x
    yelp [] = refl []
    yelp {f = f} {g = g} (x ,- xs) rewrite yelp xs = ?



module NAT-TRANS where
  open Category
  open _=>_
  record _~~>_ {C D : Category} (F G : C => D) : Set where
    field
        hoist : (X : Obj C) →  D [ F-Obj F X , F-Obj G X ]
        nat : {X Y : Obj C} {f : C [ X , Y ]} →  D [ hoist X >> F-map G f ] == D [ F-map F f >> hoist Y ]

open NAT-TRANS

LIST_TO_MAYBE : LIST ~~> MAYBE
LIST_TO_MAYBE = record
  { hoist = λ { X [] → nothing ; X (x ,- _) → just x }
  ; nat = extensionality λ { [] → refl _ ; (x ,- x₁) → refl _ }
  }




