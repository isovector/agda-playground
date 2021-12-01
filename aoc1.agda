{-# OPTIONS --guardedness #-}

import Data.Nat
import Data.Maybe
import Data.List
import Data.Product 
import Data.Bool
import Relation.Nullary
import Data.Nat.Show 
import Data.String 
import Function
import IO
open Function
open Data.Nat
open Data.Maybe using (fromMaybe)
open Data.List hiding (fromMaybe)
open Data.Bool using (Bool)
open Data.Product using (_×_; _,_; uncurry)
open Relation.Nullary using (_because_; ofʸ; yes)
open Data.String using (String)
open Data.Nat.Show using (readMaybe; show)
open IO 


variable
  A B : Set

parse : String → List ℕ
parse = mapMaybe (readMaybe 10) ∘ Data.String.lines

filter' : (A → Bool) → List A → List A
filter' p []               = []
filter' p (x ∷ xs) with (p x)
...                | Bool.true  = x ∷ filter' p xs
...                | Bool.false = filter' p xs

solve : List ℕ → ℕ
solve l = length $ filter' (uncurry _≤ᵇ_) $ zip l $ drop 1 l

main : Main
main = run $ do
  x ← readFiniteFile "/home/sandy/aoc1.txt"
  putStrLn $ show $ solve $ parse x

