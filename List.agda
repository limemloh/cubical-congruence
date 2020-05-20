{-# OPTIONS --cubical --safe #-}

module List where
  open import Cubical.Foundations.Everything hiding (empty)
  open import Cubical.Data.List public
  open import Cubical.Data.Nat
  open import Cubical.Data.Bool

  private
    variable
      ℓ ℓ' : Level
      A : Set ℓ
      B : Set ℓ'

  if_then_else_ : Bool → A → A → A
  if true then x else y = x
  if false then x else y = y

  mapList : (f : A → B) → List A → List B
  mapList f [] = []
  mapList f (x ∷ xs) = f x ∷ mapList f xs

  repeat : ℕ → A → List A
  repeat zero a = []
  repeat (suc n) a = a ∷ repeat n a

  foldl : (B → A → B) → B → List A → B
  foldl f b [] = b
  foldl f b (x ∷ xs) = foldl f (f b x) xs

  flat : List (List A) → List A
  flat l = foldl _++_ [] l

  flatmap : (A → List B) → List A → List B
  flatmap f l = flat (mapList f l)

  any : (A → Bool) → List A → Bool
  any f [] = false
  any f (x ∷ xs) = if f x then true else any f xs

  takeWhile : (A → Bool) → List A → List A
  takeWhile f [] = []
  takeWhile f (x ∷ xs) with f x
  takeWhile f (x ∷ xs) | false = []
  takeWhile f (x ∷ xs) | true = x ∷ takeWhile f xs
