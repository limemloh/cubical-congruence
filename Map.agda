{-# OPTIONS --cubical --safe #-}

open import Cubical.Data.Bool

module Map {K : Set} (_==_ : K → K → Bool) where
  open import List
  open import Cubical.Data.Maybe
  open import Cubical.Data.Prod

  Map : ∀ {ℓ} → Set ℓ → Set ℓ
  Map A = List (K × A)

  module _ {ℓ} {A : Set ℓ} where

    empty : Map A
    empty = []

    lookup : K → Map A → Maybe A
    lookup k [] = nothing
    lookup k ((i , x) ∷ m) with i == k
    lookup k ((i , x) ∷ m) | false = lookup k m
    lookup k ((i , x) ∷ m) | true = just x

    safeLookup : K → Map A → A → A
    safeLookup k m a with lookup k m
    safeLookup k m a | nothing = a
    safeLookup k m a | just x = x

    delete : K → Map A → Map A
    delete k [] = []
    delete k ((i , n) ∷ m) with i == k
    delete k (x ∷ m) | false = x ∷ delete k m
    delete k (x ∷ m) | true = m

    insert : K → A → Map A → Map A
    insert k a m = (k , a) ∷ delete k m

    update : K → (A → A) → Map A → Map A
    update k f m with lookup k m
    update k f m | nothing = m
    update k f m | just x = insert k (f x) m

    updater : K → (Maybe A → Maybe A) → Map A → Map A
    updater k f m with f (lookup k m)
    updater k f m | nothing = m
    updater k f m | just x = insert k x m

    union : Map A → Map A → Map A
    union [] n = n
    union ((k , a) ∷ m) n = insert k a (union m n)

    mapValues : {B : Set} → (A → B) → Map A → Map B
    mapValues f [] = []
    mapValues f ((k , x) ∷ m) = (k , f x) ∷ mapValues f m

    toList : Map A → List (K × A)
    toList x = x

    values : Map A → List A
    values m = mapList proj₂ m
