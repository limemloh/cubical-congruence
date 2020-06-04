{-# OPTIONS --cubical --safe #-}

module ReflectionUtils where
  open import Cubical.Foundations.Everything hiding (empty)
  open import Cubical.Data.Bool hiding (_≟_)
  open import Cubical.Data.Prod
  open import Cubical.Data.Maybe
  open import Cubical.Data.Nat
  open import Cubical.Data.Unit
  open import Reflection hiding (Type; name; _≟_)
  open import Reflection.Term using (_≟_)
  import Agda.Builtin.Nat as Nat

  open import List

  -- Macroes for debugging
  macro
    runTC : ∀ {A : Set} → TC A → Term → TC Unit
    runTC tc goal = do a ← tc
                       q ← quoteTC a
                       unify goal q
    runTCTerm : TC Term → Term → TC Unit
    runTCTerm tc goal =
      do a ← tc
         unify goal a

  mapTC : {A B : Set} → (f : A → B) → TC A →  TC B
  mapTC f tc = do x ← tc
                  return (f x)

  sequenceTC : {A : Set} → List (TC A) → TC (List A)
  sequenceTC [] = return []
  sequenceTC (tc ∷ tcs) =
    do x ← tc
       xs ← sequenceTC tcs
       return (x ∷ xs)

  unwrapArg : Arg Term → Term
  unwrapArg (arg _ x) = x

  mapArg : (Term → Term) → Arg Term → Arg Term
  mapArg f (arg i a) = arg i (f a)

  isVarN : Nat.Nat → Term → Bool
  isVarN n (var x _) = n Nat.== x
  isVarN n _ = false

  mapIndex : ℕ → (ℕ → ℕ) → Term → Term
  mapIndex zero _ t = t
  mapIndex (suc n) f (var x args) = var (f x) (mapList (mapArg (mapIndex n f)) args)
  mapIndex (suc n) f (con c args) = con c (mapList (mapArg (mapIndex n f)) args)
  mapIndex (suc n) f (def f₁ args) = def f₁ (mapList (mapArg (mapIndex n f)) args)
  mapIndex (suc n) f (lam v (abs s x)) = lam v (abs s (mapIndex n f x))
  mapIndex (suc n) f (pat-lam cs args) = pat-lam cs (mapList (mapArg (mapIndex n f)) args)
  mapIndex (suc n) f (pi a (abs s x)) = pi (mapArg (mapIndex n f) a) (abs s (mapIndex n f x))
  mapIndex (suc n) f (agda-sort (Sort.set t)) = agda-sort (Sort.set (mapIndex n f t))
  mapIndex (suc n) f t = t

  reflTerm : Term → Term
  reflTerm t = (def (quote refl) (hArg unknown ∷ hArg unknown ∷ hArg t ∷ []))

  isIntervalFn : Term → TC Bool
  isIntervalFn t =
    catchTC (do (checkType t (pi (vArg (def (quote I) [])) (abs "_" unknown)))
                return true)
            (return false)

  isHomogeneous : Term → TC Bool
  isHomogeneous t = withNormalisation true
    (catchTC (do checkType t (def (quote _≡_) (repeat 2 (hArg unknown) ++ repeat 2 (vArg unknown)))
                 return true)
             (return false))

  record PathInfo : Set where
    constructor PInfo
    field
      left : Term
      right : Term
      pathover : Maybe Term
  open PathInfo

  getPathTypeInfo : Term → TC PathInfo
  getPathTypeInfo ty = catchTC (helper ty)
                              (do n ← reduce ty
                                  helper n)
    where
      helper : Term → TC PathInfo
      helper (def (quote _≡_) (_ ∷ arg _ P ∷ arg _ l ∷ arg _ r ∷ [])) = return (PInfo l r (just (reflTerm P)))
      helper (def (quote PathP) (_ ∷ arg _ P ∷ arg _ l ∷ arg _ r ∷ [])) = return (PInfo l r (just P))
      helper t = typeError (strErr "Term" ∷ termErr t ∷ strErr "is not a path." ∷ [])

  endpoint0 : ∀ {ℓ} {A : I → Type ℓ} (P : (i : I) → A i) → A i0
  endpoint0 P = P i0

  endpoint1 : ∀ {ℓ} {A : I → Type ℓ} (P : (i : I) → A i) → A i1
  endpoint1 P = P i1

  endpoint0Term : Term → TC Term
  endpoint0Term P = normalise (def (quote endpoint0) (hArg unknown ∷ hArg unknown ∷ vArg P ∷ []))

  endpoint1Term : Term → TC Term
  endpoint1Term P = normalise (def (quote endpoint1) (hArg unknown ∷ hArg unknown ∷ vArg P ∷ []))

  getPathInfo : Term → TC PathInfo
  getPathInfo t =
    do isInter ← isIntervalFn t
       if isInter then
         (do l ← endpoint0Term t
             r ← endpoint1Term t
             return (PInfo l r nothing))
         else do ty ← inferType t
                 getPathTypeInfo ty

-- * Building Terms

  pattern SymPTerm p = (def (quote symP) (_ ∷ _ ∷ _ ∷ _ ∷ arg _ p ∷ []))
  pattern ReflTerm n = (def (quote refl)) (_ ∷ _ ∷ arg _ n ∷ [])

  symTerm : Term → Term
  symTerm (def (quote sym) (_ ∷ _ ∷ _ ∷ _ ∷ arg _ p ∷ [])) = p
  symTerm (SymPTerm p) = p
  -- symTerm t@(ReflTerm _) = t
  symTerm p = (def (quote symP) (repeat 4 (hArg unknown) ++ vArg p ∷ []))

  symTerms : List Term → List Term
  symTerms l = mapList symTerm l

  symTermsTC : List (TC Term) → List (TC Term)
  symTermsTC l = mapList (mapTC symTerm) l

  rUnitPathover : ∀ {ℓ} {A B : Type ℓ} → (AB : A ≡ B) → (a : A) → (b : B) → PathP (λ i → (AB ∙ refl) i) a b ≡ PathP (λ i → AB i) a b
  rUnitPathover AB a b = λ i → PathP (λ j → rUnit AB (~ i) j) a b

  lUnitPathover : ∀ {ℓ} {A B : Type ℓ} → (AB : A ≡ B) → (a : A) → (b : B) → PathP (λ i → (refl ∙ AB) i) a b ≡ PathP (λ i → AB i) a b
  lUnitPathover AB a b = λ i → PathP (λ j → lUnit AB (~ i) j) a b

  comp-PathP-Path : ∀ {ℓ} {A B : Type ℓ} {AB : A ≡ B} {a : A} {b b' : B} → PathP (λ i → AB i) a b → b ≡ b' → PathP (λ i → AB i) a b'
  comp-PathP-Path {AB = AB} {a = a} {b' = b'} p q = transport (rUnitPathover AB a b') (compPathP p q)

  comp-Path-PathP : ∀ {ℓ} {A B : Type ℓ} {AB : A ≡ B} {a a' : A} {b : B} → a ≡ a' → PathP (λ i → AB i) a' b → PathP (λ i → AB i) a b
  comp-Path-PathP {AB = AB} {a = a} {b = b} p q = transport (lUnitPathover AB a b) (compPathP p q)

  composeTerm : TC Term → TC Term → TC Term
  composeTerm tc-p tc-q =
    do p ← tc-p
       q ← tc-q
       hp ← isHomogeneous p
       hq ← isHomogeneous q
       helper hp hq p q
    where
      compose : Bool → Bool → Term → Term → Term
      compose true true p q = def (quote _∙_) (repeat 5 (hArg unknown) ++ vArg p ∷ vArg q ∷ [])
      compose true false p q = def (quote comp-Path-PathP) (repeat 7 (hArg unknown) ++ vArg p ∷ vArg q ∷ [])
      compose false true p q = def (quote comp-PathP-Path) (repeat 7 (hArg unknown) ++ vArg p ∷ vArg q ∷ [])
      compose false false (SymPTerm p) (SymPTerm q) =
        symTerm (def (quote compPathP) (repeat 6 (hArg unknown) ++ vArg p ∷ vArg q ∷ []))
      compose false false p q = def (quote compPathP) (repeat 6 (hArg unknown) ++ vArg p ∷ vArg q ∷ [])
      helper : Bool → Bool → Term → Term → TC Term
      helper hp hq (SymPTerm p) (SymPTerm q) = mapTC symTerm (helper hq hp q p)
      helper hp hq (ReflTerm _) q = return q
      helper hp hq p (ReflTerm _) = return p
      helper hp hq p q = return (compose hp hq p q)

  composeTerms : List (TC Term) → List (TC Term) → List (TC Term)
  composeTerms l r = flatmap (λ x → mapList (composeTerm x) r) l

  hcongr-ideal : ∀ {ℓ} {A : I → Type ℓ}
                   {C : (i : I) → A i → Type ℓ}
                   {f : (a : A i0) → C i0 a} {g : (b : A i1) → C i1 b}
                   {a : A i0} {b : A i1} →
                   (fg : PathP (λ i → (a : A i) → C i a) f g) →
                   (ab : PathP A a b) →
                   PathP (λ i → C i (ab i)) (f a) (g b)
  hcongr-ideal fg ab = λ i → fg i (ab i)

  hcongrTerm : Term → Term → Term
  hcongrTerm fg ab = (def (quote hcongr-ideal) (repeat 7 (hArg unknown) ++ vArg fg ∷ vArg ab ∷ []))

  hcongrTerms : List Term → List Term → List Term
  hcongrTerms fs as = flatmap (λ f → mapList (hcongrTerm f) as) fs

  hcongrTermTC : TC Term → TC Term → TC Term
  hcongrTermTC tc-fg tc-ab =
    do fg ← tc-fg
       ab ← tc-ab
       return (hcongrTerm fg ab)

  hcongrTermsTC : List (TC Term) → List (TC Term) → List (TC Term)
  hcongrTermsTC fs as = flatmap (λ f → mapList (hcongrTermTC f) as) fs

  module Examples where
    -- * Examples
    getPathInfoExamplePath : ∀ {ℓ} {A : Type ℓ} {a b : A} → (p : a ≡ b) →
      runTC (getPathInfo (quoteTerm p)) ≡ PInfo (quoteTerm a) (quoteTerm b) (just (reflTerm (quoteTerm A)))
    getPathInfoExamplePath p = refl

    getPathInfoExamplePathP : ∀ {ℓ} {A : I → Type ℓ} {a : A i0} {b : A i1} → (p : PathP A a b) →
      runTC (getPathInfo (quoteTerm p)) ≡ PInfo (quoteTerm a) (quoteTerm b) (just (quoteTerm A))
    getPathInfoExamplePathP p = refl

    getPathInfoExampleInterval : ∀ {ℓ} {A : Type ℓ} → (p : I → A) →
      runTC (getPathInfo (quoteTerm p)) ≡ PInfo (quoteTerm (p i0)) (quoteTerm (p i1)) nothing
    getPathInfoExampleInterval p = refl

    getPathInfoExampleDepInterval : ∀ {ℓ} {A : I → Type ℓ} → (p : (i : I) → A i) →
      runTC (getPathInfo (quoteTerm p)) ≡ PInfo (quoteTerm (p i0)) (quoteTerm (p i1)) nothing
    getPathInfoExampleDepInterval p = refl

    isIntervalFnExampleInterval : ∀ {ℓ} {A : Type ℓ} → (p : I → A) →
      runTC (isIntervalFn (quoteTerm p)) ≡ true
    isIntervalFnExampleInterval p = refl

    isIntervalFnExampleDepInterval : ∀ {ℓ} {A : I → Type ℓ} → (p : (i : I) → A i) →
      runTC (isIntervalFn (quoteTerm p)) ≡ true
    isIntervalFnExampleDepInterval p = refl

    isIntervalFnExamplePath : ∀ {ℓ} {A : Type ℓ} {a b : A} → (p : a ≡ b) →
      runTC (isIntervalFn (quoteTerm p)) ≡ false
    isIntervalFnExamplePath p = refl

    isIntervalFnExamplePathP : ∀ {ℓ} {A : I → Type ℓ} {a : A i0} {b : A i1} → (p : PathP A a b) →
      runTC (isIntervalFn (quoteTerm p)) ≡ false
    isIntervalFnExamplePathP p = refl

    endpoint0TermExampleInterval : ∀ {ℓ} {A : Type ℓ} → (p : I → A) →
      runTCTerm (endpoint0Term (quoteTerm p)) ≡ p i0
    endpoint0TermExampleInterval p = refl

    endpoint0TermExampleDepInterval : ∀ {ℓ} {A : I → Type ℓ} → (p : (i : I) → A i) →
      runTCTerm (endpoint0Term (quoteTerm p)) ≡ p i0
    endpoint0TermExampleDepInterval p = refl

    endpoint1TermExampleInterval : ∀ {ℓ} {A : Type ℓ} → (p : I → A) →
      runTCTerm (endpoint1Term (quoteTerm p)) ≡ p i1
    endpoint1TermExampleInterval p = refl

    endpoint1TermExampleDepInterval : ∀ {ℓ} {A : I → Type ℓ} → (p : (i : I) → A i) →
      runTCTerm (endpoint1Term (quoteTerm p)) ≡ p i1
    endpoint1TermExampleDepInterval p = refl
