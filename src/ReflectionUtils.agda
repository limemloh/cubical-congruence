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

  open import List hiding ([_])

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

  mapArgList : (Term → Term) → List (Arg Term) → List (Arg Term)
  mapArgList f args = mapList (λ {(arg i x) → arg i (f x)}) args

  mapIndex : (ℕ → ℕ) → Term → Term
  mapIndex f (var x args) = var (f x) (mapList (λ {(arg i x) → arg i (mapIndex f x)}) args)
  mapIndex f (con c args) = con c (mapList (λ {(arg i x) → arg i (mapIndex f x)}) args)
  mapIndex f (def f₁ args) = def f₁ (mapList (λ {(arg i x) → arg i (mapIndex f x)}) args)
  mapIndex f (lam v (abs s x)) = lam v (abs s (mapIndex f x))
  mapIndex f (pat-lam cs args) = pat-lam cs (mapList (λ {(arg i x) → arg i (mapIndex f x)}) args)
  mapIndex f (pi (arg i a) (abs s x)) = pi (arg i (mapIndex f a)) (abs s (mapIndex f x))
  mapIndex f (agda-sort (Sort.set t)) = agda-sort (Sort.set (mapIndex f t))
  mapIndex f t = t

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

  pathTypeInfo : Term → TC PathInfo
  pathTypeInfo ty = catchTC (helper ty)
                            (do n ← reduce ty
                                helper n)
    where
      helper : Term → TC PathInfo
      helper (def (quote _≡_) (_ ∷ arg _ P ∷ arg _ l ∷ arg _ r ∷ [])) = return (PInfo l r nothing)
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

  pathInfo : Term → TC PathInfo
  pathInfo t =
    do isInter ← isIntervalFn t
       if isInter then
         (do l ← endpoint0Term t
             r ← endpoint1Term t
             return (PInfo l r nothing))
         else do ty ← inferType t
                 pathTypeInfo ty

-- * Building Terms
  pattern SymTerm p = (def (quote sym) (_ ∷ _ ∷ _ ∷ _ ∷ arg _ p ∷ []))
  pattern SymPTerm p = (def (quote symP) (_ ∷ _ ∷ _ ∷ _ ∷ arg _ p ∷ []))
  pattern ReflTerm n = (def (quote refl)) (_ ∷ _ ∷ arg _ n ∷ [])

  symTerm : Term → Term
  symTerm (SymTerm p) = p
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

  composeTerm : Term → Term → TC Term
  composeTerm (SymPTerm p) (SymPTerm q) = mapTC symTerm (composeTerm q p)
  composeTerm (SymTerm p) (SymTerm q) = mapTC symTerm (composeTerm q p)
  composeTerm (ReflTerm _) q = return q
  composeTerm p (ReflTerm _) = return p
  composeTerm p q =
    do hp ← isHomogeneous p
       hq ← isHomogeneous q
       return (compose hp hq)
    where
      compose : Bool → Bool → Term
      compose true  true  = def (quote _∙_)             (repeat 5 (hArg unknown) ++ vArg p ∷ vArg q ∷ [])
      compose true  false = def (quote comp-Path-PathP) (repeat 7 (hArg unknown) ++ vArg p ∷ vArg q ∷ [])
      compose false true  = def (quote comp-PathP-Path) (repeat 7 (hArg unknown) ++ vArg p ∷ vArg q ∷ [])
      compose false false = def (quote compPathP)       (repeat 6 (hArg unknown) ++ vArg p ∷ vArg q ∷ [])

  composeTCTerm : TC Term → TC Term → TC Term
  composeTCTerm tc-p tc-q =
    do p ← tc-p
       q ← tc-q
       composeTerm p q

  composeTerms : List (TC Term) → List (TC Term) → List (TC Term)
  composeTerms l r = flatmap (λ x → mapList (composeTCTerm x) r) l

  hcongr-ideal : ∀ {ℓ} {A : I → Type ℓ}
                   {C : (i : I) → A i → Type ℓ}
                   {f : (a : A i0) → C i0 a} {g : (b : A i1) → C i1 b}
                   {a : A i0} {b : A i1} →
                   (α : PathP (λ i → (x : A i) → C i x) f g) →
                   (p : PathP A a b) →
                   PathP (λ i → C i (p i)) (f a) (g b)
  hcongr-ideal α p = λ i → α i (p i)

  hcongrTerm : Term → Term → Term
  hcongrTerm α p = (def (quote hcongr-ideal) (repeat 7 (hArg unknown) ++ vArg α ∷ vArg p ∷ []))

  hcongrTerms : List Term → List Term → List Term
  hcongrTerms fs as = flatmap (λ f → mapList (hcongrTerm f) as) fs

  hcongrTermTC : TC Term → TC Term → TC Term
  hcongrTermTC tc-α tc-p =
    do α ← tc-α
       p ← tc-p
       return (hcongrTerm α p)

  hcongrTermsTC : List (TC Term) → List (TC Term) → List (TC Term)
  hcongrTermsTC fs as = flatmap (λ f → mapList (hcongrTermTC f) as) fs

  module Examples where
    Example-pathInfo-Path : ∀ {ℓ} {A : Type ℓ} {a b : A} → (p : a ≡ b) →
      runTC (pathInfo (quoteTerm p)) ≡ PInfo (quoteTerm a) (quoteTerm b) nothing
    Example-pathInfo-Path p = refl

    Example-pathInfo-PathP : ∀ {ℓ} {A : I → Type ℓ} {a : A i0} {b : A i1} → (p : PathP A a b) →
      runTC (pathInfo (quoteTerm p)) ≡ PInfo (quoteTerm a) (quoteTerm b) (just (quoteTerm A))
    Example-pathInfo-PathP p = refl

    Example-pathInfo-Interval : ∀ {ℓ} {A : Type ℓ} → (p : I → A) →
      runTC (pathInfo (quoteTerm p)) ≡ PInfo (quoteTerm (p i0)) (quoteTerm (p i1)) nothing
    Example-pathInfo-Interval p = refl

    Example-pathInfo-DepInterval : ∀ {ℓ} {A : I → Type ℓ} → (p : (i : I) → A i) →
      runTC (pathInfo (quoteTerm p)) ≡ PInfo (quoteTerm (p i0)) (quoteTerm (p i1)) nothing
    Example-pathInfo-DepInterval p = refl

    Example-isHomogeneous-Path : ∀ {ℓ} {A : Type ℓ} {a b : A} → (p : a ≡ b) →
      runTC (isHomogeneous (quoteTerm p)) ≡ true
    Example-isHomogeneous-Path p = refl

    Example-isHomogeneous-PathP : ∀ {ℓ} {A : I → Type ℓ} {a : A i0} {b : A i1} → (p : PathP A a b) →
      runTC (isHomogeneous (quoteTerm p)) ≡ false
    Example-isHomogeneous-PathP p = refl

    Example-isHomogeneous-PathPHom : ∀ {ℓ} {A : I → Type ℓ} {a b : A i0} → (p : PathP (λ i → A i0) a b) →
      runTC (isHomogeneous (quoteTerm p)) ≡ true
    Example-isHomogeneous-PathPHom p = refl

    -- Example-isHomogeneous-Interval : ∀ {ℓ} {A : Type ℓ} → (p : I → A) →
    --   runTC (isHomogeneous (quoteTerm p)) ≡ true
    -- Example-isHomogeneous-Interval p = refl

    Example-isHomogeneous-DepInterval : ∀ {ℓ} {A : I → Type ℓ} → (p : (i : I) → A i) →
      runTC (isHomogeneous (quoteTerm p)) ≡ false
    Example-isHomogeneous-DepInterval p = refl

    Example-isIntervalFn-Interval : ∀ {ℓ} {A : Type ℓ} → (p : I → A) →
      runTC (isIntervalFn (quoteTerm p)) ≡ true
    Example-isIntervalFn-Interval p = refl

    Example-isIntervalFn-DepInterval : ∀ {ℓ} {A : I → Type ℓ} → (p : (i : I) → A i) →
      runTC (isIntervalFn (quoteTerm p)) ≡ true
    Example-isIntervalFn-DepInterval p = refl

    Example-isIntervalFn-Path : ∀ {ℓ} {A : Type ℓ} {a b : A} → (p : a ≡ b) →
      runTC (isIntervalFn (quoteTerm p)) ≡ false
    Example-isIntervalFn-Path p = refl

    Example-isIntervalFn-PathP : ∀ {ℓ} {A : I → Type ℓ} {a : A i0} {b : A i1} → (p : PathP A a b) →
      runTC (isIntervalFn (quoteTerm p)) ≡ false
    Example-isIntervalFn-PathP p = refl

    Example-endpoint0Term-Interval : ∀ {ℓ} {A : Type ℓ} → (p : I → A) →
      runTCTerm (endpoint0Term (quoteTerm p)) ≡ p i0
    Example-endpoint0Term-Interval p = refl

    Example-endpoint0Term-DepInterval : ∀ {ℓ} {A : I → Type ℓ} → (p : (i : I) → A i) →
      runTCTerm (endpoint0Term (quoteTerm p)) ≡ p i0
    Example-endpoint0Term-DepInterval p = refl

    Example-endpoint1Term-Interval : ∀ {ℓ} {A : Type ℓ} → (p : I → A) →
      runTCTerm (endpoint1Term (quoteTerm p)) ≡ p i1
    Example-endpoint1Term-Interval p = refl

    Example-endpoint1Term-DepInterval : ∀ {ℓ} {A : I → Type ℓ} → (p : (i : I) → A i) →
      runTCTerm (endpoint1Term (quoteTerm p)) ≡ p i1
    Example-endpoint1Term-DepInterval p = refl

    Example-composeTerm-PathPath : ∀ {ℓ} {A : Type ℓ} {a b c : A} (p : a ≡ b) (q : b ≡ c) →
      runTCTerm (composeTerm (quoteTerm p) (quoteTerm q)) ≡ p ∙ q
    Example-composeTerm-PathPath p q = refl

    Example-composeTerm-ReflPath : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b)  →
      runTCTerm (composeTerm (quoteTerm (refl {x = a})) (quoteTerm p)) ≡ p
    Example-composeTerm-ReflPath p = refl

    Example-composeTerm-PathRefl : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b)  →
      runTCTerm (composeTerm (quoteTerm p) (quoteTerm (refl {x = a}))) ≡ p
    Example-composeTerm-PathRefl p = refl

    Example-composeTerm-SymSym : ∀ {ℓ} {A : Type ℓ} {a b c : A} (p : a ≡ b) (q : b ≡ c) →
      runTCTerm (composeTerm (quoteTerm (sym q)) (quoteTerm (sym p))) ≡ sym (p ∙ q)
    Example-composeTerm-SymSym p q = refl


    -- test :  ∀ {ℓ} {A : Type ℓ} {a : A} {b : A} →
    --   runTCTerm (normalise (quoteTerm ((λ i → A)[ a ≡ b ]))) ≡ {!!}
    -- test p = {!!}
