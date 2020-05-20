{-# OPTIONS --cubical --safe #-}

module ReflectionUtils where
  open import Cubical.Foundations.Everything hiding (empty)
  open import Cubical.Data.Bool hiding (_≟_)
  open import Cubical.Data.Prod
  open import Cubical.Data.Maybe
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
    runTCt : TC Term → Term → TC Unit
    runTCt tc goal =
      do a ← tc
         unify goal a

  mapTC : {A B : Set} → (f : A → B) → TC A →  TC B
  mapTC f tc = do x ← tc
                  return (f x)

  sequence : {A : Set} → List (TC A) → TC (List A)
  sequence [] = return []
  sequence (tc ∷ tcs) =
    do x ← tc
       xs ← sequence tcs
       return (x ∷ xs)

  unwrapArg : Arg Term → Term
  unwrapArg (arg _ x) = x

  mapArg : (Term → Term) → Arg Term → Arg Term
  mapArg f (arg i a) = arg i (f a)

  isVarN : Nat.Nat → Term → Bool
  isVarN n (var x _) = n Nat.== x
  isVarN n _ = false

  apply : ∀ {ℓ} {ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → (f : (a : A) → B a) → (a : A) → B a
  apply f a = f a

  applyI : ∀ {ℓ} {B : I → Type ℓ} → (f : (a : I) → B a) → (a : I) → B a
  applyI f a = f a

  applyTerm : Term → Term → Term
  applyTerm f a = def (quote apply) (repeat 4 (hArg unknown) ++ vArg f ∷ vArg a ∷ [])

  endpoint0 : ∀ {ℓ} (P : I → Type ℓ) → Type ℓ
  endpoint0 P = P i0

  endpoint1 : ∀ {ℓ} (P : I → Type ℓ) → Type ℓ
  endpoint1 P = P i1

  endpoint0Term : Term → TC Term
  endpoint0Term P = normalise (def (quote endpoint0) (hArg unknown ∷ vArg P ∷ []))

  endpoint1Term : Term → TC Term
  endpoint1Term P = normalise (def (quote endpoint1) (hArg unknown ∷ vArg P ∷ []))

  isIntervalPath : Term → TC Bool
  isIntervalPath t =
    catchTC (do (checkType t (pi (vArg (def (quote I) [])) (abs "_" unknown)))
                return true)
            (return false)

  isHomogeneous : Term → TC Bool
  isHomogeneous t = withNormalisation true
    (catchTC (do checkType t (def (quote _≡_) (repeat 2 (hArg unknown) ++ repeat 2 (vArg unknown)))
                 return true)
             (return false))

  path-type-info : Term → TC (Term × Term × Term)
  path-type-info ty = catchTC (helper ty)
                              (do n ← reduce ty
                                  helper n)
    where
      helper : Term → TC (Term × Term × Term)
      helper (def (quote _≡_) (_ ∷ arg _ P ∷ arg _ l ∷ arg _ r ∷ [])) = return (l , r ,  P)
      helper (def (quote PathP) (_ ∷ arg _ P ∷ arg _ l ∷ arg _ r ∷ [])) = return (l , r ,  P)
      helper t = typeError (strErr "Term" ∷ termErr t ∷ strErr "is not a path." ∷ [])

  path-info : Term → TC (Term × Term × Term)
  path-info t = -- withNormalisation true
    do ty ← inferType t
       path-type-info ty

  record PathInfo : Set where
    constructor PInfo
    field
      left : Term
      right : Term
      pathover : Maybe Term
  open PathInfo

  getSimplePathInfo : Term → TC PathInfo
  getSimplePathInfo t =
    do (l , r , P) ← path-info t
       hom ← isHomogeneous t
       return (PInfo l r (if hom then nothing else (just P)))

  getPathInfo : Term → TC PathInfo
  getPathInfo t =
    do isInter ← isIntervalPath t
       if isInter then
         (do l ← endpoint0Term t
             r ← endpoint1Term t
             return (PInfo l r nothing))
         else getSimplePathInfo t

  getPathover : Term → TC Term
  getPathover t = do (_ , _ , P) ← path-info t
                     return P

  -- ** Reflection Helpers

  reflTerm : Term → Term
  reflTerm t = (def (quote refl) (hArg unknown ∷ hArg unknown ∷ hArg t ∷ []))

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
