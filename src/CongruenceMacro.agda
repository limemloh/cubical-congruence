{-# OPTIONS --cubical --safe #-}

module CongruenceMacro where
  open import Cubical.Foundations.Everything hiding (empty)
  open import List
  open import Cubical.Data.Prod hiding (map)
  open import Cubical.Data.Maybe
  open import Cubical.Data.Bool hiding (_≟_)
  import Agda.Builtin.Nat as Nat
  open import Cubical.Data.Nat
  open import Reflection hiding (Type; name; _≟_)
  open import ReflectionUtils
  open import CongruenceClosure

-- * Parsing Term to input

  traverseArgs : ℕ → (List (Arg Term) → Term) → List (Arg Term) → TC DepTree

  termToDep : ℕ → Term → TC DepTree
  termToDep zero _ = typeError (strErr "Timeout" ∷ [])
  termToDep (suc n) (var x args) = traverseArgs n (var x) args
  termToDep (suc n) (con c args) = traverseArgs n (con c) args
  termToDep (suc n) (def f args) = traverseArgs n (def f) args
  termToDep _ (pat-lam cs args) = typeError (strErr "pat-lam is not of supported type." ∷ [])
  termToDep _ (agda-sort s) = typeError (strErr "agda-sort is not of supported type." ∷ [])
  termToDep _ (meta x x₁) = typeError (strErr "meta is not of supported type." ∷ [])
  termToDep _ t = return (mkLeaf t)

  traverseArgs n f args = mapTC proj₂ (foldl fn (return ([] , mkLeaf (f []))) args)
    where
      fn : TC (List (Arg Term) × DepTree) → Arg Term → TC (List (Arg Term) × DepTree)
      fn accTC (arg i x) =
        do acc ← accTC
           let args = proj₁ acc ∷ʳ (arg i x)
           let ltree = proj₂ acc
           rtree ← termToDep n x
           return (args , mkNode (mkLocal (f args) ltree rtree))

  depToInput : DepTree → List Input
  depToInput (mkLeaf x) = []
  depToInput (mkNode (mkLocal c f a)) = depToInput f ++ depToInput a ∷ʳ Dep (mkNode (mkLocal c f a))

  pathToInput : ℕ → Bool → Term → TC (List Input)
  pathToInput n b term =
    do info ← getPathInfo term
       lt ← termToDep n (PathInfo.left info)
       rt ← termToDep n (PathInfo.right info)
       return (depToInput lt ++ depToInput rt ∷ʳ Eq b (mkEqual (ref lt) (ref rt) (fromTerm term)))

  termToInput : ℕ → Term → TC (List Input)
  termToInput n term =
    catchTC (pathToInput n false term)
            (do tree ← termToDep n term
                return (depToInput tree))

  pathoverToTerms : ℕ → Term → List Term
  pathoverToTerms n (lam _ (abs _ x)) = helper n 0 x
    where
      helper : ℕ → ℕ → Term → List Term
      helperWithArgs : ℕ → ℕ → (List (Arg Term) → Term) → List (Arg Term) → List Term
      helperWithArgs zero _ _ _ = []
      helperWithArgs (suc n) d f args =
        let argTerms = mapList unwrapArg args
            found = if any (isVarN d) argTerms then
              mapIndex n predℕ (f (takeWhile (λ a → not (isVarN d (unwrapArg a))) args)) ∷ []
                else []
        in flatmap (helper n d) argTerms ++ found
      helper zero _ _ = []
      helper (suc n) d (var x args) = helperWithArgs n d (var x) args
      helper (suc n) d (con c args) = helperWithArgs n d (con c) args
      helper (suc n) d (def f args) = helperWithArgs n d (def f) args
      helper (suc n) d (pat-lam cs args) = helperWithArgs n d (pat-lam cs) args
      helper (suc n) d (lam _ (abs _ x)) = helper n (suc d) x
      helper (suc n) d (pi a b) = []
      helper (suc n) d (agda-sort s) = []
      helper (suc n) d (lit l) = []
      helper (suc n) d (meta x x₁) = []
      helper (suc n) d unknown = []
  pathoverToTerms n _ = []

  pathoverToInput : ℕ → Maybe Term → TC (List Input)
  pathoverToInput n nothing = return []
  pathoverToInput n (just x) = mapTC flat (sequenceTC (mapList (pathToInput n true) (pathoverToTerms n x)))

  goalToInput : ℕ → Term → TC (Term × Term × List Input)
  goalToInput n goal = catchTC
    (do PInfo a b P ← getPathInfo goal
        aInput ← termToDep n a
        bInput ← termToDep n b
        pathoverInput ← pathoverToInput n P
        return ( a , b , pathoverInput ++ depToInput aInput ++ depToInput bInput ))
    (typeError (strErr "Failed parsing the goal" ∷ []))

  -- Fetches and parses the context
  inputFromCtx : ℕ → TC (List Input)
  inputFromCtx n =
    do ctx ← getContext
       rec (length ctx)
    where
      rec : ℕ → TC (List Input)
      rec zero = return []
      rec (suc i) =
        do l ← termToInput n (var i [])
           r ← rec i
           return (l ++ r)
           
-- * Macros

  -- To put a cap on computation and satisfy the termination checker
  fuel = 10000

  -- Debug CC from the goal type
  computeCCHelper : Maybe Term → Term → TC Data
  computeCCHelper hint goalTy =
    do ctxInput ← inputFromCtx fuel
       PInfo a b P ← getPathTypeInfo goalTy
       aInput ← termToDep fuel a
       bInput ← termToDep fuel b
       pathoverInput ← pathoverToInput fuel P
       hintInput ← case hint of λ {
         nothing → return [] ;
         (just info) → pathToInput fuel false info }
       let input = pathoverInput ++ hintInput ++ depToInput aInput ++ depToInput bInput ++ ctxInput
       return (congruenceClosure fuel input)

  computeCC : Term → TC Data
  computeCC = computeCCHelper nothing
       
  computeCCH : Term → Term → TC Data
  computeCCH hint = computeCCHelper (just hint)

  noSolutionError : Term → Term → TC Unit
  noSolutionError a b = typeError
    (strErr "Unable to connect" ∷ termErr a ∷ strErr "and" ∷ termErr b ∷ [])

  noValidSolutionError : Term → Term → TC Unit
  noValidSolutionError a b = typeError
    (strErr "Non of the connections between " ∷ termErr a ∷
      strErr "and" ∷ termErr b ∷ strErr "were a match" ∷ [])

  congruenceHelper : Maybe Term → Term → TC Unit
  congruenceHelper hint goal =
      do ctxInput ← inputFromCtx fuel
         (a , b , goalInput) ← goalToInput fuel goal
         hintInput ← case hint of λ {
           nothing → return [] ;
           (just help) → pathToInput fuel false help }
         let cc = congruenceClosure fuel (hintInput ++ goalInput ++ ctxInput)
         let solutions = connect fuel a b cc
         case solutions of λ {
           [] → noSolutionError a b ;
           (x ∷ x₁) → tryAll solutions (noValidSolutionError a b)}
      where
        tryAll : List (TC Term) → TC Unit → TC Unit
        tryAll [] err = err
        tryAll (tc ∷ tcs) err =
          do t ← tc
             catchTC (unify goal t) (tryAll tcs err)

  macro
    congruenceH : Term → Term → TC Unit
    congruenceH hint = congruenceHelper (just hint)
    
    congruence : Term → TC Unit
    congruence = congruenceHelper nothing


