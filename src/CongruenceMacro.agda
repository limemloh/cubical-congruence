{-# OPTIONS --cubical --safe #-}

module CongruenceMacro where
  open import Cubical.Foundations.Everything hiding (empty)
  open import List hiding ([_])
  open import Cubical.Data.Prod hiding (map)
  open import Cubical.Data.Maybe
  open import Cubical.Data.Bool hiding (_≟_)
  import Agda.Builtin.Nat as Nat
  open import Cubical.Data.Nat
  open import Reflection hiding (Type; name; _≟_)
  open import ReflectionUtils
  open import CongruenceClosure

-- * Parsing Terms
  listTree : DepTree → List Input
  listTree (mkLeaf x) = []
  listTree (mkNode (mkLocal c f a)) = listTree f ++ listTree a ∷ʳ Dep (mkNode (mkLocal c f a))

  traverseArgs : ℕ → (List (Arg Term) → Term) → List (Arg Term) → TC DepTree

  termToTree : ℕ → Term → TC DepTree
  termToTree zero _ = typeError (strErr "Timeout" ∷ [])
  termToTree (suc n) (var x args) = traverseArgs n (var x) args
  termToTree (suc n) (con c args) = traverseArgs n (con c) args
  termToTree (suc n) (def f args) = traverseArgs n (def f) args
  termToTree _ (pat-lam cs args) = typeError (strErr "pat-lam is not of supported type." ∷ [])
  termToTree _ (agda-sort s) = typeError (strErr "agda-sort is not of supported type." ∷ [])
  termToTree _ (meta x x₁) = typeError (strErr "meta is not of supported type." ∷ [])
  termToTree _ t = return (mkLeaf t)

  traverseArgs n f args = mapTC proj₂ (foldl fn (return ([] , mkLeaf (f []))) args)
    where
      fn : TC (List (Arg Term) × DepTree) → Arg Term → TC (List (Arg Term) × DepTree)
      fn accTC (arg i x) =
        do acc ← accTC
           let args = proj₁ acc ∷ʳ (arg i x)
           let ltree = proj₂ acc
           rtree ← termToTree n x
           return (args , mkNode (mkLocal (f args) ltree rtree))

  parsePath : ℕ → Bool → Term → TC (List Input)
  parsePath n b term =
    do info ← getPathInfo term
       lt ← termToTree n (PathInfo.left info)
       rt ← termToTree n (PathInfo.right info)
       return (listTree lt ++ listTree rt ∷ʳ Eq b (mkEqual (ref lt) (ref rt) (fromTerm term)))

  parse : ℕ → Term → TC (List Input)
  parse n term =
    catchTC (parsePath n false term)
            (do tree ← termToTree n term
                return (listTree tree))

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
  
  parsePathover : ℕ → Term → List Term
  parsePathover n (lam _ (abs _ x)) = helper n 0 x
    where
      helper : ℕ → ℕ → Term → List Term
      helperWithArgs : ℕ → ℕ → (List (Arg Term) → Term) → List (Arg Term) → List Term
      helperWithArgs zero _ _ _ = []
      helperWithArgs (suc n) d f args =
        let argTerms = mapList unwrapArg args
            found = if any (isVarN d) argTerms then (mapIndex n predℕ (f (takeWhile (λ a → not (isVarN d (unwrapArg a))) args))) ∷ [] else []
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
  parsePathover n _ = []

  pathoverToEs : ℕ → Maybe Term → TC (List Input)
  pathoverToEs n nothing = return []
  pathoverToEs n (just x) = mapTC flat (sequence (mapList (parsePath n true) (parsePathover n x)))

  parseGoal : ℕ → Term → TC (Term × Term × List Input)
  parseGoal n goal = catchTC
    (do PInfo a b P ← getPathInfo goal
        aEs ← termToTree n a
        bEs ← termToTree n b
        pathoverEs ← pathoverToEs n P
        return ( a , b , pathoverEs ++ listTree aEs ++ listTree bEs ))
    (typeError (strErr "Failed parsing the goal" ∷ []))

  parseCtx : ℕ → TC (List Input)
  parseCtx n =
    do ctx ← getContext
       rec (length ctx)
    where
      rec : ℕ → TC (List Input)
      rec zero = return []
      rec (suc i) =
        do l ← parse n (var i [])
           r ← rec i
           return (l ++ r)
-- * Macros

  fuel = 10000

  -- Debug CC from the goal type
  computeCCHelper : Maybe Term → Term → TC Data
  computeCCHelper hint goalTy =
    do ctxEs ← parseCtx fuel
       (a , b , P) ← path-type-info goalTy
       aEs ← termToTree fuel a
       bEs ← termToTree fuel b
       pathoverEs ← pathoverToEs fuel (just P)
       helpEs ← case hint of λ {
         nothing → return [] ;
         (just help) → parsePath fuel false help }
       let cc = congruenceClosure fuel (helpEs ++ pathoverEs ++ listTree aEs ++ listTree bEs ++ ctxEs)
       return cc

  computeCC : Term → TC Data
  computeCC = computeCCHelper nothing
       
  computeCCH : Term → Term → TC Data
  computeCCH hint = computeCCHelper (just hint)

  congruenceHelper : Maybe Term → Term → TC Unit
  congruenceHelper hint goal =
      do ctxEs ← parseCtx fuel
         (a , b , goalEs) ← parseGoal fuel goal
         helpEs ← case hint of λ {
           nothing → return [] ;
           (just help) → parsePath fuel false help }
         let cc = congruenceClosure fuel (helpEs ++ goalEs ++ ctxEs)
         let solutions = connect fuel a b cc
         case solutions of λ {
           [] → typeError (strErr "Unable to connect" ∷ termErr a ∷ strErr "and" ∷ termErr b ∷ []) ;
           (x ∷ x₁) → tryAll solutions
             (typeError (strErr "Non of the connections between " ∷ termErr a ∷ strErr "and" ∷ termErr b ∷ strErr "were a match" ∷ []))}
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


