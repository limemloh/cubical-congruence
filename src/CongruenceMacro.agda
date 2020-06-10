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

  depFromArgs : (f : List (Arg Term) → Term) → (args : List (Arg Term)) → DepTree

  termToDep : Term → DepTree
  termToDep (var x args) = depFromArgs (var x) args
  termToDep (con c args) = depFromArgs (con c) args
  termToDep (def f args) = depFromArgs (def f) args
  termToDep t = mkLeaf t

  depFromArgs f args = helper f (mkLeaf (f [])) args
    where
      helper : (f : List (Arg Term) → Term) → DepTree → (args : List (Arg Term)) → DepTree
      helper f ltree [] = ltree
      helper f ltree (arg i t ∷ args) =
        let fn : List (Arg Term) → Term
            fn a = f (arg i t ∷ a)
            rtree = termToDep t
            tree = mkNode (mkLocal (fn []) ltree rtree)
        in helper fn tree args

  depToInput : DepTree → List Input
  depToInput (mkLeaf x) = []
  depToInput (mkNode (mkLocal c f a)) = depToInput f ++ depToInput a ∷ʳ Dep (mkNode (mkLocal c f a))

  termToDepInput : Term → List Input
  termToDepInput = depToInput ∘ termToDep

  pathToInput : Bool → Term → TC (List Input)
  pathToInput b term =
    do PInfo l r _ ← pathInfo term
       return (termToDepInput l ++ termToDepInput r ∷ʳ Eq b (mkEqual l r (fromTerm term)))

  termToInput : Term → TC (List Input)
  termToInput term =
    catchTC (pathToInput false term)
            (return (termToDepInput term))

  argsUntilVarN : ℕ → List (Arg Term) → List (Arg Term)
  argsUntilVarN d args = takeWhile (not ∘ isVarN d ∘ unwrapArg) args

  termsUsingAbs : Term → List Term
  termsUsingAbs (lam _ (abs _ t)) = helper 0 t
    where
      helper : ℕ → Term → List Term
      helperWithArgs : ℕ → (List (Arg Term) → Term) → List (Arg Term) → List Term
      helperWithArgs d f args =
        let found = if any (isVarN d ∘ unwrapArg) args
                    then mapIndex predℕ (f (argsUntilVarN d args)) ∷ []
                    else []
        in (flatmap (helper d ∘ unwrapArg) args) ++ found
      helper d (var x args) = helperWithArgs d (var x) args
      helper d (con c args) = helperWithArgs d (con c) args
      helper d (def f args) = helperWithArgs d (def f) args
      helper d (pat-lam cs args) = helperWithArgs d (pat-lam cs) args
      helper d (lam _ (abs _ x)) = helper (suc d) x
      helper d _ = []
  termsUsingAbs _ = []

  pathoverToInput : Maybe Term → TC (List Input)
  pathoverToInput nothing = return []
  pathoverToInput (just x) = mapTC flat (sequenceTC (mapList (pathToInput true) (termsUsingAbs x)))

  goalToInput : Term → TC (Term × Term × List Input)
  goalToInput goal = catchTC
    (do PInfo l r P ← pathInfo goal
        pathoverInput ← pathoverToInput P
        return (l , r , pathoverInput ++ termToDepInput l ++ termToDepInput r))
    (typeError (strErr "Failed to parse the goal as a path" ∷ []))

  -- Fetches and parses the context
  inputFromCtx : TC (List Input)
  inputFromCtx =
    do ctxTypes ← getContext
       let ctx = mapList (λ i → var i []) (range (length ctxTypes))
       let inputs = mapList termToInput (rev ctx)
       mapTC flat (sequenceTC inputs)
           
-- * Macros

  -- To put a cap on computation and satisfy the termination checker
  fuel = 10000

  -- Debug CC from the goal type
  computeCCHelper : Maybe Term → Term → TC Data
  computeCCHelper hint goalTy =
    do ctxInput ← inputFromCtx
       PInfo a b P ← pathTypeInfo goalTy
       pathoverInput ← pathoverToInput P
       hintInput ← case hint of λ {
         nothing → return [] ;
         (just info) → pathToInput false info }
       let input = pathoverInput ++ hintInput ++ termToDepInput a ++ termToDepInput b ++ ctxInput
       return (processInput fuel input)
  macro
    computeCC : Term → Term → TC Unit
    computeCC goaltype goal =
      do d ← computeCCHelper nothing goaltype
         dataTerm ← quoteTC d
         unify goal dataTerm
  
    computeCCHint : Term → Term → Term → TC Unit
    computeCCHint hint goaltype goal =
      do d ← computeCCHelper (just hint) goaltype
         dataTerm ← quoteTC d
         unify goal dataTerm
    -- computeCCH hint goal = computeCCHelper (just hint) goal

  noSolutionError : Term → Term → TC Unit
  noSolutionError a b = typeError
    (strErr "Unable to connect" ∷ termErr a ∷ strErr "and" ∷ termErr b ∷ [])

  noValidSolutionError : Term → Term → List (TC Term) → TC Unit
  noValidSolutionError a b solutions =
    do terms ← sequenceTC solutions
       let s = flatmap (λ t → strErr "[" ∷ termErr t ∷ strErr "]" ∷ []) terms
       typeError (strErr "Non of the connections between " ∷ termErr a ∷
                  strErr "and" ∷ termErr b ∷ strErr "were a match: " ∷ s)

  congruenceHelper : Maybe Term → Term → TC Unit
  congruenceHelper hint goal =
      do ctxInput ← inputFromCtx
         (l , r , goalInput) ← goalToInput goal
         hintInput ← case hint of λ {
           nothing → return [] ;
           (just help) → pathToInput false help }
         let solutions = congruenceClosure fuel l r (hintInput ++ goalInput ++ ctxInput)
         case solutions of λ {
           [] → noSolutionError l r ;
           (x ∷ x₁) → tryAll solutions (noValidSolutionError l r solutions)}
      where
        tryAll : List (TC Term) → TC Unit → TC Unit
        tryAll [] err = err
        tryAll (tc ∷ tcs) err =
          do t ← tc
             catchTC (unify goal t) (tryAll tcs err)

  macro
    congruenceH : Term → Term → TC Unit
    congruenceH hint goal = congruenceHelper (just hint) goal
    
    congruence : Term → TC Unit
    congruence goal = congruenceHelper nothing goal
