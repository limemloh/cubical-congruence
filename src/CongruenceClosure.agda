-- * Congruence Closure Procedure
-- The solution of Selsam and De Moura for Intensional Type Theory
-- naturally extended to Cubical Type Theory
{-# OPTIONS --cubical --safe #-}

module CongruenceClosure where
  open import Cubical.Foundations.Everything hiding (empty)
  open import List
  open import Cubical.Data.Prod hiding (map)
  open import Cubical.Data.Maybe
  open import Cubical.Data.Bool hiding (_≟_)
  import Agda.Builtin.Nat as Nat
  open import Cubical.Data.Nat
  import Relation.Nullary as N
  open import Reflection using (Term; TC) renaming (return to pure)
  open import Reflection.Term using (_≟_)
  open import ReflectionUtils

  _==_ : Term → Term → Bool
  l == r with (l ≟ r)
  l == r | does N.because proof = does

  _==ₓ_ : Term × Term → Term × Term → Bool
  (l₁ , l₂) ==ₓ (r₁ , r₂) = l₁ == r₁ and l₂ == r₂

  open import Map _==_ public
  import Map _==ₓ_ as Pair

  Ref = Term

  -- Dependency tree (Instead of dependency graph)
  data DepTree : Set

  -- Local Definition (c := l r)
  data LDef : Set where
    mkLocal : (c : Ref) → (f : DepTree) → (a : DepTree) → LDef

  -- Dependency tree : Either a Local definition or a typing
  data DepTree where
    mkNode : LDef → DepTree -- c := l r
    mkLeaf : Ref → DepTree -- a : A

  ref : DepTree → Ref
  ref (mkNode (mkLocal c f a)) = c
  ref (mkLeaf x) = x

  -- Edge in the equivalence graph
  data Edge : Set where
    -- From a proof in the context
    fromTerm : (prf : Term) → Edge
    -- Derive later using hcongr-ideal
    fromCongr : (fl : Ref) → (fr : Ref) → (al : Ref) → (ar : Ref) → Edge
    -- Flip edge later
    symEdge : Edge → Edge

  -- Collection of all the edges between two terms
  record ParallelEdges : Set where
    constructor mkParallelEdges
    field
      left : Ref
      right : Ref
      edges : List Edge

  mergeParallel : ParallelEdges → ParallelEdges → ParallelEdges
  mergeParallel (mkParallelEdges l r es₁) (mkParallelEdges _ _ es₂) = mkParallelEdges l r (es₁ ++ es₂)

  -- Input representation of equal
  record Equal : Set where
    constructor mkEqual
    field
      left : Ref
      right : Ref
      proof : Edge

  -- Input for the congruence closure procedure
  data Input : Set where
    -- Equality description and flag whether it is from the type path
    Eq : Bool → Equal → Input
    -- Dependency input
    Dep : DepTree → Input

  UseList = Map LDef

  record Data : Set where
    field
      -- Input still to process
      pending : List Input
      -- Like the representative in union-find
      repr : Map Ref
      -- To efficient iterate every vertex in a connect component
      next : Map Ref
      -- Tracking size of components
      size : Map ℕ
      -- Describe egdes/proofs in the univalent e-graph
      edges : Map (Map ParallelEdges)
      -- Keeps track of who depends on who
      useList : Map UseList
      -- Map where key is representatives of LDef
      congrTable : Pair.Map LDef

  initialData : List Input → Data
  initialData p = record { congrTable = Pair.empty
                         ; pending = p
                         ; repr = empty
                         ; next = empty
                         ; useList = empty
                         ; size = empty
                         ; edges = empty
                         }

  -- lookups with fallbacks
  repr : Ref → Data → Ref
  repr n d = findWithDefault n n (Data.repr d)

  next : Ref → Data → Ref
  next n d = findWithDefault n n (Data.next d)

  useList : Ref → Data → UseList
  useList n d = findWithDefault empty n (Data.useList d)

  size : Ref → Data → ℕ
  size n d = findWithDefault 1 (repr n d) (Data.size d)

  outgoing : Ref → Data → Map ParallelEdges
  outgoing n d =
    findWithDefault ((n , mkParallelEdges n n []) ∷ []) n (Data.edges d)

    -- Notation for equivalence of terms
  [_≊_]_ : Ref → Ref → Data → Bool
  [ l ≊ r ] d = repr l d == repr r d

  flipEdge : Edge → Edge
  flipEdge (symEdge e) = e
  flipEdge e = symEdge e

  -- A walk along paths
  Walk = List Edge

  -- Calculates all the walks from `a` to its representative
  walksToRepr : Ref → Data → List Walk
  walksToRepr a d = rec n a
    where
      -- Get the representative of a
      ra = repr a d
      n = size a d

      rec : ℕ → Ref → List Walk
      rec zero b = []
      rec (suc n) b = let
        -- Get the outgoing edges
        out = outgoing b d
        -- Recursively get walks from every endpoint of outgoing edge
        in flatmap helper (elems out)
        where
          helper : ParallelEdges → List Walk
          helper (mkParallelEdges l r edges) with l == r
          helper (mkParallelEdges _ r edges) | true = if r == ra then [] ∷ mapList [_] edges else []
          helper (mkParallelEdges _ r edges) | false =
            let restEdges = rec n r
                consEdge = λ edge → mapList (edge ∷_) restEdges
            in flatmap consEdge edges

  -- Reduce the walk length if possible
  shorten : Walk → Walk
  shorten [] = []
  shorten (fromTerm (ReflTerm _) ∷ es) = shorten es
  shorten (symEdge (fromTerm (ReflTerm _)) ∷ es) = shorten es
  shorten (l@(fromTerm prf₁) ∷ r@(symEdge (fromTerm prf₂)) ∷ es) = if prf₁ == prf₂ then shorten es else (l ∷ shorten (r ∷ es))
  shorten (l@(symEdge (fromTerm prf₁)) ∷ r@(fromTerm prf₂) ∷ es) = if prf₁ == prf₂ then shorten es else (l ∷ shorten (r ∷ es))
  shorten (symEdge (fromCongr fl fr al ar) ∷ es) = fromCongr fr fl ar al ∷ shorten es
  shorten (e ∷ es) = e ∷ shorten es

  -- Fix empty walks
  emptyToRefl : Ref → Walk → Walk
  emptyToRefl n [] = fromTerm (reflTerm n) ∷ []
  emptyToRefl _ e = e

  -- -- Making `a` the representative in its component
  promoteToRepr : Ref → Data → Data
  promoteToRepr a d = rec (size a d) a d
    where
      ra = repr a d
      rec : ℕ → Ref → Data → Data
      rec zero _ d = d
      rec (suc _) l d with l == ra
      rec (suc _) l d | true = d
      rec (suc n) l d | false =
        let outEdges = outgoing l d
            parallelEdges = elems outEdges
            d = record d { edges = delete l (Data.edges d) }
        in foldl helper d parallelEdges
        where
          helper : Data → ParallelEdges → Data
          helper d (mkParallelEdges l r pfs) =
            let d = rec n r d
                flipParallel = mkParallelEdges r l (mapList flipEdge pfs)
                outEdgesR = insertWith mergeParallel l flipParallel (outgoing r d)
                edges = insert r outEdgesR (Data.edges d)
            in record d {edges = edges}


  updateComponentRepr : Ref → Ref → Data → Data
  updateComponentRepr from to d =
    let mappedRepr = mapElems (λ rep → if rep == from then to else rep) (Data.repr d)
    in record d { repr = insert from to mappedRepr }
    -- -- TODO: Use next when Map is efficient
    -- record d {repr = rec (size from d) from (Data.repr d)}
    -- where
    --   rec : ℕ → Ref → Map Ref → Map Ref
    --   rec _ c m with c == to
    --   rec (suc n) c m | false = rec n (next c d) (insert c to m)
    --   rec _ _ m | _ = m

  -- Finds every possible walk between `l` and `r`
  walksBetween : Ref → Ref → Data → List Walk
  walksBetween l r d with [ l ≊ r ] d
  walksBetween l r d | false = []
  walksBetween l r d | true =
    -- Make `r` the representative
    let rsize = size r d
        d = promoteToRepr r d
        d = updateComponentRepr (repr l d) r d
        d = record d { size = insert r rsize (Data.size d) }
        -- Collect edges from `l` to the representative `r`
        walks = walksToRepr l d
    -- Find and remove cancellations
        shortWalks = mapList (emptyToRefl l ∘ shorten) walks
    in shortWalks

  connect : ℕ → Ref → Ref → Data → List (TC Term)
  connect zero    l r d = []
  connect (suc n) l r d = walksToTerms (walksBetween l r d)
    where
      walksToTerms : List Walk → List (TC Term)

      edgeToTerms : Edge → List (TC Term)
      edgeToTerms (fromTerm prf) = pure prf ∷ []
      edgeToTerms (fromCongr fl fr al ar) = hcongrTermsTC (connect n fl fr d) (connect n al ar d)
      edgeToTerms (symEdge e) = symTermsTC (edgeToTerms e)

      walkToTerms : Walk → List (TC Term)
      walkToTerms [] = []
      walkToTerms (edge ∷ []) = edgeToTerms edge
      walkToTerms (edge ∷ edges) = composeTerms (edgeToTerms edge) (walkToTerms edges)

      walksToTerms paths = flatmap walkToTerms paths

  -- CongrTable operations
  lDefToKey : LDef → Data → Ref × Ref
  lDefToKey (mkLocal c f a) d = (repr (ref f) d , repr (ref a) d)

  lookupCongr : LDef → Data → Maybe LDef
  lookupCongr l d = Pair.lookup (lDefToKey l d) (Data.congrTable d)

  insertCongr : LDef → Data → Data
  insertCongr e d = record d {
    congrTable = Pair.insert (lDefToKey e d) e (Data.congrTable d)}

  deleteCongr : LDef → Data → Data
  deleteCongr e d = record d {
    congrTable = Pair.delete (lDefToKey e d) (Data.congrTable d)}

  findOrInsertCongr : LDef → Data → Data
  findOrInsertCongr e d with lookupCongr e d
  findOrInsertCongr e d | nothing = insertCongr e d
  findOrInsertCongr (mkLocal c₁ f₁ a₁) d | just (mkLocal c₂ f₂ a₂) = record d {
    pending = Eq false (mkEqual c₁ c₂ (fromCongr (ref f₁) (ref f₂) (ref a₁) (ref a₂))) ∷ Data.pending d }

  -- Uselist operations
  addToUselist : Ref → LDef → Data → Data
  addToUselist n (mkLocal c f a) d = record d {
    useList = insert n (insert c (mkLocal c f a) (useList n d)) (Data.useList d) }

  copyUselist : Ref → Ref → Data → Data
  copyUselist from to d = record d {
    useList = insert to (union (useList from d) (useList to d)) (Data.useList d) }

  removeUses : UseList → Data → Data
  removeUses u d = foldl (λ d₁ l → deleteCongr l d₁) d (elems u)

  reinsertUses : UseList → Data → Data
  reinsertUses u d = foldl (λ d₁ l → findOrInsertCongr l d) d (elems u)

  swapNext : Ref → Ref → Data → Data
  swapNext l r d = let ln = next l d
                       rn = next r d
                   in record d { next = insert l rn (insert r ln (Data.next d)) }


  insertEdge : Ref → Ref → Edge → Data → Data
  insertEdge l r e d =
    let outgoingL = outgoing l d
        newOutgoingL = insertWith mergeParallel r (mkParallelEdges l r (e ∷ [])) outgoingL
    in record d { edges = insert l newOutgoingL (Data.edges d) }

  initUselist : LDef → LDef → Data → Data
  initUselist (mkLocal c f a) P d = addToUselist (ref f) P (addToUselist (ref a) P (rec f))
    where
      rec : DepTree → Data
      rec (mkNode x) = initUselist x P d
      rec (mkLeaf x) = d

  trivial : Ref → Data → Bool
  trivial r d = let out = outgoing r d
                    edges = lookup r out
                    in case edges of λ {
                      nothing → true ;
                      (just (mkParallelEdges left right edges)) → length edges Nat.< 1   }

  processDep : DepTree → Data → Data
  processDep (mkLeaf x) d = d
  processDep (mkNode l@(mkLocal c f a)) d =
    let edge = fromCongr (ref f) (ref f) (ref a) (ref a)
        d =
          -- TODO: Only add edge if nontrivial f = f or a = a exists
          -- if (trivial (ref f) d and trivial (ref f) d) then d else
               insertEdge c c edge d
    in
        findOrInsertCongr l (initUselist l l d)

  -- Depth First search with predicate
  dfsAny : (Ref → Bool) → Ref → Data → Bool
  dfsAny f a d = rec (size a d) f a d
    where
      rec : ℕ → (Ref → Bool) → Ref → Data → Bool
      rec zero _ _ _ = false
      rec (suc n) f a d = f a or any (λ x → rec n f (ParallelEdges.right (proj₂ x)) d) (outgoing a d)

  -- Assumes that the type path equalities are processed first
  processEq : Bool → Equal → Data → Data
  processEq _ (mkEqual l r _ ) d with [ l ≊ r ] d
  processEq false (mkEqual l r _) d | true = d
  processEq true (mkEqual l r edge) d | true =
    -- Input from type path inside a component
    let looping = l == r
        rCanReachL = dfsAny (λ n → n == l) r d
        swap = (not looping) and rCanReachL
        a = if swap then r else l
        b = if swap then l else r
        newEdge = if swap then flipEdge edge else edge
        -- TODO: If looping iterate uselist and add self-congruent egdes to deps
        in insertEdge a b newEdge d
  processEq _ (mkEqual l r edge) d | false =
    -- Input equality between different components
    let swap = size r d Nat.< size l d
        a = if swap then r else l
        b = if swap then l else r
        newEdge = if swap then flipEdge edge else edge
        ra = repr a d
        rb = repr b d
        d = removeUses (useList ra d) d
        d = promoteToRepr a d
        d = updateComponentRepr ra rb d
        d = record d { repr = insert a rb (Data.repr d) }
        d = record d { size = insert rb (size ra d + size rb d) (Data.size d) }
        d = insertEdge a b newEdge d
        d = reinsertUses (useList ra d) d
        d = swapNext ra rb d
        d = copyUselist ra rb d
    in d

  processInput : ℕ → List Input → Data
  processInput n p = rec n (initialData p)
    where
      rec : ℕ → Data → Data
      rec zero d = d
      rec (suc n) d with Data.pending d
      rec (suc n) d | [] = d
      rec (suc n) d | Eq b x ∷ p = rec n (processEq b x (record d { pending = p }))
      rec (suc n) d | Dep x ∷ p = rec n (processDep x (record d { pending = p }))

  -- The ℕ is "fuel" to satify the termination checker
  congruenceClosure : ℕ → Ref → Ref → List Input → List (TC Term)
  congruenceClosure n l r input = connect n l r (processInput n input)
