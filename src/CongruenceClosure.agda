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
  open import Reflection hiding (Type; name; _≟_)
  open import Reflection.Term using (_≟_)
  open import ReflectionUtils

  Ref = Term

  _==_ : Term → Term → Bool
  l == r with (l ≟ r)
  l == r | does N.because proof = does

  _==ₓ_ : Term × Term → Term × Term → Bool
  (l₁ , l₂) ==ₓ (r₁ , r₂) = l₁ == r₁ and l₂ == r₂

  open import Map _==_
  import Map _==ₓ_ as Pair

  K = Term

  -- Dependency tree (Technically it should be a graph)
  data Tree : Set

  -- Corresponds to a local definition (c := l r)
  data LDef : Set where
    mkLocal : (c : Ref) → (f : Tree) → (a : Tree) → LDef

  -- Either a Local definition or a typing
  data Tree where
    mkNode : LDef → Tree -- c := l r
    mkLeaf : Ref → Tree -- a : A

  data Edge : Set where
    fromTerm : (prf : Term) → Edge                       -- Something from the context
    fromCongr : (fl : Ref) → (fr : Ref) → (al : Ref) → (ar : Ref) → Edge -- Derive using hcongr-ideal
    symEdge : Edge → Edge

  -- Collection of all the edges between two terms
  record ParallelEdges : Set where
    constructor mkParallelEdges
    field
      left : Ref
      right : Ref
      edges : List Edge

  -- A walk along paths
  EPath = List Edge

  record Equal : Set where
    constructor mkEqual
    field
      left : Ref
      right : Ref
      proof : Edge

  data E : Set where
    Eq : Bool → Equal → E
    ¬Eq : Tree → E

  ref : Tree → Ref
  ref (mkNode (mkLocal c f a)) = c
  ref (mkLeaf x) = x

  UseList = Map LDef

  record Data : Set where
    field
      pending : List E          -- Information to add to the data structure
      repr : Map Ref            -- Like the representative in union-find
      next : Map Ref            -- To efficient iterate every vertex in a connect component
      size : Map ℕ              --
      proof : Map (Map ParallelEdges)   -- Describe egdes/proofs in the univalent e-graph
      useList : Map UseList     -- Keeps track of who depends on who
      congrTable : Pair.Map LDef -- Map such that LDef with same representatives are mapped to the same value

  initialData : List E → Data
  initialData p = record { congrTable = Pair.empty
                         ; pending = p
                         ; repr = empty
                         ; next = empty
                         ; useList = empty
                         ; size = empty
                         ; proof = empty
                         }

  -- lookups with fallbacks
  repr : Ref → Data → Ref
  repr n d = safeLookup n (Data.repr d) n

  next : Ref → Data → Ref
  next n d = safeLookup n (Data.next d) n

  useList : Ref → Data → UseList
  useList n d = safeLookup n (Data.useList d) empty

  size : Ref → Data → ℕ
  size n d = safeLookup n (Data.size d) 1

  mkReflEqual : Ref → Equal
  mkReflEqual n = mkEqual n n (fromTerm (reflTerm n))

  proof : Ref → Data → Map ParallelEdges
  proof n d = safeLookup n (Data.proof d) ((n , mkParallelEdges n n (fromTerm (reflTerm n) ∷ [])) ∷ [])

  flipEdge : Edge → Edge
  flipEdge (symEdge e) = e
  flipEdge e = symEdge e

  mkEPathsToRepr : Ref → Data → List EPath
  mkEPathsToRepr a d = rec n a
    where
    -- Get the representative of a
      ra = repr a d
      n = size ra d
    -- Recurser
      rec : ℕ → Ref → List EPath
      rec zero b = []
      -- Base case when reaching the representative
      rec (suc n) b = let
      -- Get the outgoing edges
        outgoing = proof b d
      -- Recursively get EPaths from every endpoint of outgoing edge
        epaths = flatmap (λ { (mkParallelEdges l r edges) →
          if l == r then (mapList (λ x → [ x ]) edges)
          else (flatmap (λ edge → mapList (λ rest → edge ∷ rest) (rec n r)) edges)
            }) (values outgoing)
        in epaths

  flipEPath : EPath → EPath
  flipEPath epaths = rev (mapList flipEdge epaths)

  composeEPaths : List EPath → List EPath → List EPath
  composeEPaths [] r = r
  composeEPaths l [] = l
  composeEPaths l r = flatmap (λ e → mapList (_++_ e) r) l

  compaction : EPath → EPath
  compaction [] = []
  compaction (fromTerm (ReflTerm _) ∷ es) = compaction es
  compaction (symEdge (fromTerm (ReflTerm _)) ∷ es) = compaction es
  compaction (l@(fromTerm prf₁) ∷ r@(symEdge (fromTerm prf₂)) ∷ es) = if prf₁ == prf₂ then compaction es else (l ∷ compaction (r ∷ es))
  compaction (l@(symEdge (fromTerm prf₁)) ∷ r@(fromTerm prf₂) ∷ es) = if prf₁ == prf₂ then compaction es else (l ∷ compaction (r ∷ es))
  compaction (e ∷ es) = e ∷ compaction es

  emptyToRefl : Ref → EPath → EPath
  emptyToRefl n [] = fromTerm (reflTerm n) ∷ []
  emptyToRefl _ e = e

  connectPath : Ref → Ref → Data → List EPath
  connectPath l r d with repr l d == repr r d
  connectPath l r d | false = []
  connectPath l r d | true =
    -- Proofs to each repr
    let lEPaths = mkEPathsToRepr l d
        rEPaths = mkEPathsToRepr r d
    -- Reverse the second one
        rEPathsFlipped = mapList flipEPath rEPaths
    -- Compose the two
        ePaths = composeEPaths lEPaths rEPathsFlipped
    -- Find and remove cancellations
        compactEPaths = mapList (emptyToRefl l) (mapList compaction ePaths)
    in compactEPaths

  connect : ℕ → Ref → Ref → Data → List (TC Term)
  connect zero    l r d = []
  connect (suc n) l r d = ePathsToTerms (connectPath l r d)
    where
      ePathsToTerms : List EPath → List (TC Term)

      edgeToTerms : Edge → List (TC Term)
      edgeToTerms (fromTerm prf) = return prf ∷ []
      edgeToTerms (fromCongr fl fr al ar) = hcongrTermsTC (connect n fl fr d) (connect n al ar d)
      edgeToTerms (symEdge e) = symTermsTC (edgeToTerms e)

      ePathToTerms : EPath → List (TC Term)
      ePathToTerms [] = []
      ePathToTerms (edge ∷ []) = edgeToTerms edge
      ePathToTerms (edge ∷ edges) = composeTerms (edgeToTerms edge) (ePathToTerms edges)

      ePathsToTerms paths = flatmap ePathToTerms paths

  -- CongrTable operations
  lDefKey : LDef → Data → Ref × Ref
  lDefKey (mkLocal c f a) d = (repr (ref f) d , repr (ref a) d)

  lookupCongr : LDef → Data → Maybe LDef
  lookupCongr l d = Pair.lookup (lDefKey l d) (Data.congrTable d)

  insertCongr : LDef → Data → Data
  insertCongr e d = record d { congrTable = Pair.insert (lDefKey e d) e (Data.congrTable d)}

  deleteCongr : LDef → Data → Data
  deleteCongr e d = record d { congrTable = Pair.delete (lDefKey e d) (Data.congrTable d)}

  -- Similar notation as the Lean paper
  [_≊_]_ : Ref → Ref → Data → Bool
  [ l ≊ r ] d = repr l d == repr r d

  findOrInsertCongr : LDef → Data → Data
  findOrInsertCongr e d with lookupCongr e d
  findOrInsertCongr e d | nothing = insertCongr e d
  findOrInsertCongr (mkLocal c₁ f₁ a₁) d | just (mkLocal c₂ f₂ a₂) =
    record d { pending = Eq false (mkEqual c₁ c₂ (fromCongr (ref f₁) (ref f₂) (ref a₁) (ref a₂))) ∷ Data.pending d }

  addToUselist : Ref → LDef → Data → Data
  addToUselist n (mkLocal c f a) d =
    record d { useList = insert n (insert c (mkLocal c f a) (useList n d)) (Data.useList d) }

  moveUselist : Ref → Ref → Data → Data
  moveUselist from to d = record d { useList = insert to (union (useList from d) (useList to d)) (Data.useList d) }

  removeUses : UseList → Data → Data
  removeUses u d = rec (toList u) d
    where
      rec : List (Ref × LDef) → Data → Data
      rec [] d = d
      rec ((n , l) ∷ xs) d = rec xs (deleteCongr l d)

  reinsertUses : UseList → Data → Data
  reinsertUses u d = rec (toList u) d
    where
      rec : List (Ref × LDef) → Data → Data
      rec [] d = d
      rec ((n , l) ∷ xs) d = rec xs (findOrInsertCongr l d)

  swapNext : Ref → Ref → Data → Data
  swapNext l r d = let ln = next l d
                       rn = next r d
                   in record d { next = insert l rn (insert r ln (Data.next d)) }

  -- Flips proofs making `a` the representative in the component
  flipProofs : Ref → Data → Data
  flipProofs a d = rec (size (repr a d) d) a d
    where
      rec : ℕ → Ref → Data → Data
      rec zero _ d = d
      rec (suc n) l d with repr l d == l
      rec (suc n) l d | true = d
      rec (suc n) l d | false = foldl helper d (values (proof l d))
        where
          helper : Data → ParallelEdges → Data
          helper d (mkParallelEdges l r pfs) = record d {
            proof = update r (insert l (mkParallelEdges r l (mapList flipEdge pfs))) (Data.proof (rec n r d)) }

  insertProof : Ref → Ref → Edge → Data → Data
  insertProof l r e d = record d { proof = insert l (updater r (λ x → just (mkParallelEdges l r (e ∷ (fromJust-def [] (map-Maybe ParallelEdges.edges x))))) (proof l d) ) (Data.proof d) }
  -- record d { proof = update l (update r (λ par → record par { edges = e ∷ ParallelEdges.edges par })) (Data.proof d) }

  initialize : Tree → Data → Data
  initialize (mkNode l@(mkLocal c f a)) d =
    let d = inituselist l l d
        -- d = insertProof c c (fromCongr (ref f) (ref f) (ref a) (ref a)) d -- This solution makes some example spin forever
        d = findOrInsertCongr l d
    in d
    where
      inituselist : LDef → LDef → Data → Data
      inituselist (mkLocal c f a) P d = addToUselist (ref f) P (addToUselist (ref a) P (rec f))
        where
          rec : Tree → Data
          rec (mkNode x) = inituselist x P d
          rec (mkLeaf x) = d
  initialize (mkLeaf x) d = d

  dfsAny : (Ref → Bool) → Ref → Data → Bool
  dfsAny f a d = rec (size (repr a d) d) f a d
    where
      rec : ℕ → (Ref → Bool) → Ref → Data → Bool
      rec zero _ _ _ = false
      rec (suc n) f a d = f a or any (λ x → rec n f (ParallelEdges.right (proj₂ x)) d) (proof a d)

  -- Assumes that the important paths are processed first
  processEq : Bool → Equal → Data → Data
  processEq _ (mkEqual l r _ ) d with [ l ≊ r ] d
  processEq false (mkEqual l r _) d | true = d
  processEq true (mkEqual l r edge) d | true =
    -- Find which direction to insert path by DFS for other endpoint
    let looping = l == r
        rCanReachL = dfsAny (λ n → n == l) r d
        swap = (not looping) and rCanReachL
        a = if swap then r else l
        b = if swap then l else r
        newEdge = if swap then flipEdge edge else edge
    -- Insert edge
        d = insertProof a b newEdge d
     in d
  processEq _ (mkEqual l r edge) d | false =
    let swap = size (repr r d) d Nat.< size (repr l d) d
        a = if swap then r else l
        b = if swap then l else r
        newEdge = if swap then flipEdge edge else edge
        ra = repr a d
        rb = repr b d
        d = removeUses (useList ra d) d
        d = flipProofs a d
        mappedRepr = mapValues (λ rep → if rep == ra then rb else rep) (Data.repr d)
        d = record d { repr = insert a rb mappedRepr }
        d = insertProof a b newEdge d
        d = reinsertUses (useList ra d) d
        d = swapNext ra rb d
        d = moveUselist ra rb d
        d = record d { size = insert rb (size ra d + size rb d) (Data.size d) }
    in d

  -- The ℕ is "fuel" to satify the termination checker
  congruenceClosure : ℕ → List E → Data
  congruenceClosure n p = rec n (initialData p)
    where
      rec : ℕ → Data → Data
      rec zero d = d
      rec (suc n) d with Data.pending d
      rec (suc n) d | [] = d
      rec (suc n) d | Eq b x ∷ p = rec n (processEq b x (record d { pending = p }))
      rec (suc n) d | ¬Eq x ∷ p = rec n (initialize x (record d { pending = p }))
