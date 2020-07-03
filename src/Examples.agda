{-# OPTIONS --cubical --safe #-}

module Examples where
  open import Cubical.Foundations.Everything
  open import Cubical.Data.Nat
  open import Cubical.Data.Maybe
  open import Cubical.Data.List
  open import Cubical.Data.Prod
  open import CongruenceMacro

  -- For debugging
  open import CongruenceClosure
  open import ReflectionUtils
  open import Reflection hiding (Type)

  private
    variable
      ℓ : Level
      A : Set ℓ
      a : A
      b : A
      c : A

  -- Symmetry
  test₁ : a ≡ b → b ≡ a
  test₁ p = congruence

  -- Transitivity
  test₂ : a ≡ b → b ≡ c → a ≡ c
  test₂ p q = congruence

  -- Symmetry and Transitivity
  test₃ : b ≡ a → b ≡ c → a ≡ c
  test₃ p q = congruence

  test₄ : c ≡ b → b ≡ a → a ≡ c
  test₄ p q = congruence

  -- Congruence one function
  test₅ : (f : A → A) → a ≡ b → f a ≡ f b
  test₅ f p = congruence

  -- Congruence and Transitivity
  test₆ : (f : A → A) → a ≡ b → b ≡ c → f a ≡ f c
  test₆ f p q = congruence

  -- Congruence two functions of same type
  test₇ : {f g : A → A} → f ≡ g → a ≡ b → f a ≡ g b
  test₇ pf p = congruence

  -- Transitivity and congruence: two functions of same type
  test₈ : {f g : A → A} → f ≡ g → a ≡ b → b ≡ c → f a ≡ g c
  test₈ pf p q = congruence

  test₉ : ∀ {ℓ} {A B : Type ℓ} {f : A → B → A} {a : A} {b : B} → f a b ≡ a → f (f a b) b ≡ a
  test₉ p = congruence

  -- Taken from https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.congruence
  test₁₀ : ∀ {f : A → A} {g : A → A → A} {a b : A} → a ≡ f a → g b (f a) ≡ f (f a) → g a b ≡ f (g b a) → g a b ≡ a
  test₁₀ p q r = congruence

  -- Congruence contructor
  test₁₁ : ∀ {ℓ} {A : Type ℓ} {a b : A} → a ≡ b → just a ∷ [] ≡ just b ∷ []
  test₁₁ p = congruence

  -- Literals
  test₁₂ : 2 ≡ 3 → 3 ≡ 2
  test₁₂ p = congruence

  -- Transitivity heterogeneuos
  test₁₃ : ∀ {ℓ} {A B C : Type ℓ} {AB : A ≡ B} {BC : B ≡ C} {a : A} {b : B} {c : C} →
    PathP (λ i → AB i) a b → PathP (λ i → BC i) b c → PathP (λ i → (AB ∙ BC) i) a c
  test₁₃ p q = congruence

  -- Transitivity heterogeneuos and homogeneous
  test₁₄ : ∀ {ℓ} {A B : Type ℓ} {AB : A ≡ B} {a : A} {b b' : B} →
    PathP (λ i → AB i) a b → b ≡ b' → PathP (λ i → AB i) a b'
  test₁₄ p q = congruence

  -- Transitivity homogeneous and heterogeneuos
  test₁₅ : ∀ {ℓ} {A B : Type ℓ} {AB : A ≡ B} {a a' : A} {b : B} →
    a ≡ a' → PathP (λ i → AB i) a' b → PathP (λ i → AB i) a b
  test₁₅ p q = congruence

  -- Congruence dependent function
  test₁₆ : ∀ {ℓ} {A : Type ℓ} {C : A → Type ℓ} (f : (a : A) → C a) {a a' : A} →
    (p : a ≡ a') → PathP (λ i → C (p i)) (f a) (f a')
  test₁₆ f p = congruence

  -- Congruence Transitivity dependent function
  test₁₇ : ∀ {ℓ} {A : Type ℓ} {C : A → Type ℓ} (f : (a : A) → C a) {a b c : A} →
    (p : a ≡ b) → (q : b ≡ c) → PathP (λ i → C ((p ∙ q) i)) (f a) (f c)
  test₁₇ f p q = congruence

  -- Favor paths appearing in the type path
  test₁₈ : ∀ {ℓ} {A : Type ℓ} {C : A → Type ℓ} (f : (a : A) → C a) {a b : A} →
    (p q : a ≡ b) → PathP (λ i → C (p i)) (f a) (f b)
  test₁₈ f p q = congruence
  test₁₉ : ∀ {ℓ} {A : Type ℓ} {C : A → Type ℓ} (f : (a : A) → C a) {a b : A} →
    (p q : a ≡ b) → PathP (λ i → C (q i)) (f a) (f b)
  test₁₉ f p q = congruence

  -- Appearing two paths of same type in the type path
  test₂₀ : ∀ {ℓ} {A : Type ℓ} {C : A → A → Type ℓ} (f : (a : A) → (a' : A) → C a a') {a b : A} →
    (p q : a ≡ b) → PathP (λ i → C (p i) (q i)) (f a a) (f b b)
  test₂₀ f p q = congruence


-- * TODO

  -- -- Try different solutions when paths of same type appear in type path (p and refl)
  -- test₂₁ : ∀ {ℓ} {A : Type ℓ} {C : A → Type ℓ} (f : (a : A) → C a) {a : A} →
  --   (p : a ≡ a) → PathP (λ i → C (p i)) (f a) (f a)
  -- test₂₁ f p = congruence

  -- -- Looping in the type path
  -- test₂₂ : ∀ {ℓ} {A : Type ℓ} {C : A → Type ℓ} (f : (a : A) → C a) {a : A} →
  --   (p : a ≡ a) → (λ i → C ((p ∙ p) i))[ f a ≡ f a ]
  -- test₂₂ f p = congruence

-- -- Vectors
--   data Vec (A : Type₀) : ℕ → Type₀ where
--     []ₓ  : Vec A zero
--     _∷ₓ_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

--   _+++_ : ∀ {A} {n m} → Vec A n → Vec A m → Vec A (n + m)
--   []ₓ +++ r = r
--   (x ∷ₓ l) +++ r = x ∷ₓ (l +++ r)

--   +++-unit-r : ∀ {A} {n} → (v : Vec A n) → PathP (λ i → Vec A (+-zero n i)) (v +++ []ₓ) v
--   +++-unit-r []ₓ = refl
--   +++-unit-r {A} {suc n₁} (x ∷ₓ v) =
--     let IH = +++-unit-r v
--         -- q = quoteTerm (v +++ []ₓ)
--         -- l = x ∷ₓ (v +++ []ₓ)
--         -- r = x ∷ₓ v
--         -- ql = quoteTerm l
--         -- qr = quoteTerm r
--         goal = PathP (λ i → Vec A (suc (+-zero n₁ i))) (x ∷ₓ (v +++ []ₓ)) (x ∷ₓ v)
--         cc = computeCCHint IH goal
--         -- reprl = repr ql cc
--         -- reprr = repr qr cc
--         -- nql = runTC (normalise ql)
--         -- nqr = runTC (normalise qr)
--         nnn = (λ i → _∷ₓ_ x)
--         as = quoteTerm nnn
--         ann = con (quote _∷ₓ_) (hArg unknown ∷ hArg unknown ∷ vArg (var 1 []) ∷ [])
--         reprr = connect fuel ann ann cc
--         proofof = runTC (normalise (def (quote refl)
--           (hArg unknown ∷
--            hArg unknown ∷
--            hArg
--            (con (quote _∷ₓ_)
--             (hArg unknown ∷ hArg unknown ∷ vArg (var 1 []) ∷ []))
--            ∷ [])))
--         asd = runTCTerm (return proofof)
--         asdddd = runTC (do n ← quoteTC nnn
--                            inferType n)
--         asdasd = {!!}
--     in hcongr-ideal nnn IH

-- --   +++-assoc : ∀ {A} {m n o} → (v : Vec A m) → (w : Vec A n) → (q : Vec A o) →
-- --                 PathP (λ i → Vec A (+-assoc m n o i)) (v +++ (w +++ q)) ((v +++ w) +++ q)
-- --   +++-assoc []ₓ w q = refl
-- --   +++-assoc (x ∷ₓ v) w q = hcongr-ideal (λ i a → x ∷ₓ a) (+++-assoc v w q)
