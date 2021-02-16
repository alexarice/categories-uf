{-# OPTIONS --safe --cubical --postfix-projections #-}

open import Cubical.Categories.Category

module Cubical.Categories.Reasoning {ℓ} (C : Precategory ℓ ℓ) ⦃ c-cat : isCategory C ⦄ where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.PresheavesStrict

open Precategory

C' = PSImage C

infixr 7 _⋆p_

_⋆p_ = _⋆_ C'
idp = id C'

record Expr (a b c d : C .ob) : Type ℓ where
  field
    before : C' [ a , b ]
    focus : C' [ b , c ]
    after : C' [ c , d ]

  eval : C' [ a , d ]
  eval = before ⋆p focus ⋆p after

open Expr

_∼_ : ∀ {a b c d} → (x : C' [ a , d ]) → (y : Expr a b c d) → Type ℓ
x ∼ y = x ≡ eval y

infix 6 _∘⌊_⌋∘_ ⌊_⌋ _∘⌊_⌋ ⌊_⌋∘_ _∘⌊⌋∘_ ⌊⌋ _∘⌊⌋ ⌊⌋∘_
infix 3 _∎′

_∘⌊_⌋∘_ : ∀ {a b c d} → C' [ a , b ] → C' [ b , c ] → C' [ c , d ] → Expr a b c d
(g ∘⌊ f ⌋∘ h) .before = g
(g ∘⌊ f ⌋∘ h) .focus = f
(g ∘⌊ f ⌋∘ h) .after = h

⌊_⌋ : ∀ {a b} → C' [ a , b ] → Expr a a b b
⌊ f ⌋ = idp _ ∘⌊ f ⌋∘ idp _

_∘⌊_⌋ : ∀ {a b c} → C' [ a , b ] → C' [ b , c ] → Expr a b c c
g ∘⌊ f ⌋ = g ∘⌊ f ⌋∘ idp _

⌊_⌋∘_ : ∀ {a b c} → C' [ a , b ] → C' [ b , c ] → Expr a a b c
⌊ f ⌋∘ g = idp _ ∘⌊ f ⌋∘ g

⌊⌋ : ∀ {a} → Expr a a a a
⌊⌋ = ⌊ idp _ ⌋

_∘⌊⌋ : ∀ {a b} → C' [ a , b ] → Expr a b b b
g ∘⌊⌋ = g ∘⌊ idp _ ⌋

⌊⌋∘_ : ∀ {a b} → C' [ a , b ] → Expr a a a b
⌊⌋∘ g = ⌊ idp _ ⌋∘ g

_∘⌊⌋∘_ : ∀ {a b c} → C' [ a , b ] → C' [ b , c ] → Expr a b b c
g ∘⌊⌋∘ h = g ∘⌊ idp _ ⌋∘ h

data _IsRelatedTo_ {a b c d} (x : C' [ a , d ]) (y : Expr a b c d) : Type ℓ where
  relTo : x ∼ y → x IsRelatedTo y

infix 1 begin_
begin_ : ∀ {a b c d} {x : C' [ a , d ]} {y : Expr a b c d} → x IsRelatedTo y → x ≡ eval y
begin relTo p = p

step-≈ : ∀ {a b c d} (x : C' [ a , d ]) {y : C' [ a , d ]} {z : Expr a b c d} → y IsRelatedTo z → x ≡ y → x IsRelatedTo z
step-≈ _ (relTo y∼z) x∼y = relTo (x∼y ∙ y∼z)

step-≈˘ : ∀ {a b c d} (x : C' [ a , d ]) {y : C' [ a , d ]} {z : Expr a b c d} → y IsRelatedTo z → y ≡ x → x IsRelatedTo z
step-≈˘ _ p q = step-≈ _ p (sym q)

_∎′ : ∀ {a b} → (x : C' [ a , b ]) → x IsRelatedTo ⌊ x ⌋
x ∎′ = relTo refl

replaceFocus : ∀ {a b c d} (x : Expr a b c d) → (y : C' [ b , c ]) → Expr a b c d
replaceFocus x y .before = x .before
replaceFocus x y .focus = y
replaceFocus x y .after = x .after

congExpr : ∀ {a b c d} → (x : Expr a b c d) → {y : C' [ b , c ]} → focus x ≡ y → eval x ∼ (replaceFocus x y)
congExpr x p = cong (λ a → before x ⋆p a ⋆p after x) p

step-cong-≈ : ∀ {a b c d} (x : Expr a b c d) {y : C' [ b , c ]} {z : Expr a b c d} → (eval (replaceFocus x y)) IsRelatedTo z → focus x ≡ y → eval x IsRelatedTo z
step-cong-≈ x (relTo p) q = relTo (congExpr x q ∙ p)

step-cong-≈˘ : ∀ {a b c d} (x : Expr a b c d) {y : C' [ b , c ]} {z : Expr a b c d} → (eval (replaceFocus x y)) IsRelatedTo z → y ≡ focus x → eval x IsRelatedTo z
step-cong-≈˘ x (relTo p) q = relTo (congExpr x (sym q) ∙ p)

infixr 2 step-≈
syntax step-≈ x rest p = x ≈⟨ p ⟩ rest

infixr 2 step-≈˘
syntax step-≈˘ x rest p = x ≈⟨ p ⟩ rest

infixr 2 step-cong-≈
syntax step-cong-≈ x rest p = x ≈⌊ p ⌋ rest

infixr 2 step-cong-≈˘
syntax step-cong-≈˘ x rest p = x ≈˘⌊ p ⌋ rest
