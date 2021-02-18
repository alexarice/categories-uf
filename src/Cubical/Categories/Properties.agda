{-# OPTIONS --safe --cubical --postfix-projections #-}

module Cubical.Categories.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.PresheavesStrict

private
  variable
    ℓ ℓ' : Level



strictify : (C : Precategory ℓ ℓ) → ⦃ _ : isCategory C ⦄ → (P : Precategory ℓ ℓ → Type ℓ') → P (PSImage C) → P C
strictify C P p = transport (sym (cong P (eq C))) p

module _ {ℓ} (C : Precategory ℓ ℓ) where

  open Precategory C

  Id-Unique : Type ℓ
  Id-Unique = ∀ {x} {f : C [ x , x ]} → (∀ {y} (g : C [ y , x ]) → g ⋆ f ≡ g) → f ≡ id x

  Id-Comm : Type ℓ
  Id-Comm = ∀ {a b} {f : C [ a , b ]} → (f ⋆ id b ≡ id a ⋆ f)

  Id-Comm-Sym : Type ℓ
  Id-Comm-Sym = ∀ {a b} {f : C [ a , b ]} → (id a ⋆ f ≡ f ⋆ id b)

  Assoc² : Type ℓ
  Assoc² = ∀ {v w x y z}
             {f : C [ v , w ]}
             {g : C [ w , x ]}
             {h : C [ x , y ]}
             {j : C [ y , z ]}
           → ((f ⋆ g) ⋆ h) ⋆ j ≡ f ⋆ (g ⋆ (h ⋆ j))

  Assoc²' : Type ℓ
  Assoc²' = ∀ {v w x y z}
              {f : C [ v , w ]}
              {g : C [ w , x ]}
              {h : C [ x , y ]}
              {j : C [ y , z ]}
            → (f ⋆ (g ⋆ h)) ⋆ j ≡ f ⋆ (g ⋆ (h ⋆ j))

  Pullʳ : Type ℓ
  Pullʳ = ∀ {w x y z}
            {f : C [ w , x ]}
            {a : C [ x , y ]}
            {b : C [ y , z ]}
            {c : C [ x , z ]}
          → c ≡ a ⋆ b
          → f ⋆ c ≡ (f ⋆ a) ⋆ b

  Pullˡ : Type ℓ
  Pullˡ = ∀ {w x y z}
            {a : C [ w , x ]}
            {b : C [ x , y ]}
            {f : C [ y , z ]}
            {c : C [ w , y ]}
          → c ≡ a ⋆ b
          → c ⋆ f ≡ a ⋆ (b ⋆ f)

  Elimʳ : Type ℓ
  Elimʳ = ∀ {x y} {f : C [ x , y ]} {a : C [ y , y ]} → a ≡ id y → f ⋆ a ≡ f

  Introʳ : Type ℓ
  Introʳ = ∀ {x y} {f : C [ x , y ]} {a : C [ y , y ]} → a ≡ id y → f ≡ f ⋆ a

  Elimˡ : Type ℓ
  Elimˡ = ∀ {x y} {f : C [ x , y ]} {a : C [ x , x ]} → a ≡ id x → a ⋆ f ≡ f

  Introˡ : Type ℓ
  Introˡ = ∀ {x y} {f : C [ x , y ]} {a : C [ x , x ]} → a ≡ id x → f ≡ a ⋆ f

module _ {ℓ} (C : Precategory ℓ ℓ) ⦃ _ : isCategory C ⦄ where

  open import Cubical.Categories.Reasoning C

  id-unique : Id-Unique C
  id-unique = strictify C Id-Unique
    λ p → p (idp _)

  id-comm : Id-Comm C
  id-comm = strictify C Id-Comm refl

  id-comm-sym : Id-Comm-Sym C
  id-comm-sym = strictify C Id-Comm-Sym refl

  assoc² : Assoc² C
  assoc² = strictify C Assoc² refl

  assoc²' : Assoc²' C
  assoc²' = strictify C Assoc²' refl

  pullʳ : Pullʳ C
  pullʳ = strictify C Pullʳ
    λ {w x y z f a b c} p → begin
      f ;⌊ c ⌋ ≡⌊ p ⌋
      f ; a ; b ∎′

  elimʳ : Elimʳ C
  elimʳ = strictify C Elimʳ λ {x y f} p i → f ; p i

  introʳ : Introʳ C
  introʳ = strictify C Introʳ λ {x y f} p i → f ; p (~ i)

  elimˡ : Elimˡ C
  elimˡ = strictify C Elimˡ λ {x y f} p i → p i ; f

  introˡ : Introˡ C
  introˡ = strictify C Introˡ λ {x y f} p i → p (~ i) ; f
