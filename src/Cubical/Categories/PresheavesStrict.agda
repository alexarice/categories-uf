{-# OPTIONS --cubical --no-import-sorts --postfix-projections --safe #-}

module Cubical.Categories.PresheavesStrict where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Foundations.Path

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Sets

module _ {ℓ ℓ' : Level} (C : Precategory ℓ ℓ') where

  open Precategory
  open Functor

  Presheaf : Type (ℓ-max (ℓ-suc ℓ) ℓ')
  Presheaf = Functor (C ^op) (SET ℓ)

  record StrictNatTrans (F G : Presheaf) : Type (ℓ-max ℓ ℓ') where
    field
     SN-ob : (∀ (x : C .ob) → F .F-ob x .fst → G .F-ob x .fst)
     SN-hom : (∀ {x y : C .ob}
            → (f : C [ x , y ])
            → (a : F .F-ob y .fst)
            → (b : F .F-ob x .fst)
            → F .F-hom f a ≡ b
            → G .F-hom f (SN-ob y a) ≡ SN-ob x b)

  open StrictNatTrans


  makeSNTPathEquivProof : {F G : Presheaf} → (α β : StrictNatTrans F G) → isEquiv (λ (p : α ≡ β) → cong SN-ob p)
  makeSNTPathEquivProof {F} {G} α β .equiv-proof γ = ctr , isCtr
    where
      B : (∀ x → F .F-ob x .fst → G .F-ob x .fst) → Type (ℓ-max ℓ ℓ')
      B o = {x y : C .ob} (f : C [ x , y ]) (a : F .F-ob y .fst) (b : F .F-ob x .fst) →
          F .F-hom f a ≡ b → G .F-hom f (o y a) ≡ o x b

      BProp : ∀ o → isProp (B o)
      BProp o = isPropImplicitΠ λ x → isPropImplicitΠ λ y → isPropΠ4 (λ a b c d → G .F-ob x .snd (G .F-hom a (o y b)) (o x c))

      ctrP : α ≡ β
      ctrP i .SN-ob = γ i
      ctrP i .SN-hom = isProp→PathP {B = λ i → B (γ i)} (λ j → BProp (γ j)) (α .SN-hom) (β .SN-hom) i
      ctr : fiber (λ z → cong SN-ob z) γ
      ctr = ctrP , refl

      isCtr : ∀ z → ctr ≡ z
      isCtr (z , p) = ΣPathP (ctrP≡ , cong (λ x → sym (snd x)) fzsingl) where
        fzsingl : Path (singl γ) (γ , refl) (cong SN-ob z , sym p)
        fzsingl = isContrSingl γ .snd (cong SN-ob z , sym p)
        ctrSnd : SquareP (λ i j → B (fzsingl i .fst j)) (cong SN-hom ctrP) (cong SN-hom z) refl refl
        ctrSnd = isProp→SquareP (λ _ _ → BProp _) _ _ _ _
        ctrP≡ : ctrP ≡ z
        ctrP≡ i j .SN-ob = fzsingl i .fst j
        ctrP≡ i j .SN-hom = ctrSnd i j

  makeSNTPathEquiv : ∀ {F G} → (α β : StrictNatTrans F G) → (α .SN-ob ≡ β .SN-ob) ≃ (α ≡ β)
  makeSNTPathEquiv α β = invEquiv ((cong SN-ob) , (makeSNTPathEquivProof α β))

  makeSNTPath : ∀ {F G} → (α β : StrictNatTrans F G) → (α .SN-ob ≡ β .SN-ob) → (α ≡ β)
  makeSNTPath α β = equivFun (makeSNTPathEquiv α β)

  idSNT : (F : Presheaf) → StrictNatTrans F F
  idSNT F .SN-ob c x = x
  idSNT F .SN-hom f a b p = p

  seqSNT : {F G H : Presheaf} → StrictNatTrans F G → StrictNatTrans G H → StrictNatTrans F H
  seqSNT α β .SN-ob c x = SN-ob β c (SN-ob α c x)
  seqSNT {F} {G} {H} α β .SN-hom f a b p = SN-hom β f (SN-ob α _ a) (SN-ob α _ b) (SN-hom α f a b p)

  PreShvStrict : Precategory (ℓ-max (ℓ-suc ℓ) ℓ') (ℓ-max ℓ ℓ')
  PreShvStrict .ob = Presheaf
  PreShvStrict .Hom[_,_] = StrictNatTrans
  PreShvStrict .id = idSNT
  PreShvStrict ._⋆_ = seqSNT
  PreShvStrict .⋆IdL α = refl
  PreShvStrict .⋆IdR α = refl
  PreShvStrict .⋆Assoc α β γ = refl

private
  variable
    ℓ : Level

module _ (C : Precategory ℓ ℓ) ⦃ C-cat : isCategory C ⦄ where
  open Functor
  open Precategory C
  open StrictNatTrans

  yo : ob → Presheaf C
  yo x .F-ob y .fst = C [ y , x ]
  yo x .F-ob y .snd = C-cat .isSetHom
  yo x .F-hom f g = f ⋆⟨ C ⟩ g
  yo x .F-id i f = ⋆IdL f i
  yo x .F-seq f g i h = ⋆Assoc g f h i

  YO : Functor C (PreShvStrict C)
  YO .F-ob = yo
  YO .F-hom f .SN-ob z g = g ⋆⟨ C ⟩ f
  YO .F-hom f .SN-hom g a b p = (sym (⋆Assoc g a f)) ∙ cong (λ - → seq' C - f) p
  YO .F-id {x} = makeSNTPath C _ _ λ i c y → ⋆IdR y i
  YO .F-seq f g = makeSNTPath C _ _ λ i c y → ⋆Assoc y f g (~ i)

  module _ {x} (F : Presheaf C) where
    yo-yo-yo : StrictNatTrans C (yo x) F → F .F-ob x .fst
    yo-yo-yo α = α .SN-ob _ (id _)

    no-no-no : F .F-ob x .fst → StrictNatTrans C (yo x) F
    no-no-no a .SN-ob y f = F .F-hom f a
    no-no-no a .SN-hom f b c q =
      F .F-hom f (F .F-hom b a) ≡[ i ]⟨ F .F-seq b f (~ i) a ⟩
      F .F-hom (b ⋆⟨ C ^op ⟩ f) a ≡[ i ]⟨ F .F-hom (q i) a ⟩
      F .F-hom c a ∎

    open Iso

    yoIso : Iso (StrictNatTrans C (yo x) F) (F .F-ob x .fst)
    yoIso .fun = yo-yo-yo
    yoIso .inv = no-no-no
    yoIso .rightInv b i = F .F-id i b
    yoIso .leftInv a = makeSNTPath C _ _ λ i y f → rem y f i
      where
        rem : (y : ob) (f : yo x .F-ob y .fst) →
                no-no-no (yo-yo-yo a) .SN-ob y f ≡ a .SN-ob y f
        rem y f = a .SN-hom f (id x) f (⋆IdR f)

    yoEquiv : StrictNatTrans C (yo x) F ≃ F .F-ob x .fst
    yoEquiv = isoToEquiv yoIso


  PSImage : Precategory ℓ ℓ
  PSImage .Precategory.ob = ob
  PSImage .Precategory.Hom[_,_] x y = StrictNatTrans C (yo x) (yo y)
  PSImage .Precategory.id x = idSNT C (yo x)
  PSImage .Precategory._⋆_ = seqSNT C
  PSImage .Precategory.⋆IdL f = refl
  PSImage .Precategory.⋆IdR f = refl
  PSImage .Precategory.⋆Assoc f g h = refl

  is-cat : isCategory PSImage
  is-cat .isSetHom α β p q = isoInvInjective (equivToIso (makeSNTPathEquiv C α β)) p q
                                             (isSetΠ2 (λ x y → isSetHom C-cat) (α .SN-ob) (β .SN-ob) _ _)

  YO-Res : Functor C (PSImage)
  YO-Res .F-ob x = x
  YO-Res .F-hom f .SN-ob z g = g ⋆⟨ C ⟩ f
  YO-Res .F-hom f .SN-hom g a b p =
    g ⋆ (a ⋆ f) ≡[ i ]⟨ ⋆Assoc g a f (~ i) ⟩
    (g ⋆ a) ⋆ f ≡[ i ]⟨ p i ⋆ f ⟩
    b ⋆ f ∎
  YO-Res .F-id {x} = makeSNTPath C _ _ λ i c y → ⋆IdR y i
  YO-Res .F-seq f g = makeSNTPath C _ _ λ i c y → ⋆Assoc y f g (~ i)

  NO-Res : Functor PSImage C
  NO-Res .F-ob x = x
  NO-Res .F-hom {x} {y} f = yo-yo-yo (yo y) f
  NO-Res .F-id = refl
  NO-Res .F-seq {x} {y} f g = sym (g .SN-hom (yo-yo-yo (yo y) f) (id y) (yo-yo-yo (yo y) f) (⋆IdR (yo-yo-yo (yo y) f)))

  YO-Res-full : isFull YO-Res
  YO-Res-full x y F[f] = ∣ yo-yo-yo (yo y) F[f] , yoIso {x} (yo y) .Iso.leftInv F[f] ∣

  isFaithfulYO : isFaithful YO
  isFaithfulYO x y f g p i =
    hcomp
      (λ j → λ{ (i = i0) → ⋆IdL f j; (i = i1) → ⋆IdL g j})
      (yo-yo-yo _ (p i))

  YO-Res-equiv : ∀ (x y : ob) → C [ x , y ] ≃ StrictNatTrans C (yo x) (yo y)
  YO-Res-equiv x y = invEquiv (yoEquiv {x} (yo y))

  eq-hom : ∀ x y → C [ x , y ] ≡ PSImage [ x , y ]
  eq-hom x y i = ua (YO-Res-equiv x y) i

  eq-id : ∀ x → PathP (λ i → eq-hom x x i) (id x) (idSNT C (yo x))
  eq-id x i = toPathP {A = λ i → ua (YO-Res-equiv x x) i} γ i
    where
      γ : transport (ua (YO-Res-equiv x x)) (id x) ≡ idSNT C (yo x)
      γ = transport (ua (YO-Res-equiv x x)) (id x) ≡⟨ uaβ (YO-Res-equiv x x) (id x) ⟩
          no-no-no (yo x) (id x) ≡⟨ YO-Res .F-id {x} ⟩
          idSNT C (yo x) ∎

  eq-comp : ∀ x y z → PathP (λ i →
                                eq-hom x y i →
                                eq-hom y z i → eq-hom x z i) (_⋆_) (seqSNT C)
  eq-comp x y z i = ua→ {e = YO-Res-equiv x y} {B = λ i → ua (YO-Res-equiv y z) i → ua (YO-Res-equiv x z) i} {f₀ = _⋆_ } {f₁ = seqSNT C} (λ f → ua→ λ g → toPathP (α f g)) i
    where
      α : ∀ f g → transport (λ _ → PSImage [ x , z ]) (no-no-no (yo z) (f ⋆ g))
          ≡ seqSNT C (no-no-no (yo y) f) (no-no-no (yo z) g)
      α f g =
        transport (λ _ → PSImage [ x , z ]) (no-no-no (yo z) (f ⋆ g)) ≡⟨ transportRefl _ ⟩
        no-no-no (yo z) (f ⋆ g) ≡⟨ YO-Res .F-seq f g ⟩
        seqSNT C (no-no-no (yo y) f) (no-no-no (yo z) g) ∎

  eq : C ≡ PSImage
  eq i .Precategory.ob = ob
  eq i .Precategory.Hom[_,_] x y = eq-hom x y i
  eq i .Precategory.id x = eq-id x i
  eq i .Precategory._⋆_ {x} {y} {z} = eq-comp x y z i
  eq i .Precategory.⋆IdL {x} {y} = γ i
    where
      γ : PathP (λ i → (f : eq-hom x y i) → eq-comp x x y i (eq-id x i) f ≡ f) (⋆IdL) λ f → refl
      γ = toPathP (isPropΠ (λ a → isSetHom is-cat _ _) _ _)
  eq i .Precategory.⋆IdR {x} {y} = γ i
    where
      γ : PathP (λ i → (f : eq-hom x y i) → eq-comp x y y i f (eq-id y i) ≡ f) (⋆IdR) λ f → refl
      γ = toPathP (isPropΠ (λ a → isSetHom is-cat _ _) _ _)
  eq i .Precategory.⋆Assoc {w} {x} {y} {z} = γ i
    where
      γ : PathP (λ i → (f : eq-hom w x i) → (g : eq-hom x y i) → (h : eq-hom y z i) → eq-comp w y z i (eq-comp w x y i f g) h ≡ eq-comp w x z i f (eq-comp x y z i g h)) ⋆Assoc λ f g h → refl
      γ = toPathP (isPropΠ3 (λ a b c → isSetHom is-cat _ _) _ _)
