module Quotient.Algebra where

private
  open import Relation.Binary.PropositionalEquality as P using (proof-irrelevance; _≡_)
  open import Data.Nat using (ℕ; zero; suc)

  open import Data.Vec.N-ary

  N-ary-equality : ∀ {a} {A : Set a} (n : ℕ) → (f g : N-ary n A A) → Set (N-ary-level a a n)
  N-ary-equality {A = A} n f g = Eq {A = A} n (_≡_ {A = A}) f g

  private
    module N-ary-equality-Ex where
      open import Data.Nat

      ex₀ : N-ary-equality {A = ℕ} 0 2 2
      ex₀ = P.refl

      ex₁ : N-ary-equality {A = ℕ} 1 suc (λ ξ → ξ + 1)
      ex₁ zero = P.refl
      ex₁ (suc n) = P.cong suc (ex₁ n)

      open import Function using (flip)

      ex₂ : N-ary-equality {A = ℕ} 2 _+_ (flip _+_)
      ex₂ = +-comm
        where
        open import Algebra
        import Data.Nat.Properties
        open CommutativeSemiring Data.Nat.Properties.commutativeSemiring

  N-ary-irrelevance : ∀ {a} {A : Set a} (n : ℕ) → Set (N-ary-level a a n)
  N-ary-irrelevance {A = A} n = ∀ {f g} (p q : N-ary-equality {A = A} n f g) → p ≡ q

  postulate
    extensional-irrelevance : ∀ {a} {A : Set a} (n : ℕ) → N-ary-irrelevance {a} {A} n

  private
    module N-ary-irrelevance-Ex where

      ex₀ : N-ary-irrelevance {A = ℕ} 0
      ex₀ = proof-irrelevance

      ex₁ : N-ary-irrelevance {A = ℕ} 1
      ex₁ = extensional-irrelevance 1

open import Quotient
open import Algebra
open import Relation.Binary -- using (Setoid)
open import Algebra.Structures

open import Data.Product
open import Function
open import Algebra.FunctionProperties using (Op₁; Op₂)

import Algebra.FunctionProperties as FunProp

Sound₁ : ∀ {c ℓ} (S : Setoid c ℓ) → let open Setoid S in Op₁ Carrier → Set _
Sound₁ S f = let open Setoid S in f Preserves _≈_ ⟶ _≈_

quot₁ : ∀ {c ℓ} {S : Setoid c ℓ} → let open Setoid S in
        {f : Op₁ Carrier} → (∙-sound : Sound₁ S f) → Op₁ (Quotient S)
quot₁ {S = S} {f} prf = rec _ (λ x → [ f x ]) (λ x≈x′ → [ prf x≈x′ ]-cong)
  where
  open Setoid S

Sound₂ : ∀ {c ℓ} (S : Setoid c ℓ) → let open Setoid S in Op₂ Carrier → Set _
Sound₂ S ∙ = let open Setoid S in ∙ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_

quot₂ : ∀ {c ℓ} {S : Setoid c ℓ} → let open Setoid S in
        {∙ : Op₂ Carrier} → (∙-sound : Sound₂ S ∙) → Op₂ (Quotient S)
quot₂ {S = S} {_∙_} prf = rec S (λ x → rec _ (λ y → [ x ∙ y ])
                                (λ y≈y′ → [ refl ⟨ prf ⟩ y≈y′ ]-cong))
                                -- (λ {x} {x′} x≈x′ → P.cong (λ ξ → rec S ξ _)
                                -- (extensionality (λ _ → [ x≈x′ ⟨ prf ⟩ refl ]-cong)))
                                (λ x≈x′ → extensionality (elim _ _ (λ _ → [ (x≈x′ ⟨ prf ⟩ refl) ]-cong)
                                (λ _ → proof-irrelevance _ _)))
  where
  open Setoid S
  postulate extensionality : P.Extensionality _ _


quot-assoc : ∀ {c ℓ} {S : Setoid c ℓ} →
             let
               open Setoid S
               module F₀ = FunProp _≈_
               module F = FunProp (_≡_ {A = Quotient S})
             in
             {∙ : Op₂ Carrier} → (∙-sound : Sound₂ S ∙) →
             F₀.Associative ∙ → F.Associative (quot₂ ∙-sound)
quot-assoc {S = S} sound prf
  = elim S _
         (λ x → elim S _ (λ y → elim S _ (λ z → [ prf x y z ]-cong)
         (λ _ → extensional-irrelevance 0 _ _))
         (λ _ → extensional-irrelevance 1 _ _))
         (λ _ → extensional-irrelevance 2 _ _)

quot-comm : ∀ {c ℓ} {S : Setoid c ℓ} →
            let
              open Setoid S
              module F₀ = FunProp _≈_
              module F = FunProp (_≡_ {A = Quotient S})
            in
            {∙ : Op₂ Carrier} → (∙-sound : Sound₂ S ∙) →
            F₀.Commutative ∙ → F.Commutative (quot₂ ∙-sound)
quot-comm {S = S} sound prf
  = elim S _
         (λ x → elim S _ (λ y → [ prf x y ]-cong)
         (λ _ → extensional-irrelevance 0 _ _))
         (λ _ → extensional-irrelevance 1 _ _)

quot-leftIdentity : ∀ {c ℓ} {S : Setoid c ℓ} →
                    let
                      open Setoid S
                      module F₀ = FunProp _≈_
                      module F = FunProp (_≡_ {A = Quotient S})
                    in
                    {∙ : Op₂ Carrier} → (∙-sound : Sound₂ S ∙) →
                    {ε : Carrier} →
                    F₀.LeftIdentity ε ∙ → F.LeftIdentity [ ε ] (quot₂ ∙-sound)
quot-leftIdentity {S = S} {∙} sound {ε} prf
  = elim S _
         (λ x → [ prf x ]-cong)
         (λ _ → extensional-irrelevance 0 _ _)

quot-rightIdentity : ∀ {c ℓ} {S : Setoid c ℓ} →
                     let
                       open Setoid S
                       module F₀ = FunProp _≈_
                       module F = FunProp (_≡_ {A = Quotient S})
                     in
                     {∙ : Op₂ Carrier} → (∙-sound : Sound₂ S ∙) →
                     {ε : Carrier} →
                     F₀.RightIdentity ε ∙ → F.RightIdentity [ ε ] (quot₂ ∙-sound)
quot-rightIdentity {S = S} {∙} sound {ε} prf
  = elim S _
         (λ x → [ prf x ]-cong)
         (λ _ → extensional-irrelevance 0 _ _)

quot-identity : ∀ {c ℓ} {S : Setoid c ℓ} →
                let
                  open Setoid S
                  module F₀ = FunProp _≈_
                  module F = FunProp (_≡_ {A = Quotient S})
                in
                {∙ : Op₂ Carrier} → (∙-sound : Sound₂ S ∙) →
                {ε : Carrier} →
                F₀.Identity ε ∙ → F.Identity [ ε ] (quot₂ ∙-sound)
quot-identity sound (prfˡ , prfʳ)
  = quot-leftIdentity sound prfˡ , quot-rightIdentity sound prfʳ

quot-leftInverse : ∀ {c ℓ} {S : Setoid c ℓ} →
                   let
                     open Setoid S
                     module F₀ = FunProp _≈_
                     module F = FunProp (_≡_ {A = Quotient S})
                   in
                   {⁻¹ : Op₁ Carrier} → (⁻¹-sound : Sound₁ S ⁻¹) →
                   {∙ : Op₂ Carrier} → (∙-sound : Sound₂ S ∙) →
                   {ε : Carrier} →
                   F₀.LeftInverse ε ⁻¹ ∙ → F.LeftInverse [ ε ] (quot₁ ⁻¹-sound) (quot₂ ∙-sound)
quot-leftInverse {S = S} {_⁻¹} ⁻¹-sound {_∙_} ∙-sound {ε} prf
  = elim S _
         (λ x → [ prf x ]-cong)
         (λ _ → extensional-irrelevance 0 _ _)

quot-rightInverse : ∀ {c ℓ} {S : Setoid c ℓ} →
                   let
                     open Setoid S
                     module F₀ = FunProp _≈_
                     module F = FunProp (_≡_ {A = Quotient S})
                   in
                   {⁻¹ : Op₁ Carrier} → (⁻¹-sound : Sound₁ S ⁻¹) →
                   {∙ : Op₂ Carrier} → (∙-sound : Sound₂ S ∙) →
                   {ε : Carrier} →
                   F₀.RightInverse ε ⁻¹ ∙ → F.RightInverse [ ε ] (quot₁ ⁻¹-sound) (quot₂ ∙-sound)
quot-rightInverse {S = S} {_⁻¹} ⁻¹-sound {_∙_} ∙-sound {ε} prf
  = elim S _
         (λ x → [ prf x ]-cong)
         (λ _ → extensional-irrelevance 0 _ _)

quot-inverse : ∀ {c ℓ} {S : Setoid c ℓ} →
               let
                 open Setoid S
                 module F₀ = FunProp _≈_
                 module F = FunProp (_≡_ {A = Quotient S})
               in
               {⁻¹ : Op₁ Carrier} → (⁻¹-sound : Sound₁ S ⁻¹) →
               {∙ : Op₂ Carrier} → (∙-sound : Sound₂ S ∙) →
               {ε : Carrier} →
               F₀.Inverse ε ⁻¹ ∙ → F.Inverse [ ε ] (quot₁ ⁻¹-sound) (quot₂ ∙-sound)
quot-inverse ⁻¹-sound  ∙-sound (prfˡ , prfʳ)
  = quot-leftInverse ⁻¹-sound ∙-sound prfˡ , quot-rightInverse ⁻¹-sound ∙-sound prfʳ

quot-isSemigroup : ∀ {c ℓ} → (Σ : Semigroup c ℓ) → let open Semigroup Σ in
                   IsSemigroup (_≡_ {A = Quotient setoid}) (quot₂ ∙-cong)
quot-isSemigroup Σ = record
  { isEquivalence = Relation.Binary.Setoid.isEquivalence (P.setoid _)
  ; assoc = quot-assoc ∙-cong assoc
  ; ∙-cong = P.cong₂ _
  }
  where
  open Semigroup Σ

quot-isMonoid : ∀ {c ℓ} → (Σ : Monoid c ℓ) → let open Monoid Σ in
                IsMonoid (_≡_ {A = Quotient setoid}) (quot₂ ∙-cong) [ ε ]
quot-isMonoid Σ = record
  { isSemigroup = quot-isSemigroup semigroup
  ; identity = quot-identity ∙-cong identity
  }
  where
  open Monoid Σ

quot-isGroup : ∀ {c ℓ} → (Σ : Group c ℓ) → let open Group Σ in
               IsGroup (_≡_ {A = Quotient setoid}) (quot₂ ∙-cong) [ ε ] (quot₁ ⁻¹-cong)
quot-isGroup Σ = record
  { isMonoid = quot-isMonoid monoid
  ; inverse = quot-inverse ⁻¹-cong ∙-cong inverse
  ; ⁻¹-cong = P.cong _
  }
  where
  open Group Σ

quot-isAbelianGroup : ∀ {c ℓ} → (Σ : AbelianGroup c ℓ) → let open AbelianGroup Σ in
                      IsAbelianGroup (_≡_ {A = Quotient setoid}) (quot₂ ∙-cong) [ ε ] (quot₁ ⁻¹-cong)
quot-isAbelianGroup Σ = record
  { isGroup = quot-isGroup group
  ; comm = quot-comm ∙-cong comm
  }
  where
  open AbelianGroup Σ

quot-isRing : ∀ {c ℓ} → (Σ : Ring c ℓ) → let open Ring Σ in
              IsRing (_≡_ {A = Quotient setoid}) (quot₂ +-cong) (quot₂ *-cong) (quot₁ -‿cong) [ 0# ] [ 1# ]
quot-isRing Σ = record
  { +-isAbelianGroup = quot-isAbelianGroup +-abelianGroup
  ; *-isMonoid = quot-isMonoid *-monoid
  ; distrib = {!!}
  }
  where
  open Ring Σ

-- quot-semigroup : ∀ {c ℓ} → (Σ : Semigroup c ℓ) →
--                  Semigroup (ℓ ⊔ c) (ℓ ⊔ c)
-- quot-semigroup Σ = record
--   { Carrier = Quotient setoid
--   ; _≈_ = _≡_
--   ; _∙_ = quot₂ ∙₀ ∙-cong
--   ; isSemigroup = quot-isSemigroup Σ
--   }
--   where
--   open Semigroup Σ renaming (_∙_ to ∙₀)
