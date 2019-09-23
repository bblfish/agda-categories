{-# OPTIONS --without-K --safe #-}
open import Level

open import Categories.Category

module Categories.Category.Construction.Path {o ℓ e : Level} (C : Category o ℓ e) where

open import Function using (flip)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Construct.Closure.Transitive

open Category C

-- Defining the Path Category
∘-tc : {A B : Obj} → A [ _⇒_ ]⁺ B → A ⇒ B
∘-tc [ f ]            = f
∘-tc (_ ∼⁺⟨ f⁺ ⟩ f⁺′) = ∘-tc f⁺′ ∘ ∘-tc f⁺

infix 4 _≈⁺_
_≈⁺_ : {A B : Obj} → Rel (A [ _⇒_ ]⁺ B) e
f⁺ ≈⁺ g⁺ = ∘-tc f⁺ ≈ ∘-tc g⁺

Path : Category o (o ⊔ ℓ) e
Path = record
  { Obj       = Obj
  ; _⇒_       = λ A B → A [ _⇒_ ]⁺ B
  ; _≈_       = _≈⁺_
  ; id        = [ id ]
  ; _∘_       = flip (_ ∼⁺⟨_⟩_)
  ; assoc     = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; equiv     = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  ; ∘-resp-≈  = ∘-resp-≈
  }
  where open HomReasoning
