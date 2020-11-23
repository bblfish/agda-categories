module Categories.Web.RDF where

open import Categories.Category.Finite.Fin.Instance.HGraph

open import Categories.Category.Instance.Globe
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Category.Finite.Fin
open import Data.Fin.Base using (Fin; raise; inject₁)
open import Data.Fin.Patterns
open import Categories.Category
open import Level
open import Relation.Binary.PropositionalEquality.Core using (_≡_ ; refl)
open import Data.Nat.Base -- using (ℕ)


-- perhaps place these in the Δₙ cat
-- Is there a way to avoid having to declare the module here?
Δ₃ : Category 0ℓ 0ℓ 0ℓ
Δ₃ =  Δₙ 3
module Δ₃ = Category Δ₃

Δ₄ : Category 0ℓ 0ℓ 0ℓ
Δ₄ = Δₙ 4
module Δ₄ = Category Δ₄

{-
Build functors
  G : Δ₂ → Δ₃ ­
  H : Δ₃ ­→ Δ₄

For each Δₙ we will need a Δₙ-Inst category
of functors to Set.
-}

-- This creates a Functor for each Δₙ to its successor
FΔₙ++ : (n : ℕ) → Functor (Δₙ n) (Δₙ (ℕ.suc n))
FΔₙ++ n = record
   { F₀ = λ o → o   -- the objects are the same two elements of Fin 2
   ; F₁ = Finj
   ; identity = identity
   ; homomorphism = homomorphism
   ; F-resp-≈ = F-resp
   } where

   -- The arrows are mapped injectively into the successor
   -- so for Δ₂ arrow 0F points from a node to the start of the arrow
   -- and 1F to the end. (we are working in the opposite category)
   -- They will then map to the same arrow in Δ₃
   Finj : ∀ {A} {B} → (Δₙ n) [ A , B ] → (Δₙ (ℕ.suc n)) [ A , B ]
   Finj {0F} {0F} f = f
   Finj {0F} {1F} f = inject₁ f
   Finj {1F} {1F} f = f

   identity : ∀ {A} → (Δₙ (ℕ.suc n))[ Finj (Category.id (Δₙ n) {A}) ≈ Category.id (Δₙ (ℕ.suc n)) ]
   identity {0F} = refl
   identity {1F} = refl

   homomorphism : ∀ {X} {Y} {Z} {f : (Δₙ n)[ X , Y ]} {g : (Δₙ n)[ Y , Z ]} →
            (Δₙ (ℕ.suc n))[ Finj ((Δₙ n)[ g ∘ f ]) ≈ (Δₙ(ℕ.suc n))[ Finj g ∘ Finj f ] ]
   homomorphism {0F} {0F} {0F} {f} {g} = refl
   homomorphism {0F} {0F} {1F} {f} {g} = refl
   homomorphism {0F} {1F} {1F} {f} {g} = refl
   homomorphism {1F} {1F} {1F} {f} {g} = refl

   F-resp : ∀ {A} {B} {f g : (Δₙ n)[ A , B ]} →
         (Δₙ n)[ f ≈ g ] → (Δₙ (ℕ.suc n))[ Finj f ≈ Finj g ]
   F-resp {0F} {0F} {f} {g} f≈g = f≈g
   F-resp {0F} {1F} {f} {.f} refl = refl
   F-resp {1F} {1F} {f} {g} f≈g = f≈g

FΔ₂ : Functor Δ₂ Δ₃
FΔ₂ = FΔₙ++ 2
module FΔ₂ = Functor FΔ₂

FΔ₃ : Functor Δ₃ Δ₄
FΔ₃ = FΔₙ++ 3


open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Category.Instance.Sets

Quiv : Category (Level.suc 0ℓ) 0ℓ 0ℓ
Quiv = Functors Δ₂.op (Sets 0ℓ)

Triples : Category (Level.suc 0ℓ) 0ℓ 0ℓ
Triples = Functors Δ₃.op (Sets 0ℓ)

Quads : Category (Level.suc 0ℓ) 0ℓ 0ℓ
Quads = Functors Δ₄.op (Sets 0ℓ)


{-
This allows us to define functor
  𝚫G : Δ₃-Inst → Δ₂-Inst
  𝚫H : Δ₄-Inst → Δ₃-Inst
and so look for their two adjoint functors
Σ and Π .
-}
open import Categories.NaturalTransformation
open import Categories.Category.Instance.Sets
-- reasoning
{- open import Categories.Utils.EqReasoning
open import Categories.Category.Core
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Core
-}

𝚫F : Functor Triples Quiv
𝚫F = record
   { F₀ = λ 3F → 3F ∘F FΔ₂.op  -- 3F a functor from Triples
   ; F₁ = λ μ → μ ∘ʳ FΔ₂.op
   ; identity = λ {F} →  ident F
   ; homomorphism = refl
   ; F-resp-≈ = λ z → z 
   } where 
   -- the answer is refl but it helps to see the types written out
   ident : ∀ (F : Category.Obj Triples) → Quiv [ (Category.id Triples {F} ∘ʳ FΔ₂.op) ≈ Category.id Quiv ]
   ident F = refl

ΠF : Functor Quiv Triples
ΠF = record
     { F₀ = {!!}
     ; F₁ = {!!}
     ; identity = {!!}
     ; homomorphism = {!!}
     ; F-resp-≈ = {!!}
     }

open import Data.Sum using (_⊎_ )

ΣF : Functor Quiv Triples
ΣF = record
   { F₀ =  F0
   ; F₁ = {!!}
   ; identity = {!!}
   ; homomorphism = {!!}
   ; F-resp-≈ = {!!}
   } where
     F0 : Category.Obj Quiv → Category.Obj Triples
     F0 Q  =
          -- todo: can these proofs be shortened by using the above values?
          record
            { F₀ = F₀Δ₃→S
            ; F₁ = F₁Δ₃→S
            ; identity = λ {A} → Δ₃Id {A}
            ; homomorphism = λ {X Y Z} → hom {X} {Y} {Z}
            ; F-resp-≈ = resp-≈
            } where
            module QF = Functor Q

            -- todo: it would be nice to be able to identify the objects of Δ₃ using FΔ₂ so
            -- to leave open the mappings for start and end, as those are not really relevant.
            -- one would then need to identify the remaining middle arrow somehow
            F₀Δ₃→S : Category.Obj Δ₃.op → Category.Obj (Sets 0ℓ)
            F₀Δ₃→S 0F = QF.₀ 0F ⊎ QF.₀ 1F -- original nodes + one node for each arrow
            F₀Δ₃→S 1F = QF.₀ 1F          -- the same arrows

            -- we map start (0F) and end (1F) to the same values as in Quiver
            -- but each arrow is mapped to itself considered as a node
            F₁Δ₃→S : {A B : Δ₃.Obj} → Δ₃.op [ A , B ] → Sets 0ℓ [ F₀Δ₃→S A , F₀Δ₃→S B ]
            F₁Δ₃→S {0F} {0F} 0F = λ z → z
            F₁Δ₃→S {0F} {1F} ()
            F₁Δ₃→S {0F} {Fin.suc (Fin.suc ())} f
            F₁Δ₃→S {1F} {0F} 0F = λ z → _⊎_.inj₁ (QF.₁ 0F z)
            F₁Δ₃→S {1F} {0F} 1F = λ z → _⊎_.inj₁ (QF.₁ 1F z)
            F₁Δ₃→S {1F} {0F} 2F = λ z → _⊎_.inj₂ z
            F₁Δ₃→S {1F} {1F} 0F = λ z → z

            Δ₃Id : {A : Category.Obj (Δ₃.op)} →
              Sets 0ℓ [ F₁Δ₃→S (Category.id Δ₃.op {A}) ≈ Category.id (Sets 0ℓ) ]
            Δ₃Id {0F} = refl
            Δ₃Id {1F} = refl

            hom :  {X Y Z : Δ₃.Obj} {f : Δ₃.op [ X , Y ]} {g : Δ₃.op [ Y , Z ]}
                   → Sets 0ℓ [ F₁Δ₃→S (Δ₃.op [ g ∘ f ]) ≈ Sets 0ℓ [ F₁Δ₃→S g ∘ F₁Δ₃→S f ] ]
            hom {0F} {0F} {0F} {0F} {0F} {X} = refl
            hom {0F} {0F} {1F} {f} {()} {X}
            hom {0F} {0F} {Fin.suc (Fin.suc ())} {f} {g} {X}
            hom {0F} {1F} {0F} {()} {g} {X}
            hom {0F} {Fin.suc (Fin.suc ())} {0F} {f} {g} {X}
            hom {0F} {1F} {1F} {()} {g} {X}
            hom {0F} {1F} {Fin.suc (Fin.suc ())} {f} {g} {X}
            hom {0F} {Fin.suc (Fin.suc ())} {Fin.suc Z} {f} {g} {X}
            hom {1F} {0F} {0F} {0F} {0F} {X} = refl
            hom {1F} {0F} {0F} {1F} {0F} {X} = refl
            hom {1F} {0F} {0F} {2F} {0F} {X} = refl
            hom {1F} {0F} {1F} {f} {()} {X}
            hom {1F} {0F} {Fin.suc (Fin.suc ())} {f} {g} {X}
            hom {1F} {1F} {0F} {0F} {0F} {X} = refl
            hom {1F} {1F} {0F} {0F} {1F} {X} = refl
            hom {1F} {1F} {0F} {0F} {2F} {X} = refl
            hom {1F} {1F} {1F} {0F} {0F} {X} = refl

            resp-≈ :  {A B : Δ₃.Obj} {f g : Δ₃.op [ A , B ]} →
                      Δ₃.op [ f ≈ g ] → Sets 0ℓ [ F₁Δ₃→S f ≈ F₁Δ₃→S g ]
            resp-≈ {0F} {0F} {0F} {0F} f≈g = refl
            resp-≈ {0F} {1F} {()} {g} f≈g
            resp-≈ {0F} {Fin.suc (Fin.suc ())} {f} {g} f≈g
            resp-≈ {1F} {0F} {0F} {0F} f≈g = refl
            resp-≈ {1F} {0F} {1F} {1F} f≈g = refl
            resp-≈ {1F} {0F} {2F} {2F} f≈g = refl
            resp-≈ {1F} {1F} {0F} {0F} f≈g = refl

     open NaturalTransformation
     open _⊎_
     -- open import Categories.Utils.EqReasoning
     -- open import Categories.Category.Core
     open import Relation.Binary.PropositionalEquality.Core

     F1 : {F G : Category.Obj Quiv} → Quiv [ F , G ] → Triples [ F0 F , F0 G ]
     η (F1 {F} {G} α) 0F (inj₁ x) = inj₁ (η α 0F x) -- apply natural transformation for nodes in Quiv on left
     η (F1 {F} {G} α) 0F (inj₂ y) = inj₂ (η α 1F y) -- add natural transformation for arrows to the right
     η (F1 {F} {G} α) 1F x = η α 1F x  -- arrows follow the same natural transformation as in Quiv
     commute (F1 {F} {G} α) {0F} {0F} 0F {x} = refl
     commute (F1 {F} {G} α) {0F} {1F} () {x}
     commute (F1 {F} {G} α) {0F} {Fin.suc (Fin.suc ())} f {x}
     commute (F1 {F} {G} α) {1F} {0F} 0F {a} = {!!} 
     commute (F1 {F} {G} α) {1F} {0F} 1F {x} = {!x!}
     commute (F1 {F} {G} α) {1F} {0F} 2F {x} = 
       begin
    --   ((η (F1 α) 0F) ∘ ((Functor.F₁ (F0 F)) 2F)) x
    -- ≡⟨⟩
         ((η (F1 α) 0F) ∘ (λ z → inj₂ z)) x -- (Functor.₁ (F0 F) 2F)) x
       ≡⟨⟩ -- apply x to λ z → inj₂ z
         (η (F1 α) 0F) (inj₂  x) 
       ≡⟨⟩ -- apply second definition of η above
         inj₂ (η α 1F x)
       ≡˘⟨ cong inj₂ (h {F} {G} {α} {x}) ⟩
         inj₂ (η (F1 α) 1F x)
       ≡⟨⟩ -- unwrap definition above
         ((λ z → inj₂ z) ∘ (η (F1 α) 1F)) x  -- (Functor.F₁ (F0 G) 2F)
   -- ≡⟨⟩
   --    ((Functor.F₁ (F0 G) 2F) ∘ (η (F1 α) 1F)) x
       ∎ 
       where
          open Relation.Binary.PropositionalEquality.Core.≡-Reasoning
          module Cat = Category (Sets 0ℓ)
          open Cat

          h : ∀ {F} {G} {α : Quiv [ F , G ]} {x : Functor.F₀ (F0 F) 1F}
                   →  η (F1 α) 1F x ≡ η α 1F x
          h {F} {G} {α}  = cong (λ z → (η (F1 α) 1F) z) refl
     commute (F1 {F} {G} α) {1F} {1F} 0F {x} = refl
     sym-commute (F1 {F} {G} α) = {!!}

{-
What I expect:

Where G essentially tells us how to interpret 2-graphs
into 3 graphs, ie, how to recognise s, t in Δ₂ in Δ₃,
𝚫G 𝚫H essentially forget that information, so in the 
case of 𝚫G we loose the ability to group arrows and in the
case of 𝚫H to group graphs.

But what happens in the other direction?
ΣG will probably have to make each arrow a unique type 
ΠG group all the arrows under one type? (or vice versa)
-}

open import Categories.Adjoint

{-
After that it will be uesful to see how the globe
 𝔸 → A → N
relates to Δ₃  
-}

