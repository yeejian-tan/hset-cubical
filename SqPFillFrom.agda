{-# OPTIONS --cubical=no-glue #-}

open import Helper
open import SqFillDef

module SqPFillFrom where
  module _ where
    SqPFill : ∀{ℓ} (A : I → I → Type ℓ) → Type ℓ
    SqPFill A =
        {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
        {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
        (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
        → PathP (λ i → PathP (λ j → A i j) (a₋₀ i) (a₋₁ i)) a₀₋ a₁₋

    fromSqFill : ∀{ℓ} (A : I → I → Type ℓ) → ((i j : I) → SqFill (A i j)) → SqPFill A
    fromSqFill {ℓ} A sqFill {lu} {ld} l {ru} {rd} r u d i j
      = comp (λ k → toij i j k) (λ where
             k (i = i0) → lemmaL (~ k) j
             k (i = i1) → lemmaR (~ k) j
             k (j = i0) → lemmaU (~ k) i
             k (j = i1) → lemmaD (~ k) i) (sqij i j)
      where
        -- from i to j via k
        icoe : (i j k : I) → I
        icoe i j k = if k then j else i end

        lu' ld' ru' rd' : A i j
        toij : I → I → I → Type ℓ
        toij ii jj k = A (icoe ii i k) (icoe jj j k)

        toij' : I → I → I → I → I → Type ℓ
        toij' ii i jj j k = A (icoe ii i k) (icoe jj j k)

        lu' = transport (λ k → toij i0 i0 k) lu
        lemmaLu : PathP (λ k → toij i0 i0 k) lu lu'
        lemmaLu k = transport-filler (λ k → toij i0 i0 k) lu k

        ld' = transport (λ k → toij i0 i1 k) ld
        lemmaLd : PathP (λ k → toij i0 i1 k) ld ld'
        lemmaLd k = transport-filler (λ k → toij i0 i1 k) ld k


        ru' = transport (λ k → toij i1 i0 k) ru
        lemmaRu : PathP (λ k → toij i1 i0 k) ru ru'
        lemmaRu k = transport-filler (λ k → toij i1 i0 k) ru k

        rd' = transport (λ k → toij i1 i1 k) rd
        lemmaRd : PathP (λ k → toij i1 i1 k) rd rd'
        lemmaRd k = transport-filler (λ k → toij i1 i1 k) rd k

        l' : lu' ≡ ld'
        l' jj = comp (λ k → toij' i0 i jj j k)
                    (λ where
                    k (jj = i0) → lemmaLu k
                    k (jj = i1) → lemmaLd k) (l jj)
        r' : ru' ≡ rd'
        r' jj = comp (λ k → toij' i1 i jj j k)
                    (λ where
                    k (jj = i0) → lemmaRu k
                    k (jj = i1) → lemmaRd k) (r jj)
        u' : lu' ≡ ru'
        u' ii = comp (λ k → toij' ii i i0 j k)
                    (λ where
                    k (ii = i0) → lemmaLu k
                    k (ii = i1) → lemmaRu k) (u ii)
        d' : ld' ≡ rd'
        d' ii = comp (λ k → toij' ii i i1 j k)
                    (λ where
                    k (ii = i0) → lemmaLd k
                    k (ii = i1) → lemmaRd k) (d ii)

        sqij : Square l' r' u' d'
        sqij = sqFill i j l' r' u' d'

        lemmaL      : PathP            (λ k → PathP (λ jj → toij' i0 i jj j k) (lemmaLu k) (lemmaLd k)) l l'
        lemmaL k k' = transport-filler (λ k → PathP (λ jj → toij' i0 i jj j k) (lemmaLu k) (lemmaLd k)) l k k'
        lemmaR      : PathP            (λ k → PathP (λ jj → toij' i1 i jj j k) (lemmaRu k) (lemmaRd k)) r r'
        lemmaR k k' = transport-filler (λ k → PathP (λ jj → toij' i1 i jj j k) (lemmaRu k) (lemmaRd k)) r k k'
        lemmaU      : PathP            (λ k → PathP (λ ii → toij' ii i i0 j k) (lemmaLu k) (lemmaRu k)) u u'
        lemmaU k k' = transport-filler (λ k → PathP (λ ii → toij' ii i i0 j k) (lemmaLu k) (lemmaRu k)) u k k'
        lemmaD      : PathP            (λ k → PathP (λ ii → toij' ii i i1 j k) (lemmaLd k) (lemmaRd k)) d d'
        lemmaD k k' = transport-filler (λ k → PathP (λ ii → toij' ii i i1 j k) (lemmaLd k) (lemmaRd k)) d k k'
