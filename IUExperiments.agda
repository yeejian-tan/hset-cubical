{-# OPTIONS --cubical=no-glue #-}

-- Experiments accompanying the questions at the bottom of IU.agda.
-- Each `expN…` definition is meant to be normalised (C-c C-n) and inspected.

open import Helper
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Sigma
open import SqFillDef
import IU
import IUFlat   -- unparametrised comparison, see the end of this file

module IUExperiments where

  -- Work in the universe at level 1, i.e. Step over level 0.
  open IU.Step (IU.IUEl 0) (IU.sqFillIU 0) (IU.sqFillIUEl 0)

  -- A closed Π'-headed code: ℕ → ℕ
  ℕ→ℕ : IU
  ℕ→ℕ = Π' ℕ' (λ _ → ℕ')

  -- Neutral ingredients
  postulate
    A A' : IU
    B B' : El A → IU
    pB   : B ≡ B'           -- neutral path between codomains
    pA   : A ≡ A'           -- neutral path between domains
    C    : (i : I) → El (pA i) → IU   -- codomain line over pA
    X Y Z : IU
    p    : X ≡ Y
    q    : Y ≡ Z
    r    : ℕ' ≡ Y           -- neutral path out of a constructor
    a₀   : IU.IUEl 0 .fst   -- neutral code of the previous universe

  ------------------------------------------------------------------
  -- Experiment 1: sqFillIU on four Π'-headed edges.
  -- Does the outer hcomp (walls = decodeEncodeIU …) reduce away?
  ------------------------------------------------------------------

  -- (i) closed: all edges refl on ℕ→ℕ
  exp1-closed : (i j : I) → IU
  exp1-closed i j = sqFillIU {ℕ→ℕ} {ℕ→ℕ} refl {ℕ→ℕ} {ℕ→ℕ} refl refl refl i j

  -- (ii) neutral codomain: l = r = Π' A (pB j), u = d = refl
  exp1-neutral : (i j : I) → IU
  exp1-neutral i j =
    sqFillIU {Π' A B} {Π' A B'} (λ j → Π' A (pB j))
             {Π' A B} {Π' A B'} (λ j → Π' A (pB j))
             refl refl i j

  -- (iii) neutral domain *and* codomain
  exp1-neutral-dom : (i j : I) → IU
  exp1-neutral-dom i j =
    sqFillIU {Π' A (C i0)} {Π' A' (C i1)} (λ j → Π' (pA j) (C j))
             {Π' A (C i0)} {Π' A' (C i1)} (λ j → Π' (pA j) (C j))
             refl refl i j

  ------------------------------------------------------------------
  -- Experiment 2: sqFillIU on a constant square.
  ------------------------------------------------------------------

  exp2-ℕ' : (i j : I) → IU
  exp2-ℕ' i j = sqFillIU {ℕ'} {ℕ'} refl {ℕ'} {ℕ'} refl refl refl i j

  exp2-IU' : (i j : I) → IU
  exp2-IU' i j = sqFillIU {IU'} {IU'} refl {IU'} {IU'} refl refl refl i j

  exp2-Π-closed : (i j : I) → IU
  exp2-Π-closed = exp1-closed

  exp2-Π-neutral : (i j : I) → IU
  exp2-Π-neutral i j = sqFillIU {Π' A B} {Π' A B} refl {Π' A B} {Π' A B} refl refl refl i j

  exp2-El'-neutral : (i j : I) → IU
  exp2-El'-neutral i j = sqFillIU {El' a₀} {El' a₀} refl {El' a₀} {El' a₀} refl refl refl i j

  -- fully neutral corner: blocked on the case split of sqFillIU
  exp2-neutral : (i j : I) → IU
  exp2-neutral i j = sqFillIU {X} {X} refl {X} {X} refl refl refl i j

  ------------------------------------------------------------------
  -- Experiment 3: hcomp {IU} with Π'-headed walls and base.
  -- Does Agda push the hcomp into the arguments of Π'?
  ------------------------------------------------------------------

  -- domain fixed, codomain varies
  exp3-fixed-dom : (i : I) → IU
  exp3-fixed-dom i = hcomp (λ where k (i = i0) → Π' A (pB k)
                                    k (i = i1) → Π' A B)
                           (Π' A B)

  -- domain varies too: needs a heterogeneous comp in the codomain
  exp3-var-dom : (i : I) → IU
  exp3-var-dom i = hcomp (λ where k (i = i0) → Π' (pA k) (C k)
                                  k (i = i1) → Π' A (C i0))
                         (Π' A (C i0))

  -- closed walls
  exp3-closed : (i : I) → IU
  exp3-closed i = hcomp (λ where k (i = i0) → ℕ→ℕ
                                 k (i = i1) → ℕ→ℕ)
                        ℕ→ℕ

  ------------------------------------------------------------------
  -- Experiment 4: El of an hcomp {IU} on neutral terms.
  ------------------------------------------------------------------

  exp4-neutral : (i : I) → Type
  exp4-neutral i = El (hcomp (λ where k (i = i0) → X
                                      k (i = i1) → q k)
                             (p i))

  -- constructor base, neutral walls
  exp4-mixed : (i : I) → Type
  exp4-mixed i = El (hcomp (λ where k (i = i0) → ℕ'
                                    k (i = i1) → r k)
                           ℕ')

  -- Π'-headed everything (relies on experiment 3 reducing)
  exp4-Π : (i : I) → Type
  exp4-Π i = El (exp3-fixed-dom i)

  ------------------------------------------------------------------
  -- Variants with a *closed* domain and a neutral codomain, to separate
  -- "stuck because the domain is neutral" from "stuck because of B".
  ------------------------------------------------------------------
  postulate
    B₀ B₁ : ℕ → IU
    pBℕ   : B₀ ≡ B₁
    n     : ℕ

  exp1-closed-dom : (i j : I) → IU
  exp1-closed-dom i j =
    sqFillIU {Π' ℕ' B₀} {Π' ℕ' B₁} (λ j → Π' ℕ' (pBℕ j))
             {Π' ℕ' B₀} {Π' ℕ' B₁} (λ j → Π' ℕ' (pBℕ j))
             refl refl i j

  exp3-closed-dom : (i : I) → IU
  exp3-closed-dom i = hcomp (λ where k (i = i0) → Π' ℕ' (pBℕ k)
                                     k (i = i1) → Π' ℕ' B₀)
                            (Π' ℕ' B₀)

  ------------------------------------------------------------------
  -- RESULTS  (checked with agda-cubical-uip-dev, 2.9.0-a081e3f)
  --
  -- Method: C-c C-n on the λ-forms above, plus the definitional
  -- checks below.  Caveat: do NOT normalise at *postulated* interval
  -- points (postulate 𝕚 : I): the face (𝕚 = i0) cannot be turned into
  -- a substitution, so no hcomp reduces, not even `exp3-closed 𝕚`.
  ------------------------------------------------------------------

  isΠ : IU → Type
  isΠ (Π' _ _) = ⊤
  isΠ _        = ⊥

  isEl' : IU → Type
  isEl' (El' _) = ⊤
  isEl' _       = ⊥

  ------------------------------------------------------------------
  -- Root cause shared by every "no" below: no regularity for
  -- *parametrised* data types.  IU (at every level, including the
  -- bottom one over ⊥) is a data type with parameters (the Step module
  -- parameters), so Agda transports in it with a generated `transpIU`
  -- that pattern-matches on its argument, even along a constant line.
  -- A parameterless data type gets `transp = id` instead.
  ------------------------------------------------------------------

  reg-ℕ : transp (λ _ → ℕ) i0 n ≡ n
  reg-ℕ = refl
  -- reg-IU : transp (λ _ → IU) i0 A ≡ A
  -- reg-IU = refl
  --   ✗  transpIU (λ _ → IU.IUEl 0) … i0 A  ≠  A
  -- (Same with a toy `data PTree (X : Type)` vs a parameterless `Tree`:
  --  only the parameterless one satisfies transp (λ _ → T) i0 t ≡ t.)

  ------------------------------------------------------------------
  -- Experiment 1: sqFillIU on Π'-headed edges.
  --
  -- The outer hcomp (decodeEncodeIU walls) does go away *at the head*:
  -- by experiment 3 Agda pushes it into Π', so the result is Π'-headed,
  -- closed or neutral.
  ------------------------------------------------------------------

  exp1-closed-isΠ : (i j : I) → isΠ (exp1-closed i j)
  exp1-closed-isΠ i j = tt
  exp1-neutral-isΠ : (i j : I) → isΠ (exp1-neutral i j)
  exp1-neutral-isΠ i j = tt
  exp1-neutral-dom-isΠ : (i j : I) → isΠ (exp1-neutral-dom i j)
  exp1-neutral-dom-isΠ i j = tt

  -- (i) closed: the whole square is ℕ→ℕ up to conversion.  Syntactically
  -- its normal form is  Π' ℕ' (hcomp {ℕ → IU} …)  with ~50 hcomps and
  -- ~240 transps (≈1.4 MB printed); it only collapses once the
  -- conversion checker eta-expands and applies the function-typed
  -- hcomp/transp.
  exp1-closed-const : (i j : I) → exp1-closed i j ≡ ℕ→ℕ
  exp1-closed-const i j = refl

  -- (ii) neutral: NOT the expected square, and it already fails on the
  -- *domain*.  encodeIU on (λ _ → A) is a J/transp that ends in
  -- transpIU … i0 A, which is stuck (no regularity, see above).
  -- exp1-neutral-expected : (i j : I) → exp1-neutral i j ≡ Π' A (pB j)
  -- exp1-neutral-expected i j = refl
  --   ✗  <hcomp tower ending in  fst (encodeIU (λ _ → Π' A B) …)>  ≠  A
  --
  -- exp1-closed-dom i j ≡ Π' ℕ' (pBℕ j): the conversion check did not
  -- finish within 400 s, so this one is inconclusive.  By exp3-closed-dom
  -- below, the codomain is expected to be stuck on transpIU.

  ------------------------------------------------------------------
  -- Experiment 2: sqFillIU on a constant square.
  --
  -- Nullary codes collapse syntactically (normal form is λ i j → ℕ').
  ------------------------------------------------------------------

  exp2-ℕ'-const : (i j : I) → exp2-ℕ' i j ≡ ℕ'
  exp2-ℕ'-const i j = refl
  exp2-IU'-const : (i j : I) → exp2-IU' i j ≡ IU'
  exp2-IU'-const i j = refl

  -- Closed Π' (= exp1-closed): constant only up to conversion, see above.

  -- Neutral arguments: the head constructor survives but the arguments
  -- are stuck transports, as guessed.
  exp2-Π-neutral-isΠ : (i j : I) → isΠ (exp2-Π-neutral i j)
  exp2-Π-neutral-isΠ i j = tt
  -- exp2-Π-neutral i j ≡ Π' A B
  --   ✗  domain stuck on fst (encodeIU (λ _ → Π' A B) j) / transpIU … i0 A
  exp2-El'-neutral-isEl' : (i j : I) → isEl' (exp2-El'-neutral i j)
  exp2-El'-neutral-isEl' i j = tt
  -- exp2-El'-neutral i j ≡ El' a₀
  --   ✗  stuck on transp (λ _ → IUPrev) i0 a₀  (the level-0 IU is also
  --      parametrised, by ⊥ , λ ())
  --
  -- exp2-neutral (corner X neutral): sqFillIU does not even fire; it is
  -- blocked on its case split.

  ------------------------------------------------------------------
  -- Experiment 3: hcomp {IU} with Π'-headed walls and base.
  --
  -- YES, Agda pushes it into the arguments, using the generated
  -- projections Π'-0 / Π'-1:
  --   hcomp {IU} u (Π' a b)
  --     = Π' (hcomp (λ k o → transpIU … k (Π'-0 (u k o)))
  --                 (transpIU … i0 a))
  --          (hcomp {El _ → IU} (λ k o → transp … k (Π'-1 (u k o)))
  --                 (transp (λ _ → El _ → IU) i0 b))
  -- i.e. a generic comp over the constructor telescope.  This is NOT the
  -- naive push  Π' A (λ x → hcomp … (B x)),  because of the
  -- transpIU/transp along constant lines.
  ------------------------------------------------------------------

  exp3-var-dom-isΠ : (i : I) → isΠ (exp3-var-dom i)
  exp3-var-dom-isΠ i = tt

  -- closed: collapses up to conversion
  exp3-closed-const : (i : I) → exp3-closed i ≡ ℕ→ℕ
  exp3-closed-const i = refl

  -- exp3-fixed-dom i ≡ Π' A (λ x → hcomp (… pB k x …) (B x))
  --   ✗  domain is  hcomp (… Π'-0 …) (transpIU … i0 A)  ≠  A
  -- exp3-closed-dom i ≡ Π' ℕ' (λ x → hcomp (… pBℕ k x …) (B₀ x))
  --   ✗  the domain is fine (ℕ' is closed), but the codomain walls are
  --      transpIU … i₁ (pBℕ i₁ (transp … x))  ≠  pBℕ i₁ x

  ------------------------------------------------------------------
  -- Experiment 4: El (hcomp {IU} …).
  --
  -- Neutral base or *any* neutral wall: stuck, as guessed.  The normal
  -- forms are literally  El (hcomp …)  (exp4-neutral, and also
  -- exp4-mixed, whose base is the constructor ℕ').  Pushing into
  -- constructors needs every wall to be constructor-headed as well.
  --
  -- Π'-headed walls and base: El computes, because by experiment 3 the
  -- hcomp becomes a Π':
  --   exp4-Π i = (x : El (hcomp … (transpIU … i0 A))) → El (hcomp … )
  ------------------------------------------------------------------

  ------------------------------------------------------------------
  -- Follow-up (IUFlat.agda): a level-1 universe with no parameters.
  --   * transp regularity holds                          ✓
  --   * closed domain: hcomp pushes into Π' naively      ✓
  --   * neutral domain: still stuck on  hcomp [φ ↦ A] A  ✗
  -- So parametrisation accounts for the stuck *transports*; the neutral
  -- cases of experiments 1–2 are additionally blocked by the lack of
  -- regularity for hcomp, and experiment 4 is unaffected.
  ------------------------------------------------------------------
