{-# OPTIONS --cubical=no-glue #-}

open import Agda.Primitive renaming (Set to Type)
open import Helper
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Sigma
open import SqFillDef

-- taken from Ondrej Kubánek's master's thesis: Canonicity of the Mahlo Universe
module IU where

  Fam : Type₁
  Fam = Σ Type (λ A → A → Type)

  module Step (IUElPrev : Fam)
              (sqFillIUPrev : SqFill (fst IUElPrev))
              (sqFillElPrev : ∀ A' → SqFill (snd IUElPrev A')) where
    IUPrev = fst IUElPrev -- IU at the previous level
    ElPrev = snd IUElPrev -- El at the previous level

    mutual
      data IU : Type where
        IU' : IU                            -- hat(U)_i : U_(i+1)
        El' : (A' : IUPrev) → IU -- hat(A) : U_i => hat(A) : U_(i+1)
        ℕ' : IU
        Π' : (A : IU) → (El A → IU) → IU

      El : IU → Type
      El IU' = IUPrev                          -- El hat(U)_i = U_i
      El (El' A') = ElPrev A' -- El (hat(A)) = Elprev hat(A)
      El ℕ' = ℕ
      El (Π' A B) = (x : El A) → El (B x)

    CoverIU : (x y : IU) → Type
    CoverIU IU' IU' = ⊤
    CoverIU IU' (El' A') = ⊥
    CoverIU IU' ℕ' = ⊥
    CoverIU IU' (Π' y x) = ⊥
    CoverIU ℕ' ℕ' = ⊤
    CoverIU ℕ' IU' = ⊥
    CoverIU ℕ' (El' A') = ⊥
    CoverIU ℕ' (Π' y x) = ⊥
    CoverIU (El' A') (El' A'') = A' ≡ A''
    CoverIU (El' A') IU' = ⊥
    CoverIU (El' A') ℕ' = ⊥
    CoverIU (El' A') (Π' x x₁) = ⊥
    CoverIU (Π' A B) (Π' A' B') = (A , B) ≡ (A' , B')
    -- CoverIU (Π' A B) (Π' A' B') = Σ (A ≡ A') (λ p → PathP (λ i → El (p i) → IU) B B')
    CoverIU (Π' A B) IU' = ⊥
    CoverIU (Π' A B) (El' A') = ⊥
    CoverIU (Π' A B) ℕ' = ⊥

    reflCodeIU : ∀ x → CoverIU x x
    reflCodeIU IU' = tt
    reflCodeIU (El' A') = refl
    reflCodeIU ℕ' = tt
    reflCodeIU (Π' x y) = refl

    encodeIU : ∀ {x} {y} → x ≡ y → CoverIU x y
    encodeIU {x} = J (λ y _ → CoverIU x y) (reflCodeIU x)

    encodeIURefl : ∀ x → encodeIU {x} refl ≡ reflCodeIU x
    encodeIURefl x = JRefl (λ y _ → y) (reflCodeIU x)

    decodeIU : ∀ {x} {y} → CoverIU x y → x ≡ y
    decodeIU {IU'} {IU'} tt = refl
    decodeIU {El' x} {El' y} c = cong El' c
    decodeIU {ℕ'} {ℕ'} c = refl
    decodeIU {Π' A B} {Π' A' B'} c = cong₂ Π' (cong fst c) (cong snd c)
    -- decodeIU (Π' A B) (Π' A' B') c = cong₂ Π' (fst c) (snd c)s

    decodeIURefl : ∀ x → decodeIU (reflCodeIU x) ≡ refl
    decodeIURefl IU' = refl
    decodeIURefl (El' A') = refl
    decodeIURefl ℕ' = refl
    decodeIURefl (Π' x x₁) = refl

    decodeEncodeIU : ∀ {x} {y} p → decodeIU {x} {y} (encodeIU p) ≡ p
    decodeEncodeIU {x} = J (λ y p → decodeIU (encodeIU p) ≡ p) ((transport (λ i → decodeIU (encodeIURefl x (~ i)) ≡ refl) (decodeIURefl x)))

    sqFillIU : SqFill IU             -- this shows the universe itself has sqfill
    sqFillIUEl : ∀ x → SqFill (El x) -- this shows every type has sqfill.

    sqFillIU {IU'} {IU'} l {IU'} {IU'} r u d i j
      = (hcomp (λ where k (i = i0) → decodeEncodeIU l k j
                        k (i = i1) → decodeEncodeIU r k j
                        k (j = i0) → decodeEncodeIU u k i
                        k (j = i1) → decodeEncodeIU d k i) IU')
    sqFillIU {El' lu} {El' ld} l {El' ru} {El' rd} r u d i j
      = (hcomp (λ where k (i = i0) → decodeEncodeIU l k j
                        k (i = i1) → decodeEncodeIU r k j
                        k (j = i0) → decodeEncodeIU u k i
                        k (j = i1) → decodeEncodeIU d k i)
               (El' (sqFillIUEl IU' (encodeIU l) (encodeIU r) (encodeIU u) (encodeIU d) i j)))
    sqFillIU {ℕ'} {ℕ'} l {ℕ'} {ℕ'} r u d i j
      = (hcomp (λ where k (i = i0) → decodeEncodeIU l k j
                        k (i = i1) → decodeEncodeIU r k j
                        k (j = i0) → decodeEncodeIU u k i
                        k (j = i1) → decodeEncodeIU d k i) ℕ')
    sqFillIU {Π' lu lub} {Π' ld ldb} l {Π' ru rub} {Π' rd rdb} r u d i j
      = (hcomp (λ where k (i = i0) → decodeEncodeIU l k j
                        k (i = i1) → decodeEncodeIU r k j
                        k (j = i0) → decodeEncodeIU u k i
                        k (j = i1) → decodeEncodeIU d k i)
              (decodeSquare encodeIUFilledSquare i j))
      where
        el = encodeIU l
        er = encodeIU r
        eu = encodeIU u
        ed = encodeIU d

        decodeSquare : ∀{lu ld l ru rd r u d}
            → Square {A = Σ IU (λ s → El s → IU)} {lu} {ld} l {ru} {rd} r u d
            → Square {a₀₀ = Π' (lu .fst) (lu .snd)} {Π' (fst ld) (snd ld)} (decodeIU l)
                     {Π' (fst ru) (snd ru)} {Π' (fst rd) (snd rd)} (decodeIU r) (decodeIU u) (decodeIU d)
        decodeSquare sq i j = Π' (sq i j .fst) (sq i j .snd)

        sqs = sqFillIU (cong fst el) (cong fst er) (cong fst eu) (cong fst ed)

        fourSides : I → I → I
        fourSides i j = i ∨ ~ i ∨ j ∨ ~ j

        encodeWHollowSquare : (i j : I) → Partial (fourSides i j) (Σ IU (λ s → El s → IU))
        encodeWHollowSquare i j (i = i0) = (el j .fst , el j .snd)
        encodeWHollowSquare i j (i = i1) = (er j .fst , er j .snd)
        encodeWHollowSquare i j (j = i0) = (eu i .fst , eu i .snd)
        encodeWHollowSquare i j (j = i1) = (ed i .fst , ed i .snd)

        spread : (i j i' j' : I) → sqs i j ≡ sqs i' j'
        spread i j i' j' k = sqs (if k then i' else i end) (if k then j' else j end)

        B : IU → Type
        B s = El s → IU

        p00 : El (sqs i j) → El (sqs i0 i0)
        p00 p = transport (λ k → El (spread i0 i0 i j (~ k))) p
        p01 : El (sqs i j) → El (sqs i0 i1)
        p01 p = transport (λ k → El (spread i0 i1 i j (~ k))) p
        p10 : El (sqs i j) → El (sqs i1 i0)
        p10 p = transport (λ k → El (spread i1 i0 i j (~ k))) p
        p11 : El (sqs i j) → El (sqs i1 i1)
        p11 p = transport (λ k → El (spread i1 i1 i j (~ k))) p

        lub' : El (sqs i j) → IU
        lub' p = lub (transport (λ k → El (spread i0 i0 i j (~ k))) p)
        LemmaLU : PathP (λ k → B (spread i0 i0 i j k)) lub lub'
        LemmaLU k p = lub (transp (λ l → El (spread i0 i0 i j (~ l ∧ k))) (~ k) p)

        ldb' : B (sqs i j)
        ldb' p = ldb (transport (λ k → El (spread i0 i1 i j (~ k))) p)
        LemmaLD : PathP (λ k → B (spread i0 i1 i j k)) ldb ldb'
        LemmaLD k p = ldb (transp (λ l → El (spread i0 i1 i j (~ l ∧ k))) (~ k) p)

        lb : PathP (λ k → B (spread i0 i0 i0 i1 k)) lub ldb
        lb = cong snd el
        lb' : lub' ≡ ldb'
        lb' j' p = lb j' (transport (λ k → El (spread i0 j' i j (~ k))) p)

        LemmaL : PathP (λ k' → PathP (λ k → B (spread (k' ∧ i) (k' ∧ j) (k' ∧ i) (~ k' ∨ j) k)) (LemmaLU k') (LemmaLD k')) lb lb'
        LemmaL k j' p = lb j' (transp (λ l → El (spread i0 j' i j (~ l ∧ k))) (~ k) p)

        rub' : B (sqs i j)
        rub' p = rub (transport (λ k → El (spread i1 i0 i j (~ k))) p)
        LemmaRU : PathP (λ k → B (spread i1 i0 i j k)) rub rub'
        LemmaRU k p = rub (transp (λ l → El (spread i1 i0 i j (~ l ∧ k))) (~ k) p)

        rdb' : B (sqs i j)
        rdb' p = rdb (transport (λ k → El (spread i1 i1 i j (~ k))) p)
        LemmaRD : PathP (λ k → B (spread i1 i1 i j k)) rdb rdb'
        LemmaRD k p = rdb (transp (λ l → El (spread i1 i1 i j (~ l ∧ k))) (~ k) p)

        rb : PathP (λ j → B (sqs i1 j)) rub rdb
        rb = cong snd er
        rb' : rub' ≡ rdb'
        rb' j' p = rb j' (transp (λ k → El (spread i1 j' i j (~ k))) i0 p)
        LemmaR : PathP (λ k' → PathP (λ k → B (spread (~ k' ∨ i) (k' ∧ j) (~ k' ∨ i) (~ k' ∨ j) k)) (LemmaRU k') (LemmaRD k')) rb rb'
        LemmaR k j' p = rb j' (transp (λ l → El (spread i1 j' i j (~ l ∧ k))) (~ k) p)

        ub : PathP (λ i → B (sqs i i0)) lub rub
        ub = cong snd eu
        ub' : lub' ≡ rub'
        ub' i' p = ub i' (transport ((λ k → El (spread i' i0 i j (~ k)))) p)
        LemmaU : PathP (λ k' → PathP (λ k → B (spread (k' ∧ i) (k' ∧ j) (~ k' ∨ i) (k' ∧ j) k)) (LemmaLU k') (LemmaRU k')) ub ub'
        LemmaU k i' p = ub i' (transp (λ l → El (spread i' i0 i j (~ l ∧ k))) (~ k) p)

        db : PathP (λ i → B (sqs i i1)) ldb rdb
        db = cong snd ed
        db' : ldb' ≡ rdb'
        db' i' p = db i' (transport ((λ k → El (spread i' i1 i j (~ k)))) p)
        LemmaD : PathP (λ k' → PathP (λ k → B (spread (k' ∧ i) (~ k' ∨ j) (~ k' ∨ i) (~ k' ∨ j) k)) (LemmaLD k') (LemmaRD k')) db db'
        LemmaD k i' p = db i' (transp (λ l → El (spread i' i1 i j (~ l ∧ k))) (~ k) p)

        encodeIUFilledSquare : Square {a₀₀ = (lu , lub)} el er eu ed
        encodeIUFilledSquare i' j' .fst = sqFillIU (cong fst el) (cong fst er) (cong fst eu) (cong fst ed) i' j'
        encodeIUFilledSquare i' j' .snd =
            comp (λ k → B (spread i j i' j' k)) (λ where
                k (i' = i0) → LemmaL (~ k) j'
                k (i' = i1) → LemmaR (~ k) j'
                k (j' = i0) → LemmaU (~ k) i'
                k (j' = i1) → LemmaD (~ k) i') (λ ps → sqFillIU {lub (p00 ps)} (λ j → lb' j ps) (λ j → rb' j ps) (λ i → ub' i ps) (λ i → db' i ps) i' j')


    sqFillIU {IU'} {El' _ }  l _ _ _ = ⊥-elim (encodeIU l)
    sqFillIU {IU'} {ℕ'    }  l _ _ _ = ⊥-elim (encodeIU l)
    sqFillIU {IU'} {Π' _ _}  l _ _ _ = ⊥-elim (encodeIU l)
    sqFillIU {El' _} {IU'}  l _ _ _ = ⊥-elim (encodeIU l)
    sqFillIU {El' _} {ℕ'}  l _ _ _ = ⊥-elim (encodeIU l)
    sqFillIU {El' _} {Π' _ _}  l _ _ _ = ⊥-elim (encodeIU l)
    sqFillIU {ℕ'} {IU'}  l _ _ _ = ⊥-elim (encodeIU l)
    sqFillIU {ℕ'} {El' _}  l _ _ _ = ⊥-elim (encodeIU l)
    sqFillIU {ℕ'} {Π' _ _}  l _ _ _ = ⊥-elim (encodeIU l)
    sqFillIU {Π' _ _} {El' _} l _ _ _ = ⊥-elim (encodeIU l)
    sqFillIU {Π' _ _} {ℕ'} l _ _ _ = ⊥-elim (encodeIU l)
    sqFillIU {Π' _ _} {IU'} l _ _ _ = ⊥-elim (encodeIU l)

    sqFillIU _ {IU'} {El' _ }  r _ _ = ⊥-elim (encodeIU r)
    sqFillIU _ {IU'} {ℕ'    }  r _ _ = ⊥-elim (encodeIU r)
    sqFillIU _ {IU'} {Π' _ _}  r _ _ = ⊥-elim (encodeIU r)
    sqFillIU _ {El' _} {IU'}  r _ _ = ⊥-elim (encodeIU r)
    sqFillIU _ {El' _} {ℕ'}  r _ _ = ⊥-elim (encodeIU r)
    sqFillIU _ {El' _} {Π' _ _}  r _ _ = ⊥-elim (encodeIU r)
    sqFillIU _ {ℕ'} {IU'}  r _ _ = ⊥-elim (encodeIU r)
    sqFillIU _ {ℕ'} {El' _}  r _ _ = ⊥-elim (encodeIU r)
    sqFillIU _ {ℕ'} {Π' _ _}  r _ _ = ⊥-elim (encodeIU r)
    sqFillIU _ {Π' _ _} {El' _} r _ _ = ⊥-elim (encodeIU r)
    sqFillIU _ {Π' _ _} {ℕ'} r _ _ = ⊥-elim (encodeIU r)
    sqFillIU _ {Π' _ _} {IU'} r _ _ = ⊥-elim (encodeIU r)

    sqFillIU {IU'} _ {El' _ } _ u _ = ⊥-elim (encodeIU u)
    sqFillIU {IU'} _ {ℕ'    }  _ u _ = ⊥-elim (encodeIU u)
    sqFillIU {IU'} _ {Π' _ _}  _ u _ = ⊥-elim (encodeIU u)
    sqFillIU {El' _} _ {IU'}  _ u _ = ⊥-elim (encodeIU u)
    sqFillIU {El' _} _ {ℕ'}  _ u _ = ⊥-elim (encodeIU u)
    sqFillIU {El' _} _ {Π' _ _}  _ u _ = ⊥-elim (encodeIU u)
    sqFillIU {ℕ'} _ {IU'}  _ u _ = ⊥-elim (encodeIU u)
    sqFillIU {ℕ'} _ {El' _} _ u _ = ⊥-elim (encodeIU u)
    sqFillIU {ℕ'} _ {Π' _ _} _ u _ = ⊥-elim (encodeIU u)
    sqFillIU {Π' _ _} _ {El' _} _ u _ = ⊥-elim (encodeIU u)
    sqFillIU {Π' _ _} _ {ℕ'} _ u _ = ⊥-elim (encodeIU u)
    sqFillIU {Π' _ _} _ {IU'} _ u _ = ⊥-elim (encodeIU u)

    sqFillIUEl IU' = sqFillIUPrev
    sqFillIUEl (El' A') = sqFillElPrev A'
    sqFillIUEl ℕ' = SqFillNat
      where open import SqFillNat
    sqFillIUEl (Π' A' B') = SqFillPi (El A') (λ x → El (B' x)) (λ x → sqFillIUEl (B' x))
      where open import SqFillPi

    IUEl : Fam
    IUEl = IU , El


  IUEl : ℕ → Fam
  sqFillIU : ∀ n → SqFill (IUEl n .fst) -- every universe has sqfill
  sqFillIUEl : ∀ n A' → SqFill (IUEl n .snd A') -- every type in every universe has sqfill

  IUEl zero = Step.IUEl (⊥ , λ ()) (λ {}) λ () -- no previous universe
  IUEl (suc n) = Step.IUEl (IUEl n) (sqFillIU n) λ A' → sqFillIUEl n A'
  sqFillIU zero = Step.sqFillIU (⊥ , λ ()) (λ {}) λ () --
  sqFillIU (suc n) = Step.sqFillIU (IUEl n) (sqFillIU n) (λ A → sqFillIUEl n A) --
  sqFillIUEl zero = Step.sqFillIUEl (⊥ , λ ()) (λ {}) λ () --
  sqFillIUEl (suc n) = Step.sqFillIUEl (IUEl n) (sqFillIU n) (λ A → sqFillIUEl n A) --
