module Data.DiffList

import Control.Relation
import Data.List
import Data.Nat

public export
data IsSuffixOf : (xs, ys : List a) -> Type where
    SuffixRefl : xs `IsSuffixOf` xs
    ConsSuffix : xs `IsSuffixOf` ys -> xs `IsSuffixOf` (y :: ys)

export
Reflexive (List a) IsSuffixOf where
    reflexive = SuffixRefl

export
Transitive (List a) IsSuffixOf where
    transitive prf1 SuffixRefl = prf1
    transitive prf1 (ConsSuffix prf2) = ConsSuffix (transitive prf1 prf2)

export
Preorder (List a) IsSuffixOf where

-- export
-- Antisymmetric (List a) IsSuffixOf where
--     antisymmetric SuffixRefl _ = Refl
--     antisymmetric _ SuffixRefl = Refl
--     antisymmetric {x = x :: xs, y = y :: ys} (ConsSuffix a) (ConsSuffix b) = absurd $ antimsymmetricLemma1 [] a b

export
appendIsSuffix : (xs, ys : List a) -> ys `IsSuffixOf` xs ++ ys
appendIsSuffix [] ys = SuffixRefl
appendIsSuffix (x :: xs) ys = ConsSuffix (appendIsSuffix xs ys)

export
suffixLengthLTE : (xs, ys : List a) -> xs `IsSuffixOf` ys -> length xs `LTE` length ys
suffixLengthLTE xs xs SuffixRefl = reflexive
suffixLengthLTE xs (y :: ys) (ConsSuffix x) = lteSuccRight (suffixLengthLTE xs ys x)

||| A diff-list takes a list, and appends new elements on the front
||| This allows for cheap concatenation, no matter how it is associated
|||
||| This implementation includes a proof that the function can only append
||| elements to the front
public export
record DiffList a where
    constructor MkDiffList
    append : List a -> List a
    0 isSuffix : (rest : List a) -> rest `IsSuffixOf` append rest

public export
Nil : DiffList a
Nil = MkDiffList id (\_ => reflexive)

public export
(::) : a -> DiffList a -> DiffList a
x :: xs = MkDiffList
    (\ys => x :: xs.append ys)
    (\rest => ConsSuffix (xs.isSuffix rest))

public export %inline
toList : DiffList a -> List a
toList xs = xs.append []

export
diffAppendIsSuffix :
    (xs, ys : DiffList a) ->
    (rest : List a) ->
    rest `IsSuffixOf` xs.append (ys.append rest)

public export %inline
Semigroup (DiffList a) where
    xs <+> ys = MkDiffList
        (\zs => xs.append (ys.append zs))
        (\rest =>
            let ysPrf = ys.isSuffix _
                xsPrf = xs.isSuffix _
             in transitive ysPrf xsPrf)

public export %inline
Monoid (DiffList a) where
    neutral = Nil

public export %inline
singleton : a -> DiffList a
singleton x = MkDiffList (\xs => x :: xs) (\rest => ConsSuffix SuffixRefl)

public export %inline
fromList : List a -> DiffList a
fromList xs = MkDiffList (\ys => xs ++ ys) (\rest => appendIsSuffix xs rest)

-- Non-empty
{-
public export 0
NonEmpty : DiffList a -> Type
NonEmpty xs = (rest : List a) -> length (xs.append rest) `GT` length rest

export
singletonIsNonEmpty : (x : _) -> NonEmpty (DiffList.singleton x)
singletonIsNonEmpty x rest = LTESucc reflexive

export
nonEmptyRightNonEmpty : (xs, ys : DiffList a) -> NonEmpty ys -> NonEmpty (xs <+> ys)
nonEmptyRightNonEmpty xs ys prf rest = ?foo -- transitive ?one ?two
-- 

export
nonEmptyLeftNonEmpty : (xs, ys : DiffList a) -> NonEmpty xs -> NonEmpty (xs <+> ys)
nonEmptyLeftNonEmpty xs ys f rest =
    let
        isSuffix = ?wot -- diffAppendIsSuffix xs ys rest
        prf1 = f rest
        prf2 = suffixLengthLTE (xs.append rest) (xs.append (ys.append rest)) isSuffix
     in transitive prf1 prf2

-}

-- Proofs

||| Equality of `DiffList`s is represented as equality of `DiffList.toList` of each side
public export
DiffListEq : (xs, ys : DiffList a) -> Type
DiffListEq xs ys = toList xs === toList ys

infix 6 .==

public export
(.==) : (xs, ys : DiffList a) -> Type
(.==) = DiffListEq

export
semigroupAssoc : (xs, ys, zs : DiffList a) -> ((xs <+> ys) <+> zs) .== (xs <+> (ys <+> zs))
semigroupAssoc xs ys zs = Refl

export
toListFromListId : (xs : List a) -> DiffList.toList (DiffList.fromList xs) === xs
toListFromListId xs = appendNilRightNeutral xs

export
semigroupNilRightNeutral : (xs : DiffList a) -> (xs <+> Nil) .== xs
semigroupNilRightNeutral xs = Refl

export
semigroupNilLeftNeutral : (xs : DiffList a) -> (Nil <+> xs) .== xs
semigroupNilLeftNeutral xs = Refl
