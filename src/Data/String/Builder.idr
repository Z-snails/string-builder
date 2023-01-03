module Data.String.Builder

import Control.Relation
import Control.Order
import public Data.DiffList
import Syntax.PreorderReasoning.Generic

public export
Builder : Type
Builder = DiffList String

public export %inline
FromString Builder where
    fromString = singleton

public export
char : Char -> Builder
char = singleton . cast

public export %inline
build : Builder -> String
build b = concat $ DiffList.toList b

public export
sepBy : Builder -> List Builder -> Builder
sepBy _ [] = neutral
sepBy _ [x] = x
sepBy sep (x :: xs) = MkDiffList
    (\rest => x.append (go xs rest))
    (\rest =>
        let xsPrf = goIsSuffix _ _
            xPrf = x.isSuffix _
         in transitive xsPrf xPrf)
  where
    go : List Builder -> List String -> List String
    go [] acc = acc
    go (x :: xs) acc = sep.append (x.append (go xs acc))

    0
    goIsSuffix : (xs : List Builder) -> (rest : List String) -> IsSuffixOf rest (go xs rest)
    goIsSuffix [] rest = SuffixRefl
    goIsSuffix (x :: xs) rest = CalcWith $
        |~ rest
        <~ go xs rest ...(goIsSuffix _ _)
        <~ x.append (go xs rest) ...(x.isSuffix _)
        <~ sep.append (x.append (go xs rest)) ...(sep.isSuffix _)
        <~ go (x :: xs) rest ...(reflexive)

public export %inline
showB : Show a => a -> Builder
showB = singleton . show
