module Data.String.Builder.Test

import Data.String.Builder

export
numbers : Builder
numbers = sepBy ", " (showB <$> [1..10])

export
alphabet : Builder
alphabet = concat $ char <$> ['a'..'z']
