> module Swish.HaskellRDF.Sort.Stable (module Swish.HaskellRDF.Sort.Stable)
> where
> import Data.List (group)
> import Swish.HaskellRDF.Sort.ListLib
> import Swish.HaskellRDF.Sort.LibBase
> import Swish.HaskellRDF.Sort.PairingHeap

Datentypen, um Stabilit"at zu testen.

> data With a b                 =  a :- b
>                               deriving (Show)
>
> sat				:: With a b -> b
> sat (_ :- s)			=  s

> instance (Eq a) => Eq (With a b) where
>     a :- _ == b :- _          =  a == b
>
> instance (Ord a) => Ord (With a b) where
>     a :- _ <= b :- _          =  a <= b

> number			:: (Enum b, Num b) => [a] -> [With a b]
> number as			=  [ a :- i | (a, i) <- zip as [1 ..] ]

> isStable			:: (Num a, Num b, Enum b, Eq c, Ord d)
>				=> ([With a b] -> [With c d]) -> [([a],[With c d])]
> isStable sort			=  [ (as, s)
>				   | as <- perms [1, 1, 2, 2, 2],
>				     let as' = number as,
>				     let s = sort as',
>				     not (stable s) ]

> stable			:: (Eq a, Ord b) => [With a b] -> Bool
> stable as			=  and [ ordered (map sat g) | g <- group as ]

%if False

> {-
> data A			=  A1 | A2 | A3
>
> instance Eq A where
>     _ == _			=  True
>
> instance Ord A where
>     compare _ _		=  EQ

> eq A1 A1			=  True
> eq A2 A2			=  True
> eq A3 A3			=  True
> eq _ _			=  False
>
> equal as1 as2			=  and [ eq a1 a2 | (a1, a2) <- zip as1 as2 ]

[ (as, s) | as <- perms [A1, A2, A3], let s = heapSort as, not (equal as s) ]

> -}

%endif
