%-------------------------------=  --------------------------------------------
\chapter{Squiggol}
%-------------------------------=  --------------------------------------------

%align

> module Swish.HaskellRDF.Sort.Squiggol (module Swish.HaskellRDF.Sort.Squiggol)
> where
> import Swish.HaskellRDF.Sort.ListLib (halve)
> import Swish.HaskellRDF.Sort.MergeSort (merge)

%align 33
%format (cata (x))              = "\llparenthesis " x "\rrparenthesis "
%format (ana (x))               = "\llbracket " x "\rrbracket "
%format phi                     = "\varphi "
%format psi                     = "\psi "
%format (In (a))		=  a

The squiggol approach to sorting.

> newtype Mu f			=  In (f (Mu f))
>
> cata				:: (Functor f) => (f a -> a) -> Mu f -> a
> cata phi (In x)		=  phi (fmap (cata phi) x)
>
> ana				:: (Functor f) => (a -> f a) -> a -> Mu f
> ana psi x			=  In (fmap (ana psi) (psi x))
>
> data Cell a list		=  Nil | Cons a list
>
> type List a			=  Mu (Cell a)

> data Node a bush		=  Empty | Leaf a | Fork bush bush
>
> instance Functor (Node a) where
>     fmap f Empty		=  Empty
>     fmap f (Leaf a)		=  Leaf a
>     fmap f (Fork b1 b2)	=  Fork (f b1) (f b2)
>
> type Bush a			=  Mu (Node a)

> mergeSort			:: (Ord a) => [a] -> [a]
> mergeSort			=  cata join . ana split

> split				:: [a] -> Node a [a]
> split []			=  Empty
> split [a]			=  Leaf a
> split as			=  uncurry Fork (halve as)

> join				:: (Ord a) => Node a [a] -> [a]
> join Empty			=  []
> join (Leaf a)			=  [a]
> join (Fork l r)		=  merge l r
