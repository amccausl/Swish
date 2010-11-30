%-------------------------------=  --------------------------------------------
\chapter{Finger search trees}
%-------------------------------=  --------------------------------------------

%align

> module Swish.HaskellRDF.Sort.FingerSearchtree 
> where
> import Swish.HaskellRDF.Sort.LibBase

%align 33

This is work in progress \ldots

> data Empty a			=  E
>
> data Pennant tree a		=  Top a (tree a)
>
> data Node23 tree23 a		=  N2 (tree23 a) a (tree23 a)
>				|  N3 (tree23 a) a (tree23 a) a (tree23 a) 

> data FingerTree23 tree23 a	=  Nil
>				|  One (Pennant tree23 a) (FingerTree23 (Node23 tree23) a)
>				|  Two (Pennant (Node23 tree23) a) (FingerTree23 (Node23 tree23) a)
>
> type Bag a			=  FingerTree23 Empty a

> incr						:: Pennant tree23 a -> FingerTree23 tree23 a -> FingerTree23 tree23 a
> incr p Nil					=  One p Nil
> incr (Top a1 t1) (One (Top a2 t2) ds)		=  Two (Top a1 (N2 t1 a2 t2)) ds
> incr (Top a1 t1) (Two (Top a2 (N2 t2 a3 t3)) ds)
>						=  Two (Top a1 (N3 t1 a2 t2 a3 t3)) ds
> incr (Top a1 t1) (Two (Top a2 (N3 t2 a3 t3 a4 t4)) ds)
>						=  Two (Top a1 (N2 t1 a2 t2)) (incr (Top a3 (N2 t3 a4 t4)) ds)

> data Grown tree23 a		=  U (tree23 a)  
>				|  G (tree23 a) a (tree23 a)
>
> class Ins tree23 where
>     ins			:: (Ord a) => a -> tree23 a -> Grown tree23 a

> instance Ins Empty where
>     ins a E			=  G E a E
>
> instance (Ins tree23) => Ins (Node23 tree23) where
>     ins a (N2 t1 a1 t2)
>         | a <= a1		=  node2l (ins a t1) a1 t2
>         | otherwise		=  node2r t1 a1 (ins a t2)
>     ins a (N3 t1 a1 t2 a2 t3)
>         | a <= a1		=  node3l (ins a t1) a1 t2 a2 t3
>         | a <= a2		=  node3m t1 a1 (ins a t2) a2 t3
>         | otherwise		=  node3r t1 a1 t2 a2 (ins a t3)

> node2l			:: Grown tree23 a -> a -> tree23 a -> Grown (Node23 tree23) a
> node2l (U t1) a1 t2		=  U (N2 t1 a1 t2)
> node2l (G t1 a1 t2) a2 t3	=  U (N3 t1 a1 t2 a2 t3)

> node2r t1 a1 (U t2)		=  U (N2 t1 a1 t2)
> node2r t1 a1 (G t2 a2 t3)	=  U (N3 t1 a1 t2 a2 t3)

> node3l (U t1) a1 t2 a2 t3	=  U (N3 t1 a1 t2 a2 t3)
> node3l (G t1 a1 t2)a2 t3 a3 t4=  G (N2 t1 a1 t2) a2 (N2 t3 a3 t4)

> node3m t1 a1 (U t2) a2 t3	=  U (N3 t1 a1 t2 a2 t3)
> node3m t1 a1 (G t2 a2 t3)a3 t4=  G (N2 t1 a1 t2) a2 (N2 t3 a3 t4)
>
> node3r t1 a1 t2 a2 (U t3)	=  U (N3 t1 a1 t2 a2 t3)
> node3r t1 a1 t2 a2(G t3 a3 t4)=  G (N2 t1 a1 t2) a2 (N2 t3 a3 t4)

> insert'			:: (Ord a, Ins tree23) => a -> FingerTree23 tree23 a -> Maybe (FingerTree23 tree23 a)
> insert' a Nil			=  Nothing
> insert' a (One p@(Top a1 t1) ds)
>     | a <= a1			=  Nothing
>     | otherwise		=  case insert' a ds of
>         Nothing		-> Just (one a1 (ins a t1) ds)
>         Just ds'		-> Just (One p ds')
> insert' a (Two p@(Top a1 t1) ds)
>     | a <= a1			=  Nothing
>     | otherwise		=  case insert' a ds of
>         Nothing		-> Just (two a1 (ins a t1) ds)
>         Just ds'		-> Just (Two p ds')

> one				:: a -> Grown tree23 a -> FingerTree23 (Node23 tree23) a -> FingerTree23 tree23 a
> one a1 (U t1) t2		=  One (Top a1 t1) t2
> one a1 (G t1 a2 t2) t3	=  Two (Top a1 (N2 t1 a2 t2)) t3
>
> two				:: a -> Grown (Node23 tree23) a -> FingerTree23 (Node23 tree23) a -> FingerTree23 tree23 a
> two a1 (U t1) t2		=  Two (Top a1 t1) t2
> two a1 (G t1 a2 t2) t3	=  Two (Top a1 t1) (incr (Top a2 t2) t3)

> insert			:: (Ord a) => a -> Bag a -> Bag a
> insert a t			=  case insert' a t of
>     Nothing			-> incr (Top a E) t
>     Just t'			-> t'

> class Inord tree23 where
>     inord			:: tree23 a -> Sequ a
>
> instance Inord Empty where
>     inord E			=  empty
>
> instance (Inord tree23) => Inord (Node23 tree23) where
>     inord (N2 t1 a1 t2)	=  inord t1 . single a1 . inord t2
>     inord (N3 t1 a1 t2 a2 t3)	=  inord t1 . single a1 . inord t2
>				.  single a2 . inord t3
>
> instance (Inord tree23) => Inord (Pennant tree23) where
>     inord (Top a t)		=  single a . inord t

> inorder'			:: (Inord tree23) => FingerTree23 tree23 a -> Sequ a
> inorder' Nil			=  empty
> inorder' (One p ds)		=  inord p . inorder' ds
> inorder' (Two p ds)		=  inord p . inorder' ds
>
> inorder			:: Bag a -> [a]
> inorder b			=  inorder' b []

> fingerTreeSort		:: (Ord a) => [a] -> [a]
> fingerTreeSort		=  inorder . foldr insert Nil

> type Sequ a			=  [a] -> [a]
>
> empty				=  \x -> x
>
> single a			=  \x -> a : x
