%- - - - - - - - - - - - - - - -=  - - - - - - - - - - - - - - - - - - - - - -
\subsection{Cartesian trees}
%- - - - - - - - - - - - - - - -=  - - - - - - - - - - - - - - - - - - - - - -

%align

> module Swish.HaskellRDF.Sort.CartesianTree 
> where

%align 33

> data BinTree a		=  Leaf
>				|  Node (BinTree a) a (BinTree a)
>				   deriving (Show)

Constructing a cartesian tree in linear time.

> data Spine a			=  Nil
>				|  Cons a (BinTree a) (Spine a)

> up				:: BinTree a -> Spine a -> BinTree a
> up l Nil			=  l
> up l (Cons a r s)		=  up (Node l a r) s

> cartesianTree			:: (Ord a) => [a] -> BinTree a
> cartesianTree			=  cartesianTreeBy (<=)
>
> cartesianTreeBy (<=)		=  up Leaf . foldr (\a s -> cons a Leaf s) Nil
>   where cons a t Nil		=  Cons a t Nil
>         cons a t s@(Cons a' t' s')
>             | a <= a'		=  cons a (Node t a' t') s'
>             | otherwise	=  Cons a t s

|cartesianTree [5, 8, 2, 3, 7, 4, 10, 0]|

\NB The obvious approaches (top-down and bottom-up) both lead to
$\Theta(n\log n)$ algorithms. For curiosity here is the top-down
variant of |meld|.

> meld				:: (Ord a) => BinTree a -> BinTree a -> BinTree a
> meld Leaf u			=  u
> meld t Leaf			=  t
> meld t@(Node l a r) u@(Node l' a' r')
>     | a <= a'			=  Node l a (meld r u)
>     | otherwise		=  Node (meld t l') a' r'

Note that the relative order of elements is preserved. The bottom-up
variants of cartesian trees are called \technical{pagodas}.
