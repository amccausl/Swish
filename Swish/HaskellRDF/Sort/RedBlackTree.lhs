%-------------------------------=  --------------------------------------------
\chapter{Red-black trees}
%-------------------------------=  --------------------------------------------

%align

> module Swish.HaskellRDF.Sort.RedBlackTree 
> where
> import Swish.HaskellRDF.Sort.LibBase

%align 33

Every search tree scheme can be used for sorting: the elements are
repeatedly inserted into an empty initial tree; an inorder traversal of
the final tree yields the desired ordered permutation of the input.
Here we use red-black trees as described by Chris Okasaki
\cite[p.~24]{Oka98Pur}.

Sorting on the basis of red-black trees is asymptotically optimal and
stable but neither adpative nor lazy.

> data RedBlackTree a		=  Empty
>				|  Red (RedBlackTree a) a (RedBlackTree a)
>				|  Black (RedBlackTree a) a (RedBlackTree a)

\NB For reasons of efficiency nodes do not have a separate color field,
instead the color is coded into the constructor.

> insertBy			:: Rel a -> a -> RedBlackTree a -> RedBlackTree a
> insertBy (<=) a t		=  blacken (ins t)
>   where ins Empty		=  Red Empty a Empty
>         ins (Red l b r)
>             | a <= b		=  Red (ins l) b r
>             | otherwise	=  Red l b (ins r)
>         ins (Black l b r)
>             | a <= b		=  lblack (ins l) b r
>             | otherwise	=  rblack l b (ins r)
>
> blacken			:: RedBlackTree a -> RedBlackTree a
> blacken (Red l a r)		=  Black l a r
> blacken t			=  t

%align 49
{\setlength{\lwidth}{\lwidth + 1cm}

> lblack					:: RedBlackTree a -> a -> RedBlackTree a -> RedBlackTree a
> lblack (Red (Red t1 a1 t2) a2 t3) a3 t4	=  Red (Black t1 a1 t2) a2 (Black t3 a3 t4)
> lblack (Red t1 a1 (Red t2 a2 t3)) a3 t4	=  Red (Black t1 a1 t2) a2 (Black t3 a3 t4)
> lblack l a r					=  Black l a r
>
> rblack					:: RedBlackTree a -> a -> RedBlackTree a -> RedBlackTree a
> rblack t1 a1 (Red (Red t2 a2 t3) a3 t4)	=  Red (Black t1 a1 t2) a2 (Black t3 a3 t4)
> rblack t1 a1 (Red t2 a2 (Red t3 a3 t4))	=  Red (Black t1 a1 t2) a2 (Black t3 a3 t4)
> rblack l a r					=  Black l a r

}
%align 33

> inorder			:: RedBlackTree a -> [a]
> inorder t			=  traverse t []
>     where
>     traverse Empty x		=  x
>     traverse (Red l a r) x	=  traverse l (a : traverse r x)
>     traverse (Black l a r) x	=  traverse l (a : traverse r x)
>
> redBlackSort			:: (Ord a) => [a] -> [a]
> redBlackSort			=  redBlackSortBy (<=)
>
> redBlackSortBy		:: Rel a -> [a] -> [a]
> redBlackSortBy (<=)		=  inorder . foldr (insertBy (<=)) Empty


Note that |lblack| and |rblack| sometimes perform an unnecessary test
since both subtrees are tested for red-red violations. Here is a
variant of |insertBy| which remedies this shortcoming, albeit at the
expense of readability (this solves exercise~3.10(b) in
\cite{Oka98Pur}, the original version already solves
exercise~3.10(a)).

> insertBy'			:: Rel a -> a -> RedBlackTree a -> RedBlackTree a
> insertBy' (<=) a t		=  blacken (ins t)
>     where
>     ins Empty			=  Red Empty a Empty
>     ins (Red l b r)		=  error "red node"
>     ins (Black l b r)		=  black l b r
>
>     black l b r
>       | a <= b		=  case l of
>         Empty			-> Black (Red Empty a Empty) b r
>         Red ll lb lr
>           | a <= lb		-> case ins ll of
>             Red lll llb llr	-> Red (Black lll llb llr) lb (Black lr b r)
>             ll'		-> Black (Red ll' lb lr) b r
>           | otherwise		-> case ins lr of
>             Red lrl lrb lrr	-> Red (Black ll lb lrl) lrb (Black lrr b r)
>             lr'		-> Black (Red ll lb lr') b r
>         Black ll lb lr	-> Black (black ll lb lr) b r
>       | otherwise		=  case r of
>         Empty			-> Black l b (Red Empty a Empty)
>         Red rl rb rr
>           | a <= rb		-> case ins rl of
>             Red rll rlb rlr	-> Red (Black l b rll) rlb (Black rlr rb rr)
>             rl'		-> Black l b (Red rl' rb rr)
>           | otherwise		-> case ins rr of
>             Red rrl rrb rrr	-> Red (Black l a rl) rb (Black rrl rrb rrr)
>             rr'		-> Black l b (Red rl rb rr')
>         Black ll lb lr	-> Black l b (black ll lb lr)
>
> redBlackSort'			:: (Ord a) => [a] -> [a]
> redBlackSort'			=  redBlackSortBy (<=)
>
> redBlackSortBy'		:: Rel a -> [a] -> [a]
> redBlackSortBy' (<=)		=  inorder . foldr (insertBy' (<=)) Empty

Empirical tests show that the decrease in readability is not justified
or counterbalanced by an increase in speed: |redBlackSort'| is
sometimes marginally faster, and sometimes marginally slower.
\Todo{Curiously, |redBlackSort'| outperforms |redBlackSort| on strictly
increasing sequences thereby contradicting the theory.}
