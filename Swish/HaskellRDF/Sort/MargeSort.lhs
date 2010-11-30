%if codeOnly

> module Swish.HaskellRDF.Sort.MargeSort (margeSort, naturalMargeSort)
> where
> import Swish.HaskellRDF.Sort.MergeSort (upDownRunsBy)
>
> data OptPair a b		=  NoPair | Pair a b
>
> data Empty a			=  E
>
> data Node23 tree a		=  N2 (tree a) a (tree a)
>				|  N3 (tree a) a (tree a) a (tree a)
>
> type FST1			=  FingerSearchTree1
>
> type OS			=  OrdSequence
>
> data Grown tree a		=  U (tree a)  
>				|  G (tree a) a (tree a)

%endif
%format Cons (a) (t)		=  a "\triangleleft " t
%format Snoc (t) (a)		=  t "\triangleright " a
%-------------------------------=  --------------------------------------------
\section{Double-ended Finger Search Trees}
\label{sec:fstvariations}
%-------------------------------=  --------------------------------------------

\Todo{Min-Max-Heaps}. The datatype |FST| implements one-sided ordered
sequences.  In order to support operations on both ends --- |snoc =
addMax| and |rear = splitMax| in addition to |cons = AddMin| and |front
= splitMin| --- we must base finger search trees on the symmetric spine
view of 2-3 trees. Here are the necessary type definitions.
%align 9
%{
%format S2			=  Simple2
%format S3			=  Simple3
%format C			=  Composite

> data FingerSearchTree1 tree a
>	=  S2 a
>	|  S3 a (tree a) a
>	|  C (Digit Front tree a)
>            (FingerSearchTree1 (Node23 tree) a)
>            (Digit Rear tree a)
>
> data Digit pennant tree a
>	=  One (pennant tree a)
>	|  Two (pennant (Node23 tree) a)

%}
%align 33

> data Front tree a		=  Cons a (tree a)
>
> data Rear tree a		=  Snoc (tree a) a
>
> data OrdSequence a		=  Nil | Id (FingerSearchTree1 Empty a)

Two points are worth mentioning. First of all, |FST1| is not capable of
representing the empty sequence. For that reason we have introduced the
wrapper datatype |OS| (see also Section~\ref{sec:external}). Second, we
use different types of pennants for the digits on the left and for
those on the right spine view. The types have been chosen so that the
order of elements within an expression reflects the order of elements
within the sequence represented.

% - - - - - - - - - - - - - - - = - - - - - - - - - - - - - - - - - - - - - - -
\subsection{Deque operations}
% - - - - - - - - - - - - - - - = - - - - - - - - - - - - - - - - - - - - - - -

The deque operations, |cons|, |incr|, |splitMin|, |zero| and their
colleagues |snoc|, |rcni|, |splitMax|, |eroz|, can be easily adapted to
the new design. Here, we show the modified versions of |cons| and
|incr| only.
%{
%format One			=  O
%format Two			=  T
%align 41

> cons					:: a -> OrdSequence a -> OrdSequence a
> cons a Nil				=  Id (S2 a)
> cons a (Id s)				=  Id (incr a E s)
>
> incr					:: a -> t a -> FST1 t a -> FST1 t a
> incr a1 t1 (S2 a2)			=  S3 a1 t1 a2
> incr a1 t1 (S3 a2 t2 a3)		=  C (One (Cons a1 t1)) (S2 a2) (One (Snoc t2 a3))
> incr a1 t1 (C (One (Cons a2 t2)) m r)	=  C (Two (Cons a1 (N2 t1 a2 t2))) m r
> incr a1 t1 (C (Two (Cons a2 (N2 t2 a3 t3))) m r)
>     =  {-"\enskip\,"-} C (Two (Cons a1 (N3 t1 a2 t2 a3 t3))) m r
> incr a1 t1 (C (Two (Cons a2 (N3 t2 a3 t3 a4 t4))) m r)
>     =  {-"\enskip\,"-} C (Two (Cons a1 (N2 t1 a2 t2))) (incr a3 (N2 t3 a4 t4) m) r

It is instructive to relate the equations to the rebalancing operations
on 2-3 trees.  The first equation corresponds to an expansion of a
2-node to a 3-node, the second equation realizes a split of a 3-node
into two 2-nodes.
%if codeOnly

> s4					:: a -> t a -> a -> t a -> a -> FST1 t a
> s4 a1 t1 a2 t2 a3			=  C (One (Cons a1 t1)) (S2 a2) (One (Snoc t2 a3))
>
> snoc					:: OrdSequence a -> a -> OrdSequence a
> snoc Nil a				=  Id (S2 a)
> snoc (Id s) a				=  Id (rcni s E a)
>
> rcni					:: FST1 t a -> t a -> a -> FST1 t a
> rcni (S2 a1) t1 a2	 		=  S3 a1 t1 a2
> rcni (S3 a1 t1 a2) t2 a3		=  s4 a1 t1 a2 t2 a3
> rcni (C f m (One (Snoc t1 a1))) t2 a2	=  C f m (Two (Snoc (N2 t1 a1 t2) a2))
> rcni (C f m (Two (Snoc (N2 t1 a1 t2) a2))) t3 a3
>     =  {-"\enskip\,"-} C f m (Two (Snoc (N3 t1 a1 t2 a2 t3) a3))
> rcni (C f m (Two (Snoc (N3 t1 a1 t2 a2 t3) a3))) t4 a4
>     =  {-"\enskip\,"-} C f (rcni m (N2 t1 a1 t2) a2) (Two (Snoc (N2 t3 a3 t4) a4))

> zero'					:: FST1 (Node23 t) a -> Digit Rear t a -> FST1 t a
> zero' (S2 a1) (One (Snoc t1 a2))	=  S3 a1 t1 a2
> zero' (S2 a1) (Two (Snoc (N2 t1 a2 t2) a3))
>					=  s4 a1 t1 a2 t2 a3
> zero' (S2 a1) (Two (Snoc (N3 t1 a2 t2 a3 t3) a4))
>					=  C (One (Cons a1 t1)) (S2 a2) (Two (Snoc (N2 t2 a3 t3) a4))
> zero' (S3 a1 t1 a2) d			=  C (Two (Cons a1 t1)) (S2 a2) d
> zero' (C (One p) m r) d		=  C (Two p) (zero' m r) d
> zero' (C (Two (Cons a1 (N2 t1 a2 t2))) m r) d
>					=  C (Two (Cons a1 t1)) (C (One (Cons a2 t2)) m r) d
> zero' (C (Two (Cons a1 (N3 t1  a2 t2 a3 t3))) m r) d
>					=  C (Two (Cons a1 t1)) (C (Two (Cons a2 (N2 t2 a3 t3))) m r) d
>
> splitMin				:: OrdSequence a -> OptPair a (OrdSequence a)
> splitMin Nil				=  NoPair
> splitMin (Id (S2 a1))			=  Pair a1 Nil
> splitMin (Id (S3 a1 E a2))		=  Pair a1 (Id (S2 a2))
> splitMin (Id (C (One (Cons a1   E)) m r))
>					=  Pair a1 (Id (zero' m r))
> splitMin (Id (C (Two (Cons a1  (N2 E a2 E))) m r))
>					=  Pair a1 (Id (C (One (Cons a2 E)) m r))
> splitMin (Id (C (Two (Cons a1  (N3 E a2 E a3 E))) m r))
>					=  Pair a1 (Id (C (Two (Cons a2 (N2 E a3 E))) m r))

> eroz					:: Digit Front t a -> FST1 (Node23 t) a -> FST1 t a
> eroz (One (Cons a1 t1)) (S2 a2)	=  S3 a1 t1 a2
> eroz (Two (Cons a1 (N2 t1 a2 t2))) (S2 a3)
>					=  s4 a1 t1 a2 t2 a3
> eroz (Two (Cons a1 (N3 t1 a2 t2 a3 t3))) (S2 a4)
>					=  C (Two (Cons a1 (N2 t1 a2 t2))) (S2 a3) (One (Snoc t3 a4))
> eroz d (S3 a1 t1 a2)			=  C d (S2 a1) (Two (Snoc t1 a2))
> eroz d (C f m (One p))		=  C d (eroz f m) (Two p) 
> eroz d (C f m (Two (Snoc (N2 t1 a1 t2) a2)))
>					=  C d (C f m (One (Snoc t1 a1))) (Two (Snoc t2 a2)) 
> eroz d (C f m (Two (Snoc (N3 t1 a1 t2 a2 t3) a3)))
>					=  C d (C f m (Two (Snoc (N2 t1 a1 t2) a2))) (Two (Snoc t3 a3)) 

%endif
%}
%align 33

\smallskip
\noindent\textbf{Remark.} \Todo{Pattern abstractions}

< D1 a1 t1			=  One (Cons a1 t1)
< D2 a1 t1 a2 t2		=  Two (Cons a1 (N2 t1 a2 t2))
< D3 a1 t1 a2 t2 a3 t3		=  Two (Cons a1 (N3 t1 a2 t2 a3 t3))

blub\hfill$\Box$

% - - - - - - - - - - - - - - - = - - - - - - - - - - - - - - - - - - - - - - -
\subsection{Bag operations}
\label{sec:bag}
% - - - - - - - - - - - - - - - = - - - - - - - - - - - - - - - - - - - - - - -

\Todo{Worte zu |insert| und |delete|}. To adapt |member| we must first
symmetrize the auxiliary datatype |Loc|.
%format fun			=  "(\star)"
%format `fun`			=  "\star "

> data Loc a			=  Lt | Eq a | Gt
> 
> between			:: a -> Loc a -> a -> a
> between a1 Lt a3		=  a1
> between a1 (Eq a2) a3		=  a2
> between a1 Gt a3		=  a3

%format fun (f) (a)		=  f "\star " a
The function |between| generalizes the operator |after| of
Section~\ref{sec:search}. Depending on the value of the second
argument the search is continued to the left or to the right.

%format min'			=  min
%format max'			=  max
%subst code a    	= "\begin{array}{@{}lcl}'n" a "'n\end{array}"
\[
\begin{array}{c@@{\qquad}c}

> min' (One (Cons m t))		=  m
> min' (Two (Cons m t))		=  m
>
> max' (One (Snoc t m))		=  m
> max' (Two (Snoc t m))		=  m

&

> memf a (One (Cons m t))	=  mem a t
> memf a (Two (Cons m t))	=  mem a t
>
> memr a (One (Snoc t m))	=  mem a t
> memr a (Two (Snoc t m))	=  mem a t

\end{array}
\]
%subst code a    	= "\[\begin{array}{@{}lcl}'n\hspace{\lwidth}&\hspace{\cwidth}&\\[-10pt]'n" a "'n\end{array}\]"
The function |member'| implements a quasi-parallel search along the two
spines.  If $d_1$ is the distance from the smallest element and $d_2$
the distance from the largest element, then |member| runs in
$\Theta(\min\{d_1, d_2\})$.

> member'			:: (Ord a, Mem t) => a -> FST1 t a -> Loc Bool
> member' a (S2 a1)
>     | a < a1			=  Lt
>     | a > a1			=  Gt
>     | otherwise		=  Eq True
> member' a (S3 a1 t1 a2)
>     | a < a1			=  Lt
>     | a > a2			=  Gt
>     | otherwise		=  Eq (mem a t1)
> member' a (C f m r)
>     | a < min' f		=  Lt
>     | a > max' r		=  Gt
>     | otherwise		=  Eq (between (memf a f) (member' a m) (memr a r))
>
> member			:: (Ord a) => a -> OrdSequence a -> Bool
> member a Nil			=  False
> member a (Id s)		=  between False (member' a s) False


The adaptive sorting algorithm described in Section~\ref{sec:insert}
has the irritating property that the worst case is a list in descending
order which is arguably almost sorted. In a sense this is due to the
measure |Inv| which yields the largest value for lists in descreasing
order. If we represent ordered sequences with 2-3 trees under the
symmetric spine view we obtain a sorting algorithm which is optimal
with respect to $\widehat{|Inv|}$ given by
\[
    \widehat{|Inv|}(x) = \min\{|Inv|(x), |Inv|(|reverse x|)\} \enskip.
\]
The new worst-case is an interleaving of an ascending and a descending
list:
\[
    1, 2n, 2, 2n-1, 3, 2n-2, \ldots, n-2, n+1, n-1, n \enskip.
\]

%if codeOnly

> fun				:: (a -> b) -> Loc a -> Loc b
> f `fun` Lt			=  Lt
> f `fun` (Eq a)		=  Eq (f a)
> f `fun` Gt			=  Gt

> class Mem tree where
>     mem			:: (Ord a) => a -> tree a -> Bool
>
> instance Mem Empty where
>     mem a E			=  False
>
> instance (Mem tree) => Mem (Node23 tree) where
>     mem a (N2 t1 a1 t2)
>         | a < a1		=  mem a t1
>         | a == a1		=  True
>         | otherwise		=  mem a t2
>     mem a (N3 t1 a1 t2 a2 t3)
>         | a < a1		=  mem a t1
>         | a == a1		=  True
>         | a < a2		=  mem a t2
>         | a == a2		=  True
>         | otherwise		=  mem a t3

> type Sequ a			=  [a] -> [a]
>
> empty				=  \x -> x
>
> unit a			=  \x -> a : x

> class Inorder tree where
>     inorder			:: tree a -> Sequ a
>
> instance Inorder Empty where
>     inorder E			=  empty
>
> instance (Inorder tree) => Inorder (Node23 tree) where
>     inorder (N2 t1 a1 t2)	=  inorder t1 . unit a1 . inorder t2
>     inorder(N3 t1 a1 t2 a2 t3)=  inorder t1 . unit a1 . inorder t2 . unit a2 . inorder t3
>
> inord (One p)			=  inorder p
> inord (Two p)			=  inorder p
>
> instance (Inorder tree) => Inorder (Front tree) where
>     inorder (Cons a t)	=  unit a . inorder t
>
> instance (Inorder tree) => Inorder (Rear tree) where
>     inorder (Snoc t a)	=  inorder t . unit a

> toList'			:: (Inorder tree) => FingerSearchTree1 tree a -> Sequ a
> toList' (S2 a1)		=  unit a1
> toList' (S3 a1 t1 a2)		=  unit a1 . inorder t1 . unit a2
> toList' (C f m r)		=  inord f . toList' m . inord r

> toList			:: OrdSequence a -> [a]
> toList Nil			=  []
> toList (Id s)			=  toList' s []

%endif

% - - - - - - - - - - - - - - - = - - - - - - - - - - - - - - - - - - - - - - -
\subsection{Concatenation}
% - - - - - - - - - - - - - - - = - - - - - - - - - - - - - - - - - - - - - - -

%include Pic8.lhs

> (<>)				:: OrdSequence a -> OrdSequence a -> OrdSequence a
> Nil <> s2			=  s2
> s1 <> Nil			=  s1
> Id s1 <> Id s2		=  Id (app s1 (U E) s2)

$a3 = (a+1)1$

%align 49

> norm (Two (Cons a1 (N3 t1 a2 t2 a3 t3))) m	=  (One (Cons a1 t1), incr a2 (N2 t2 a3 t3) m)
> norm f m					=  (f, m)

%align 41

> app					:: FST1 t a -> Grown t a -> FST1 t a -> FST1 t a
> app (S2 a1) (U t1) x			=  incr a1 t1 x
> app (S2 a1) (G t1 a2 t2) x		=  incr a1 t1 (incr a2 t2 x)
> app x (U t1) (S2 a1)			=  rcni x t1 a1
> app x (G t1 a1 t2) (S2 a2)		=  rcni (rcni x t1 a1) t2 a2
> app (S3 a1 t1 a2) (U t2) x		=  incr a1 t1 (incr a2 t2 x)
> app (S3 a1 t1 a2) (G t2 a3 t3) x	=  incr a1 t1 (incr a2 t2 (incr a3 t3 x))
> app x (U t1) (S3 a1 t2 a2)		=  rcni (rcni x t1 a1) t2 a2
> app x (G t1 a1 t2) (S3 a2 t3 a3)	=  rcni (rcni (rcni x t1 a1) t2 a2) t3 a3
> app (C f1 m1 r1) t (C f2 m2 r2)	=  C f1 (app m1' (join r1' t f2') m2') r2
>     where (m1', r1')			=  mron m1 r1
>           (f2', m2')			=  norm f2 m2

%align 33

< join				:: Digit Rear t a -> Grown t a -> Digit Front t a -> Grown (Node23 t) a
< join (One (Snoc t1 a1))  (U t2) (One (Cons a2 t3))
<				=  U (N3 t1 a1 t2 a2 t3)
< join (One (Snoc t1 a1)) (G t2 a2 t3) (One (Cons a3 t4))
<				=  G (N2 t1 a1 t2) a2 (N2 t3 a3 t4)
< {-"\ldots"-}
< join (Two (Snoc (N2 t1 a1 t2) a2)) (G t3 a3 t4) (Two (Cons a4 (N2 t5 a5 t6)))
<				=  G (N3 t1 a1 t2 a2 t3) a3 (N3 t4 a4 t5 a5 t6)

%if codeOnly


> mron m (Two (Snoc (N3 t1 a1 t2 a2 t3) a3))	=  (rcni m (N2 t1 a1 t2) a2, One (Snoc t3 a3))
> mron m r					=  (m, r)
>
> join				:: Digit Rear t a -> Grown t a -> Digit Front t a -> Grown (Node23 t) a
> join (One (Snoc t1 a1))  (U t2) (One (Cons a2 t3))
>				=  U (N3 t1 a1 t2 a2 t3)
> join (One (Snoc t1 a1)) (G t2 a2 t3) (One (Cons a3 t4))
>				=  G (N2 t1 a1 t2) a2 (N2 t3 a3 t4)
> join (One (Snoc t1 a1))  (U t2) (Two (Cons a2 t3))
>				=  G (N2 t1 a1 t2) a2 t3
> join (One (Snoc t1 a1)) (G t2 a2 t3) (Two (Cons a3 t4))
>				=  G (N3 t1 a1 t2 a2 t3) a3 t4
> join (Two (Snoc t1 a1)) (U  t2) (One (Cons a2 t3))
>				=  G t1 a1 (N2 t2 a2 t3)
> join (Two (Snoc t1 a1)) (G t2 a2 t3) (One (Cons a3 t4))
>				=  G t1 a1 (N3 t2 a2 t3 a3 t4)
> join (Two (Snoc (N2 t1 a1 t2) a2)) (U t3) (Two (Cons a3 t4))
>				=  G (N3 t1 a1 t2 a2 t3) a3 t4
> join (Two (Snoc (N2 t1 a1 t2) a2)) (G t3 a3 t4) (Two (Cons a4 (N2 t5 a5 t6)))
>				=  G (N3 t1 a1 t2 a2 t3) a3 (N3 t4 a4 t5 a5 t6)

%endif

% - - - - - - - - - - - - - - - = - - - - - - - - - - - - - - - - - - - - - - -
\subsection{Splitting}
% - - - - - - - - - - - - - - - = - - - - - - - - - - - - - - - - - - - - - - -

> part				:: (Ord a) => a -> FST1 t a -> Loc (FST1 t a, t a, FST1 t a)
> part a (S2 a1)
>     | a <= a1			=  Lt
>     | otherwise		=  Gt
> part a (S3 a1 t1 a2)
>     | a <= a1			=  Lt
>     | a >= a2			=  Gt
>     | otherwise		=  Eq (S2 a1, t1, S2 a2)
> part a (C f m r)
>     | a <= min' f		=  Lt
>     | a >= max' r		=  Gt
>     | otherwise		=  Eq (between (cutf f) (cutm `fun` part a m) (cutr r))
>     where
>     cutm (m1, t, m2)		=  split a f m1 t m2 r
>     cutf (One (Cons a1 t1))	=  (S2 a1, t1, zero' m r)
>     cutf (Two (Cons a1 t1))	=  lsplit a a1 t1 m r
>     cutr (One (Snoc t1 a1))	=  (eroz f m, t1, S2 a1)
>     cutr (Two (Snoc t1 a1))	=  rsplit a f m t1 a1

> split a f m1 (N2 t1 a1 t2) m2 r
>     | a <= a1			=  (eroz f m1, t1, C (One (Cons a1 t2)) m2 r)
>     | otherwise		=  (C f m1 (One (Snoc t1 a1)), t2, zero' m2 r)
> split a f m1 (N3 t1 a1 t2 a2 t3) m2 r
>     | a <= a1			=  (eroz f m1, t1, C (Two (Cons a1 (N2 t2 a2 t3))) m2 r)
>     | a <= a2			=  (C f m1 (One (Snoc t1 a1)), t2, C (One (Cons a2 t3)) m2 r)
>     | otherwise		=  (C f m1 (Two (Snoc (N2 t1 a1 t2) a2)), t3, zero' m2 r)

%if codeOnly

> lsplit a a1 (N2 t1 a2 t2) m2 r
>     | a <= a2			=  (S2 a1, t1, C (One (Cons a2 t2)) m2 r)
>     | otherwise		=  (zero' (S2 a1) (One (Snoc t1 a2)), t2, zero' m2 r)
> lsplit a a1 (N3 t1 a2 t2 a3 t3) m2 r
>     | a <= a2			=  (S2 a1, t1, C (Two (Cons a2 (N2 t2 a3 t3))) m2 r)
>     | a <= a3			=  (zero' (S2 a1) (One (Snoc t1 a2)), t2, C (One (Cons a3 t3)) m2 r)
>     | otherwise		=  (zero' (S2 a1) (Two (Snoc (N2 t1 a2 t2) a3)), t3, zero' m2 r)

> rsplit a f m1 (N2 t1 a1 t2) a2
>     | a <= a1			=  (eroz f m1, t1, eroz (One (Cons a1 t2)) (S2 a2))
>     | otherwise		=  (C f m1 (One (Snoc t1 a1)), t2, S2 a2)
> rsplit a f m1 (N3 t1 a1 t2 a2 t3) a3
>     | a <= a1			=  (eroz f m1, t1, eroz (Two (Cons a1 (N2 t2 a2 t3))) (S2 a3))
>     | a <= a2			=  (C f m1 (One (Snoc t1 a1)), t2, eroz (One (Cons a2 t3)) (S2 a3))
>     | otherwise		=  (C f m1 (Two (Snoc (N2 t1 a1 t2) a2)), t3, S2 a3)

%endif

> partition			:: (Ord a) => a -> OS a -> (OS a, OS a)
> partition a Nil		=  (Nil, Nil)
> partition a (Id t)		=  between (Nil, Id t) (wrap `fun` part a t) (Id t, Nil)
>   where wrap (t1, E, t2)	=  (Id t1, Id t2)

% - - - - - - - - - - - - - - - = - - - - - - - - - - - - - - - - - - - - - - -
\subsection{Margesort}
% - - - - - - - - - - - - - - - = - - - - - - - - - - - - - - - - - - - - - - -

Nicht stabil!

> merge				:: (Ord a) => OS a -> OS a -> OS a
> merge x y			=  case splitMin y of
>     NoPair			-> x
>     Pair a y'			-> x1 <> cons a (merge y' x2)
>         where (x1, x2)	=  partition a x

> margeSort			:: (Ord a) => [a] -> [a]
> margeSort			=  toList . foldm merge Nil . map single
>
> single			:: a -> OrdSequence a
> single a			=  Id (S2 a)

> naturalMargeSort		:: (Ord a) => [a] -> [a]
> naturalMargeSort		=  toList . foldm merge Nil . map fromList . upDownRunsBy (<=)

Wenn es viele gleiche Elemente gibt ... NAJA lineare Suche statt bin"arer

> merge2			:: (Ord a) => OS a -> OS a -> OS a
> merge2 x y			=  case splitMin y of
>     NoPair			-> x
>     Pair a y'			-> (x1 <> x3) <> cons a (merge2 y' x4)
>         where (x1, x2)	=  partition a x
>               (x3, x4)	=  splitWhile (== a) x2

> splitWhile p s		=  case splitMin s of
>     NoPair			-> (Nil, Nil)
>     Pair a s'
>         | p a			-> (cons a s1, s2)
>         | otherwise		-> (Nil, s)
>         where (s1, s2)	=  splitWhile p s'

% - - - - - - - - - - - - - - - = - - - - - - - - - - - - - - - - - - - - - - -
%if codeOnly

and [ x == toList (fromList x) | n <- [0 .. 500], let x = [1 .. n] ]

and [ x ++ y == toList (fromList x <> fromList y) | m <- [0 .. 100], n <- [0 .. 100], let x = [1 .. m], let y = [1 .. n] ]

[ (m, n) | m <- [0 .. 100], n <- [0 .. 100], let x = [1 .. m], let y = [m `div` 2 .. n + m `div` 2], meld x y /= toList (fromList x `merge` fromList y) ]

ordered (margeSort $ take 1500 $ random2Ints 2432 234)

and [ ordered (margeSort $ take n $ random2Ints 2432 234) | n <- [0 .. 1500] ]

> fromList []			=  Nil
> fromList as			=  Id (fromList1 as)
>
> fromList1 [a]			=  S2 a
> fromList1 (a : as)		=  incr a E (fromList1 as)

> foldm				:: (a -> a -> a) -> a -> [a] -> a
> foldm (*) e []		=  e
> foldm (*) e x			=  fst (rec (length x) x)
>     where rec 1 (a:x)		=  (a, x)
>           rec n x		=  (a * b, z)
>               where m		=  n `div` 2
>                     (a, y)	=  rec (n - m) x 
>                     (b, z)	=  rec m       y

> random2Ints           	:: Int -> Int -> [Int]
> random2Ints s1 s2
>   | s1 < 1 || s1 > 2147483562	=  error "random2Ints: Bad first seed."
>   | s2 < 1 || s2 > 2147483398	=  error "random2Ints: Bad second seed."
>   | otherwise			=  rands s1 s2

> rands                		:: Int -> Int -> [Int]
> rands s1 s2
>     | z < 1			=  z + 2147483562 : rands s1'' s2''
>     | otherwise		=  z              : rands s1'' s2''
>     where k			=  s1 `div` 53668
>           s1'			=  40014 * (s1 - k * 53668) - k * 12211
>           s1'' | s1' < 0	=  s1' + 2147483563
>                | otherwise	=  s1'
>           k'			=  s2 `div` 52774
>           s2'			=  40692 * (s2 - k' * 52774) - k' * 3791
>           s2'' | s2' < 0	=  s2' + 2147483399
>                | otherwise    =  s2'
>           z			=  s1'' - s2''

> ordered			:: (Ord a) => [a] -> Bool
> ordered []			=  True
> ordered [a]			=  True
> ordered (a1 : as @ (a2 : _))	=  a1 <= a2 && ordered as

> meld [] y			=  y
> meld x@(a:_) []		=  x
> meld x@(a:x') y@(b:y')
>     | a <= b			=  a : meld x' y
>     | otherwise		=  b : meld x  y'

Konversion in `richtige' 2-3-4 B"aume f"ur die graphische Darstellung.

> data Tree24 a			=  Void
>				|  Node2 (Tree24 a) a (Tree24 a)
>				|  Node3 (Tree24 a) a (Tree24 a) a (Tree24 a)
>				|  Node4 (Tree24 a) a (Tree24 a) a (Tree24 a) a (Tree24 a)

> class Conv tree where
>     conv			:: tree a -> Tree24 a
>
> instance Conv Empty where
>     conv E			=  Void
>
> instance (Conv tree) => Conv (Node23 tree) where
>     conv (N2 t1 a1 t2)	=  Node2 (conv t1) a1 (conv t2)
>     conv (N3 t1 a1 t2 a2 t3)	=  Node3 (conv t1) a1 (conv t2) a2 (conv t3)

> convert Nil			=  Void
> convert (Id s)		=  convert' Void s Void

> convert'			:: (Conv t) => Tree24 a -> FST1 t a -> Tree24 a -> Tree24 a
> convert' l (S2 a1) r		=  Node2 l a1 r
> convert' l (S3 a1 t1 a2) r	=  Node3 l a1 (conv t1) a2 r
> convert' l (C f m r) r'	=  convert' (link l f) m (knil r r')

> link t1 (One (Cons a1 t2))			=  Node2 t1 a1 (conv t2)
> link t1 (Two (Cons a1 (N2 t2 a2 t3)))		=  Node3 t1 a1 (conv t2) a2 (conv t3)
> link t1 (Two (Cons a1 (N3 t2 a2 t3 a3 t4)))	=  Node4 t1 a1 (conv t2) a2 (conv t3) a3 (conv t4)
>
> knil (One (Snoc t1 a1)) t2			=  Node2 (conv t1) a1 t2
> knil (Two (Snoc (N2 t1 a1 t2) a2)) t3		=  Node3 (conv t1) a1 (conv t2) a2 t3
> knil (Two (Snoc (N3 t1 a1 t2 a2 t3) a3)) t4	=  Node4 (conv t1) a1 (conv t2) a2 (conv t3) a3 t4

convert $ fromList [1 .. 12]

convert $ fromList [1 .. 17]
convert $ fromList [18 .. 24]
convert $ fromList [1 .. 17] <> fromList [18 .. 24]

convert $ fst $ partition 13 (fromList [1 .. 17] <> fromList [18 .. 24])
convert $ snd $ partition 13 (fromList [1 .. 17] <> fromList [18 .. 24])

%endif
