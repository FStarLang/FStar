(* A logical theory of integer-indexed arrays, from [0, n) *)
module Array

type seq : Type -> Type
assume val const:  a:Type -> nat -> a -> Tot (seq a)
assume val upd:    a:Type -> nat -> a -> seq a -> Tot (seq a)
assume val append: a:Type -> seq a -> seq a -> Tot (seq a)
assume val sub:    a:Type -> s:seq a -> i:nat -> j:nat -> Tot (seq a)
assume val length: a:Type -> seq a -> Tot nat
assume val sel:    a:Type -> seq a -> nat -> Tot a
assume val equal:  a:Type -> seq a -> seq a -> Tot bool

assume LengthConst: forall (a:Type) (n:nat) (x:a).                     {:pattern (length a (const a n x))}    length a (const a n x)    == n
assume LengthUpd:   forall (a:Type) (i:nat) (x:a) (s:seq a).           {:pattern (length a (upd a i x s))}    length a (upd a i x s)    == length a s
assume LengthApp:   forall (a:Type) (s1:seq a) (s2:seq a).             {:pattern (length a (append a s1 s2))} length a (append a s1 s2) == length s1 + length s2
assume LengthSub:   forall (a:Type) (s:seq a) (i:nat) (j:nat).         {:pattern (length a (sub a s i j))}    (i <= j && j <= length s) ==> length a (sub a s i j) == j - i
assume SelConst:    forall (a:Type) (n:nat) (x:a) (i:nat).             {:pattern (sel (const a n x) i)}       (i < n) ==> sel a (const a n x) i     == x
assume SelUpd1:     forall (a:Type) (s:seq a) (i:nat) (x:a).           {:pattern (sel (upd a i x s) i)}       sel a (upd a i x s) i     == x
assume SelUpd2:     forall (a:Type) (s:seq a) (i:nat) (j:nat) (x:a).   {:pattern (sel (upd a j x s) i)}       i=!=j ==> sel a (upd a j x s) i == sel a s i
assume SelAppend1:  forall (a:Type) (s1:seq a) (s2:seq a) (i:nat).     {:pattern (sel (append s1 s2) i)}      (i < length s1)  ==> sel (append s1 s2) i == sel s1 i
assume SelAppend2:  forall (a:Type) (s1:seq a) (s2:seq a) (i:nat).     {:pattern (sel (append s1 s2) i)}      (i >= length s1) ==> sel (append s1 s2) i == sel s2 i
assume SelSub:      forall (a:Type) (s:seq a) (i:nat) (j:nat) (k:nat). {:pattern (sel (sub a s i j) k)}       (k < (j - i)) ==> sel (sub a s i j) k == sel a s (i + k)
assume Extensional: forall (a:Type) (s1:seq a) (s2:seq a).             {:pattern (equal a s1 s2)}             equal a s1 s2 <==> s1==s2
assume Equals:      forall (a:Type) (s1:seq a) (s2:seq a).             {:pattern (equal a s1 s2)}             equal a s1 s2 <==> 
                            (forall (i:nat).{:pattern (sel a s1 i); (sel a s2 i)} (length s1 == length s2 
                                                                                   /\ i < length s1
                                                                                   /\ sel a s1 i == sel a s2 i))
assume TypeInj:     forall (a:Type) (b:Type) (s1:seq a) (s2:seq b). s1==s2 ==> a==b
assume AppendInj:   forall (a:Type) (b1:seq a) (b2:seq a) (c1:seq a) (c2:seq a). {:pattern (equal (append b1 b2) (append c1 c2))}
                                                                         (length b1 == length c1 /\ equal (append b1 b2) (append c1 c2))
                                                                         ==> (equal b1 c1 /\ equal b2 c2)
assume AppendSplit: forall (a:Type) (b:seq a) (i:nat). {:pattern (append (sub b 0 i) (sub b i (length b)))} equal (append (sub b 0 i) (sub b i (length b))) b

val create: a:Type -> nat -> a -> Tot (seq a)
let create (a:Type) (n:nat) (init:a) = const a n init

val index: a:Type -> s:seq a -> i:nat{(i < length s)} -> Tot a
let index (a:Type) s i   = sel a s i

val slice: a:Type -> s:seq a -> i:nat -> j:nat{(i <= j /\ j <= length s)} -> Tot (seq a)
let slice (a:Type) s i j = sub a s i j

val split: a:Type -> s:seq a -> i:nat{(0 <= i /\ i < length s)} -> Tot (seq a * seq a)
let split s i = slice s 0 i, slice s i (length s)
