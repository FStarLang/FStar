module FStar.Seq.Derived
open FStar.Seq.Base

/// s `indexable` j: j is within bounds of s
let indexable
    (#a:Type)
    (s:seq a)
    (j:int)
  : Type0
  = 0 <= j /\
    j < length s

let head 
    (#a:Type)
    (s:seq a{length s > 0})
  : Tot a 
  = s.(0)

let tail 
    (#a:Type)
    (s:seq a{length s > 0})
  : Tot (seq a)
  = sub s 1 (length s)

let last 
    (#a:Type)
    (s:seq a{length s > 0})
  : Tot a
  = s.(length s - 1)

let split
    (#a:Type)
    (s:seq a)
    (i:nat{0 <= i /\ i <= length s})
  : Tot (seq a * seq a)
  = sub s 0 i, sub s i (length s)

let cons 
    (#a:Type)
    (x:a)
    (s:seq a)
  : Tot (seq a)
  = create 1 x @| s

let snoc
    (#a:Type)
    (s:seq a)
    (x:a)
  : Tot (seq a)
  = s @| create 1 x

let un_snoc
    (#a:Type)
    (s:seq a{length s <> 0})
  : Tot (r:(seq a * a){s == snoc (fst r) (snd r)})
  = let s', a = split s (length s - 1) in
    assert (equal (snoc s' (index a 0)) s);
    s', index a 0

let rec count 
    (#a:eqtype)
    (x:a)
    (s:seq a)
  : Tot nat (decreases (length s))
  = if length s = 0 then 0
    else if head s = x
    then 1 + count x (tail s)
    else count x (tail s)

let permutation
    (a:eqtype)
    (s1:seq a)
    (s2:seq a)
   : Type
   = forall i. count i s1 == count i s2

let mem
    (#a:eqtype)
    (x:a)
    (s:seq a)
  : Tot bool
  = count x s > 0

let swap
    (#a:Type)
    (s:seq a)
    (i:nat{i<length s})
    (j:nat{j<length s})
  : Tot (seq a)
  = (s.(j) <- s.(i)).(i) <- s.(j)

let rec sorted
    (#a:Type)
    (f:(a -> a -> Tot bool))
    (s:seq a)
  : Tot bool (decreases (length s))
  = if length s <= 1
    then true
    else f (head s) s.(1) && sorted f (tail s)

/// replaces the [i,j) sub-sequence of s1 with the corresponding sub-sequence of s2
let splice
    (#a:Type)
    (s1:seq a)
    (i:nat)
    (s2:seq a{length s1=length s2})
    (j:nat{i <= j /\ j <= (length s2)})
  : Tot (seq a)
  = sub s1 0 i @| (sub s2 i j @| sub s1 j (length s1))

/// find_l f l: find the left-most element in l that satisfies f
let rec find_l 
    (#a:Type)
    (f:(a -> Tot bool))
    (l:seq a)
  : Tot (o:option a{Some? o ==> f (Some?.v o)}) (decreases (length l))
  = if length l = 0 then None
    else if f (head l) then Some (head l)
    else find_l f (tail l)

/// find_r f l: find the right-most element in l that satisfies f
let rec find_r
    (#a:Type)
    (f:(a -> Tot bool))
    (l:seq a)
  : Tot (o:option a{Some? o ==> f (Some?.v o)}) (decreases (length l))
  = if length l = 0 then None
    else let prefix, last = un_snoc l in 
         if f last then Some last
         else find_r f prefix

let for_all
    (#a:Type)
    (f:(a -> Tot bool))
    (l:seq a)
  : Tot bool
  = None? (find_l (fun i -> not (f i)) l)

let rec to_list
   (#a:Type)
   (s:seq a)
  : Tot (list a) (decreases (length s))
  = if length s = 0 then []
    else head s::to_list (tail s)

