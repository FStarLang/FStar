module VecErased
open FStar.Ghost
open FStar.WellFoundedRelation

assume
val pull (f: 'a -> GTot 'b) : GTot (g:('a -> 'b) { forall x. f x == g x })

let wfr_erased (a:Type)
  : GTot (wfr_t (erased a))
  = inverse_image_to_wfr #(erased a) #a (fun x y -> default_relation (reveal x) (reveal y)) (pull (reveal #a)) (default_wfr a)

let erased_precedes (a:Type) (x:erased a) (y:erased a)
  : Lemma 
    (requires reveal x << reveal y)
    (ensures (wfr_erased a).decreaser x << (wfr_erased a).decreaser y)
  = ()
                                                                         

assume Erased_precedes: 
  forall (a:Type) (x y: erased a).  reveal x << reveal y ==> x << y

noeq
type vec a : nat -> Type = 
  | Nil : vec a 0
  | Cons : #n:erased nat -> hd:a -> tl:vec a n -> vec a (n + 1)

let rec append (#a:Type) (#n #m:erased nat)
               (v0:vec a n) (v1:vec a m)
  : Tot (vec a (n + m))
  = match v0 with  
    | Nil -> v1
    | Cons hd tl -> Cons hd (append tl v1)
