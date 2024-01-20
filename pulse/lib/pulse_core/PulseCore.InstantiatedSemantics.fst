module PulseCore.InstantiatedSemantics
module Sem = PulseCore.Semantics2
module Mem = PulseCore.Memory

let laws ()
: squash (
    Sem.associative Mem.star /\
    Sem.commutative Mem.star /\
    Sem.is_unit Mem.emp Mem.star
  )
= let open Mem in
  let equiv_eq (x y:slprop)
    : Lemma (x `equiv` y <==> x == y)
          [SMTPat (x `equiv` y)]
    = introduce x `equiv` y ==> x == y
      with _h . Mem.slprop_extensionality x y
  in
  let _ : squash (Sem.associative star) =
    introduce 
        forall x y z. 
            ((x `star` y) `star` z) ==
            (x `star` (y `star` z))
    with Mem.star_associative x y z
  in
  let _ : squash (Sem.commutative star) = 
    introduce 
        forall x y.
            x `star` y == y `star` x
        with Mem.star_commutative x y
  in
  let _ : squash (Sem.is_unit emp star) =
    introduce
        forall x.
            (x `star` emp) == x /\
            (emp `star` x) == x
        with Mem.emp_unit x
  in
  ()

let state : Sem.state = {
    s = Mem.mem;
    is_full_mem = Mem.full_mem_pred;
    pred = Mem.slprop;
    emp = Mem.emp;
    star = Mem.star;
    interp = Mem.interp;
    evolves = Mem.mem_evolves;
    invariant = Mem.locks_invariant Set.empty;
    laws = laws ()
}

let stt (a:Type u#a) 
        (pre:Mem.slprop)
        (post:a -> Mem.slprop)
: Type0
= unit -> Dv (Sem.m u#2 u#a #state a pre post)

let return (#a:Type u#a) (x:a) (p:a -> Mem.slprop)
: stt a (p x) p
= fun _ -> Sem.ret x p

open Mem
let bind_stt
    (#a:Type u#a) (#b:Type u#b)
    (#pre1:slprop) (#post1:a -> slprop) (#post2:b -> slprop)
    (e1:stt a pre1 post1)
    (e2:(x:a -> stt b (post1 x) post2))
: stt b pre1 post2
= fun _ -> Sem.mbind (e1()) (fun x -> e2 x ())

let frame_stt
  (#a:Type u#a)
  (#pre:slprop) (#post:a -> slprop)
  (frame:slprop)
  (e:stt a pre post)
: stt a (pre `star` frame) (fun x -> post x `star` frame)
= fun _ -> Sem.frame frame (e())