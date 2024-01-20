module PulseCore.InstantiatedSemantics
module Sem = PulseCore.Semantics2
module Mem = PulseCore.Memory
open Mem

let laws ()
: squash (
    Sem.associative star /\
    Sem.commutative star /\
    Sem.is_unit emp star
  )
= let equiv_eq (x y:slprop)
    : Lemma (x `equiv` y <==> x == y)
          [SMTPat (x `equiv` y)]
    = introduce x `equiv` y ==> x == y
      with _h . slprop_extensionality x y
  in
  let _ : squash (Sem.associative star) =
    introduce 
        forall x y z. 
            ((x `star` y) `star` z) ==
            (x `star` (y `star` z))
    with star_associative x y z
  in
  let _ : squash (Sem.commutative star) = 
    introduce 
        forall x y.
            x `star` y == y `star` x
        with star_commutative x y
  in
  let _ : squash (Sem.is_unit emp star) =
    introduce
        forall x.
            (x `star` emp) == x /\
            (emp `star` x) == x
        with emp_unit x
  in
  ()

let state0 (e:inames) : Sem.state = {
    s = mem;
    is_full_mem = full_mem_pred;
    pred = slprop;
    emp = emp;
    star = star;
    interp = interp;
    evolves = mem_evolves;
    invariant = locks_invariant e;
    laws = laws ()
}

let state : Sem.state = state0 Set.empty

(* The type of general-purpose computations *)
let stt (a:Type u#a) 
        (pre:slprop)
        (post:a -> slprop)
: Type0
= unit -> Dv (Sem.m u#2 u#a #state a pre post)

let return (#a:Type u#a) (x:a) (p:a -> slprop)
: stt a (p x) p
= fun _ -> Sem.ret x p

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

(* The type of atomic actions *)
module M = Pulse.MonotonicStateMonad
let action
    (a:Type u#a)
    (except:inames)
    (pre:slprop)
    (post:a -> slprop)
= frame:slprop ->
  Sem.mst_sep_aux u#2 u#a state
    (inames_ok except)
    (state0 except).invariant
    a 
    (pre `star` frame)
    (fun x -> post x `star` frame)

let return_action
    (#a:Type u#a)
    (#except:inames)
    (#post:a -> slprop)
    (x:a)
: action a except (post x) post
= fun frame -> M.weaken (M.return x)

let bind_action
     (#a:Type u#a)
     (#b:Type u#b)
     (#except:inames)
     (#pre1 #post1 #post2:_)
     (f:action a except pre1 post1)
     (g:(x:a -> action b except (post1 x) post2))
: action b except pre1 post2
= fun frame -> M.weaken (M.bind (f frame) (fun x -> g x frame))

let frame_action
     (#a:Type u#a)
     (#b:Type u#b)
     (#except:inames)
     (#pre #post #frame:_)
     (f:action a except pre post)
: action a except (pre `star` frame) (fun x -> post x `star` frame)
= fun frame' -> f (frame `star` frame')

let stt_of_action (#a:Type u#2) #pre #post (m:action a Set.empty pre post)
: stt a pre post
= let step (frame:slprop)
    : Sem.mst_sep state a (pre `star` frame) (fun x -> post x `star` frame)
    = M.weaken (m frame)
  in
  let action : Sem.action state a = {pre=pre; post=post; step} in
  let m : Sem.m a pre post = Sem.act action in
  fun _ -> m

module MST = Pulse.MonotonicStateMonad

let mem_action_as_action
        (a:Type u#a)
        (except:inames)
        (req:slprop)
        (ens: a -> slprop)
        (act:Mem.action_except a except req ens)
: action a except req ens
= fun frame ->
    let thunk
      : unit -> MstTot a except req ens frame (fun _ -> True) (fun _ _ _ -> True)
      = fun _ -> act frame
    in
    MST.of_msttotal _ _ _ _ thunk

let action_as_mem_action
        (a:Type u#a)
        (except:inames)
        (pre:slprop)
        (post: a -> slprop)
        (act:action a except pre post)
: Mem.action_except a except pre post
= fun frame ->
    let m
      : MST.mst state.evolves
                a 
                (fun s0 -> 
                    inames_ok except s0 /\
                    interp ((pre `star` locks_invariant except s0) `star` frame) s0)
                (fun s0 x s1 ->
                    inames_ok except s1 /\
                    interp ((post x `star` locks_invariant except s1) `star` frame) s1 /\
                    (forall (f_frame:mprop frame). f_frame (core_mem s0) == f_frame (core_mem s1)))
      = magic() //MST.weaken (act frame)
    in
    MST.to_msttotal _ _ _ _ m
    // MST.to_msttotal _ _ _ _ m
