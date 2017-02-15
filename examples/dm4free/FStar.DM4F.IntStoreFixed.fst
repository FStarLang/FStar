module FStar.DM4F.IntStoreFixed

open FStar.DM4F.Heap.IntStoreFixed

(* TODO : Try to use [either a exn] instead of [option] *)
type int_store (a:Type) = heap -> M (a * heap)
let return_is (a:Type) (x:a) : int_store a = fun store -> x, store
let bind_is (a b : Type) (x:int_store a) (f: a -> int_store b) : int_store b =
  fun store ->
    let (z, store') = x store in
    f z store'

let get () : int_store heap = fun store -> store, store
let put s : int_store unit = fun _ -> (), s

total reifiable reflectable new_effect_for_free {
  INT_STORE : a:Type -> Effect
  with repr   = int_store
     ; bind   = bind_is
     ; return = return_is
  and effect_actions
       get   = get
     ; put    = put
}

effect IntStore (a:Type) (pre:INT_STORE?.pre) (post: heap -> a -> heap -> GTot Type0) =
  INT_STORE a (fun l0 p -> pre l0 /\ (forall x l1. pre l0 /\ post l0 x l1 ==> p (x, l1)))

effect IS (a:Type) =
  INT_STORE a (fun (l0:heap) (p:((a * heap) -> Type0)) -> forall (x:a). p (x, l0))

effect ISNull (a:Type) =
  INT_STORE a (fun (l0:heap) (p:((a * heap) -> Type0)) -> forall (x:a * heap). p x)
(* TODO : having a in Type *and* reifiable induces a Failure("Universe variable not found") *)
(* whenever we try to normalize-reify it (see below in xxx for instance) *)

reifiable
let read (i:id)
  : INT_STORE int (fun s0 p -> p (index s0 i, s0))
=
  let store = IS?.get () in
  index store i

reifiable
let write (i:id) (x:int)
  : INT_STORE unit (fun s0 p -> p ((), upd s0 i x))
=
  let store = IS?.get () in
  IS?.put (upd store i x)


(* let read_does_not_write_lemma (h:heap) (x:id) *)
(*   : Lemma (requires True) *)
(*       (ensures (snd (reify (read x) h) == h)) *)
(*       [SMTPat (snd (reify (read x) h))] *)
(* = () *)

unfold
let (!) = read

unfold
let op_Colon_equals = write

(* let refine_st (#a:Type) *)
(*               (#b:Type) *)
(*               (#pre : a -> Tot INT_STORE?.pre) *)
(*               (#post : a -> Tot (heap -> b -> heap -> Tot Type0)) *)
(*               ($f :(x:a -> IntStore b (pre x) (post x))) *)
(*               (x:a) *)
(*   : IntStore b (pre x) (fun h0 z h1 -> pre x h0 /\ *)
(*                                     reify (f x) h0 == (z, h1) /\ *)
(*                                     post x h0 z h1) *)
(*   = let g (h0:heap) *)
(*       : Pure (b * heap) *)
(*              (pre x h0) *)
(*              (fun (z,h1) -> pre x h0 /\ *)
(*                        reify (f x) h0 == (z, h1) /\ *)
(*                        post x h0 z h1) *)
(*       = reify (f x) h0 *)
(*     in *)
(*     IntStore?.reflect g *)
