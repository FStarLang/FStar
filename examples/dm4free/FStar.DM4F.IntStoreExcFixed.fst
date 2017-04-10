module FStar.DM4F.IntStoreExcFixed

open FStar.DM4F.Heap.IntStoreFixed

(* TODO : Try to use [either a exn] instead of [option] *)
type int_store_exc (a:Type) = heap -> M (option a * heap)
let return_is (a:Type) (x:a) : int_store_exc a = fun store -> Some x, store
let bind_is (a b : Type) (x:int_store_exc a) (f: a -> int_store_exc b) : int_store_exc b =
  fun store ->
  let (z, store') = x store in
    match z with
    | None -> None, store'
    | Some xa -> f xa store'

let get () : int_store_exc (heap) = fun store -> Some store, store
let put s : int_store_exc unit = fun _ -> Some (), s

(* DM4F does not handle polymorphic types yet so we go around this limitation *)
(* by returning an inhabitant of False and define a second polymorphic raise_ afterwards *)
let raise_impl () : int_store_exc False = fun store -> None, store

total reifiable reflectable new_effect {
  INT_STORE_EXC : a:Type -> Effect
  with repr   = int_store_exc
     ; bind   = bind_is
     ; return = return_is
     ; get   = get
     ; put    = put
     ; raise_ = raise_impl
}

effect IntStoreExc (a:Type) (pre:INT_STORE_EXC?.pre) (post: heap -> option a -> heap -> GTot Type0) =
  INT_STORE_EXC a (fun l0 p -> pre l0 /\ (forall x l1. pre l0 /\ post l0 x l1 ==> p (x, l1)))

effect ISE (a:Type) =
  INT_STORE_EXC a (fun (l0:heap) (p:((option a * heap) -> Type0)) -> forall (x:a). p (Some x, l0))

effect ISENull (a:Type) =
  INT_STORE_EXC a (fun (l0:heap) (p:((option a * heap) -> Type0)) -> forall (x:option a * heap). p x)


let raise_ (#a:Type) ()
  : IntStoreExc a (fun _ -> True) (fun l0 x l1 -> l0 == l1 /\ None? x)
= let x = INT_STORE_EXC?.raise_ () in begin match x with end


let read (i:id)
  : INT_STORE_EXC int (fun s0 p -> p (Some (index s0 i), s0))
=
  let store = ISE?.get () in
  index store i


let write (i:id) (x:int)
  : INT_STORE_EXC unit (fun s0 p -> p (Some (), upd s0 i x))
=
  let store = ISE?.get () in
  ISE?.put (upd store i x)

open FStar.DM4F.IntStoreFixed

(* unfold *)
(* let lift_int_store_int_store_exc_wp (a:Type) (wp:INT_STORE?.wp a) : INT_STORE_EXC?.wp a = *)
(*   fun (h0:heap) (p:INT_STORE_EXC?.post a) -> wp h0 (fun r -> p (Some (fst r), snd r)) *)

(* #set-options "--admit_smt_queries true" *)
(* unfold *)
(* let lift_int_store_int_store_exc (a:Type) (wp:INT_STORE?.wp a) (e:INT_STORE?.repr a wp) *)
(*   : INT_STORE_EXC?.repr a (lift_int_store_int_store_exc_wp a wp) *)
(* = fun h0 -> let (x,h1) = e h0 in Some x, h1 *)
(* #set-options "--admit_smt_queries false" *)


(* Trying to have a refiable lift from IntStoreFixed to IntStoreExcFixed *)
sub_effect INT_STORE ~> INT_STORE_EXC {
  (* lift_wp = lift_int_store_int_store_exc_wp ; *)
  lift = fun (a:Type) (e:int_store a) ->
           (fun h0 -> let (x,h1) = e h0 in Some x, h1) <: int_store_exc a
}
