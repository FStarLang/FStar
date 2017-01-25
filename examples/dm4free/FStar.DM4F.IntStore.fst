module FStar.DM4F.IntStore

open FStar.DM4F.IntStoreAux

type int_store (a:Type) = list int -> M (option a * list int)
let return_is (a:Type) (x:a) : int_store a = fun store -> Some x, store
let bind_is (a b : Type) (x:int_store a) (f: a -> int_store b) : int_store b =
  fun store ->
  let (z, store') = x store in
    match z with
    | None -> None, store'
    | Some xa -> f xa store'

let get () : int_store (list int) = fun store -> Some store, store
let put s : int_store unit = fun _ -> Some (), s
let raise_impl () : int_store False = fun store -> None, store

total reifiable reflectable new_effect_for_free {
  INT_STORE : a:Type -> Effect
  with repr   = int_store
     ; bind   = bind_is
     ; return = return_is
  and effect_actions
       get   = get
     ; put    = put
     ; raise_ = raise_impl
}

effect IntStore (a:Type) (pre:INT_STORE?.pre) (post: list int -> option a -> list int -> GTot Type0) =
  INT_STORE a (fun l0 p -> pre l0 /\ (forall x l1. pre l0 /\ post l0 x l1 ==> p (x, l1)))

effect IS (a:Type) =
  INT_STORE a (fun (l0:list int) (p:((option a * list int) -> Type0)) -> forall (x:(option a * list int)). p x)

let raise_ (#a:Type) ()
  : IntStore a (fun _ -> True) (fun l0 x l1 -> l0 == l1 /\ None? x)
= let x = INT_STORE?.raise_ () in begin match x with end

reifiable
let read (r:index) =
  let store = INT_STORE?.get () in
  match nth_opt r store with
  | None -> raise_ ()
  | Some x -> x

reifiable
let write (r:index) (x:int) =
  let store = INT_STORE?.get () in
  match set_nth_opt [] r store x with
  | None -> raise_ ()
  | Some store' -> INT_STORE?.put store'
