module FStar.DM4F.IntStore

open FStar.DM4F.IntStoreAux

type int_store (a:Type) = list int -> M (option (a * list int))
let return_is (a:Type) (x:a) : int_store a = fun store -> Some (x, store)
let bind_is (a b : Type) (x:int_store a) (f: a -> int_store b) : int_store b =
  fun store ->
  let z = x store in
    match z with
    | None -> None
    | Some (xa, store') -> f xa store'

let get (r:index) : int_store int = fun store ->
  match nth_opt r store with
  | None -> None
  | Some x -> Some (x, store)

let put (r:index) (x:int) : int_store unit = fun store ->
  match set_nth_opt [] r store x with
  | None -> None
  | Some store' -> Some ((), store')

let raise_ () : int_store False = fun store ->
  None

total reifiable reflectable new_effect_for_free {
  INT_STORE : a:Type -> Effect
  with repr   = int_store
     ; bind   = bind_is
     ; return = return_is
  and effect_actions
       get   = get
     ; put    = put
     ; raise_ = raise_
}
