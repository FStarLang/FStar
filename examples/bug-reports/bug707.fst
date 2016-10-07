module FStar.Bug707

(* NOTE: Move the file to FStar.Bug707.fst before running, or
 * you will hit bug #705 *)

let stexn a =
  int -> M (option a * int)

val return : (a:Type) -> (x:a) -> stexn a
let return a x = fun s -> Some x, s

val bind : (a:Type) -> (b:Type) ->
           (f:stexn a) -> (g:a -> stexn b) -> stexn b
let bind a b f g =
  fun s0 ->
    let tmp = f s0 in
    match tmp with
    | None, s1_fail -> None, s1_fail
    | Some r, s1_proceed -> g r s1_proceed

let get (_:unit) : stexn int =
        fun s0 -> (Some s0, s0)

let put (s:int) : stexn unit =
        fun _ -> (Some (), s)

(* Using `stexn unit`, or any other concrete type, works *)
let raise (a:Type) : stexn a =
        fun s -> (None, s)

reifiable reflectable new_effect_for_free {
  STEXN: a:Type -> Effect
  with repr    = stexn
     ; return  = return
     ; bind    = bind
  and effect_actions
       get     = get
     ; put     = put
     ; raise   = raise
}
