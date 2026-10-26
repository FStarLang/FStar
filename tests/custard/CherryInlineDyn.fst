module CherryInlineDyn

(* [@@custard_inline] on the [bind] of a class over a type constructor, used
   through a dictionary that is not a constant.  The inlined [bind] is then a
   projection returning [any], where the call it replaces returned [m b] at a
   known [m]: the continuation must return [any] too, not its old type. *)

open FStar.All
module U32 = FStar.UInt32

class monad (m: Type0 -> Type0) = {
  [@@@FStar.Attributes.custard_inline]
  bind : #a:Type0 -> #b:Type0 -> m a -> (a -> ML (m b)) -> ML (m b)
}

[@@FStar.Attributes.custard_inline]
let ( let! ) : #m:(Type -> Type) -> {| monad m |} -> #a:Type0 -> #b:Type0 -> m a -> (a -> ML (m b)) -> ML (m b) = bind

type id (a: Type0) : Type0 = a

instance monad_id : monad id = {
  bind = (fun #a #b (x: id a) (f: a -> ML (id b)) -> f x)
}

noeq type holder (m: Type0 -> Type0) = { hm : monad m; step : int -> ML (m int) }

instance holder_monad (#m: Type0 -> Type0) (h: holder m) : Tot (monad m) = h.hm

let rec steps (#m: Type0 -> Type0) (h: holder m) (n: nat) (x: int) : ML (m int) =
  if n = 0 then h.step x
  else
    let! y = h.step x in
    let! z = h.step y in
    steps h (n - 1) z

let mk_holder (k: int) : holder id = { hm = monad_id; step = (fun x -> x + k) }

let main () : ML U32.t =
  if steps #id (mk_holder 1) 2 0 = 5 then 0ul else 1ul
