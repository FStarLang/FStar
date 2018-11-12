module Bug116

type env = int -> Tot bool

assume val extend : env -> int -> Tot env

noeq type rtyping : env -> int -> Type =
  | TyAbs : #g:env ->
            x:int ->
            #e1:int ->
            rtyping (extend g x) e1 ->
            rtyping g 42

val free_in_context : e:int -> g:env -> h:rtyping g e -> Tot unit
let rec free_in_context _ _ h =
  match h with
  | TyAbs _ h1 -> ()
