module Bug812

let ex (a:Type) = unit -> M (option a)

val return_ex : (a:Type) -> (x:a) -> Tot (ex a)
let return_ex a x = fun _ -> Some x

val bind_ex : (a:Type) -> (b:Type) -> (f:ex a) -> (g:a -> Tot (ex b)) -> Tot (ex b)
let bind_ex a b f g = fun _ ->
  let r = f () in
  match r with
  | None -> None
  | Some x -> g x ()

let raise_ex (a:Type) (e:exn) : Tot (ex a) = fun _ -> None

reifiable reflectable new_effect {
  XEXN : (a:Type) -> Effect
  with repr     = ex
     ; bind     = bind_ex
     ; return   = return_ex
     ; raise   = raise_ex
}

type arg =
| Bool | Int
