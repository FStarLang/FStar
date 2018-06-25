module FStar.DM4F.Id

let id (a:Type) = unit -> M a
let return_id (a:Type) (x:a) : id a = fun () -> x

// TODO : elaborate f (x ()) to let __x = x () in f __x ?
// TODO : Not exactly sure why let x = x () in f x fails...
let bind_id (a:Type) (b:Type) (x:id a) (f:(a -> id b)) : id b =
  fun () ->
    let x = x () in
    f x ()


total reifiable reflectable new_effect {
  ID : a:Type -> Effect
  with repr   = id
     ; bind   = bind_id
     ; return = return_id
  }
