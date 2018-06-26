module Test.ReifyNBE

/// This is a copy of FStar.DM4F.Id

let id (a:Type) = unit -> M a
let return_id (a:Type) (x:a) : id a = fun () -> x
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

////////////////////////////////////////////////////////////////////////////////
#reset-options

let test1 (a:Type) (y:a) =
    assert (norm [nbe; delta] (reify (ID?.reflect (return_id a y)) ()) == y)
