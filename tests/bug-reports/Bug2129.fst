module Bug2129

let m (a:Type u#aa) () : Type u#aa = unit -> Tot  a

let return (a:Type) (x:a) : m a () = fun () -> x

let bind (a b : Type) (c : m a ()) (f : a -> m b ()) : m b () =
  fun () -> f (c ()) ()
  
let subcomp (a:Type) (u:eqtype_as_type unit) (f : m a u) : m a () = f

let if_then_else (a:Type) (f : m a ()) (g : m a ()) (b : bool) : Type = m a ()

[@@allow_informative_binders]
reifiable
reflectable
layered_effect {
  M : a:Type -> eqtype_as_type unit -> Effect
  with
  repr         = m;
  return       = return;
  bind         = bind;
  subcomp      = subcomp;
  if_then_else = if_then_else
}

let lift_pure_gtd (a:Type)
                  (f : eqtype_as_type unit -> Tot a)
                 : m a ()
 = fun () -> f ()

sub_effect PURE ~> M = lift_pure_gtd

let test () : M int () = M?.reflect (fun () -> 42)

[@@expect_failure [187]]
let test_call = test ()

