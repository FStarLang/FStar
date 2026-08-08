module Bug2066

type repr (a:Type) = unit -> a

let return (a:Type) (x:a) : repr a = fun _ -> x

let bind (a:Type) (b:Type) (f:repr a) (g:a -> repr b) : repr b
  = fun _ -> let x = f () in (g x) ()

effect {
  M with { repr; return; bind }
}

let lift_Tot_M (a:Type) (f:unit -> Tot a) : repr a = fun _ -> f ()

sub_effect PURE ~> M = lift_Tot_M

(* A lift must have type [(a:Type) -> (unit -> src a) -> repr a] *)
[@@expect_failure]
sub_effect GHOST ~> M = return
