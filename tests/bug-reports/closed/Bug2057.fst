module Bug2057

type repr (a:Type) = a

let return (a:Type) (x:a) : repr a = x
let bind (a:Type) (b:Type) (f:repr a) (g:a -> repr b) : repr b = g f

effect {
  M with { repr; return; bind }
}

let lift_PURE_M (a:Type) (f:unit -> a) : repr a = f ()

sub_effect PURE ~> M = lift_PURE_M

assume val f (_:unit) : M int

let g () : M int = f ()
