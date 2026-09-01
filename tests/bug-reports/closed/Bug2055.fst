module Bug2055

let repr (a:Type) = a

let return (a:Type) (x:a) : repr a = x

let bind (a b:Type) (x: repr a) (f:a -> repr b) : repr b = f x

reifiable
reflectable
effect {
  ND with { repr; return; bind }
}

let lift_pure_nd (a:Type) (f:unit -> a) : repr a = f ()

sub_effect Tot ~> ND = lift_pure_nd

let rec blah () : ND (squash False) = blah ()

[@@expect_failure [34]]  //Computed effect is Div, annotated effect is Tot
let blah2 () : Tot (squash False) = reify (blah ())
