module Bug2055

let repr (a:Type) (_:unit) = a

let return a (x:a) : repr a () = x

let bind a b (x: repr a _) (f:a-> repr b _) : repr b () = f x

reifiable
reflectable
layered_effect {
  ND : a:Type -> dummy:eqtype_as_type unit -> Effect
  with repr         = repr;
       return       = return;
       bind         = bind
}

let monotonic #a (wp : pure_wp a) =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> wp p1 ==> wp p2

let lift_pure_nd (a:Type) (wp:pure_wp a) (f:(eqtype_as_type unit -> PURE a wp)) :
  Pure (repr a ()) (requires (wp (fun _ -> True))) // <--- This is a lift from Tot only
                   (ensures (fun _ -> True))
  = assume (monotonic wp);
    f ()

sub_effect PURE ~> ND = lift_pure_nd

let rec blah () : ND (squash False) () = blah ()

[@@expect_failure [34]]  //Computed effect is Div, annotated effect is Tot
let blah2 () : Tot (squash False) = reify (blah ())
