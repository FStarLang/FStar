module Bug2057

type unit : Type = unit

type repr (a:Type) (_:unit) = a

let return (a:Type) (x:a) : repr a () = x
let bind (a:Type) (b:Type) (f:repr a ()) (g:a -> repr b ()) : repr b () = g f

layered_effect {
  M : Type -> unit -> Effect
  with repr = repr;
       return = return;
       bind = bind
}

let lift_PURE_M (a:Type) (wp:pure_wp a) (f:unit -> PURE a wp)
  : Pure (repr a ()) (requires wp (fun _ -> True)) (ensures fun _ -> True)
  = FStar.Monotonic.Pure.wp_monotonic_pure ();  
    f ()

sub_effect PURE ~> M = lift_PURE_M

assume val f (_:unit) : M int ()

(*
 * Expected type "Effect"; but "Bug2057.M Prims.int" has type "_: Bug2057.unit -> Prims.Tot Effect"
 *)
[@@ expect_failure [12]]
let g () : M int = f ()

(*
 * Example from #1861
 *)

[@@expect_failure [12]]
let test : (f : unit -> Exn unit _ _) -> unit =
    fun (f : unit -> Exn unit) -> ()
