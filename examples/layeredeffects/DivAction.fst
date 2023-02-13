module DivAction

let repr (a : Type) : Type = unit -> Dv a

let return (a : Type) (x : a) : repr a =
  fun () -> x

let bind (a b : Type) (v : repr a) (f : (a -> repr b)) : repr b  =
  fun () -> f (v ()) ()

total
reifiable
reflectable
effect {
  ID (a:Type)
  with {repr; return; bind}
}

let lift_pure_nd (a:Type) (wp:pure_wp a) (f:unit -> PURE a wp) :
  Pure (repr a) (requires (wp (fun _ -> True)))
                (ensures (fun _ -> True))
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    fun _ ->
    let r = f () in
    r

sub_effect PURE ~> ID = lift_pure_nd

val fix : #a:_ -> #b:_ -> ((a -> ID b) -> (a -> ID b)) -> (a -> ID b)
let fix #a #b f =
  let reified : (a -> Dv b) -> (a -> Dv b) =
    fun g x ->
      let reflected_g : (a -> ID b) =
        fun x -> ID?.reflect (fun () -> g x)
      in
      reify (f reflected_g x) ()
  in
  let rec fixed : (a -> Dv b) =
    fun x -> reified fixed x
  in
  let reflected : a -> ID b =
    fun x -> ID?.reflect (fun () -> fixed x)
  in
  reflected

[@@expect_failure]
let rec bad_div (x:int) : ID int = bad_div x

let good_div : int -> ID int = fix #int #int (fun f x -> f x)

let test (x:int) : Dv int = reify (good_div x) ()
