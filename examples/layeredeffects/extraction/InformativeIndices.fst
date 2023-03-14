module InformativeIndices

type repr (a:Type) (n:nat) = a
let return a x : repr a 1 = x
let bind a b n1 n2 (f:repr a n1) (g:a -> repr b n2) : repr b (n1+n2) = g f
reifiable
reflectable
effect {
  M (a:Type) (n:nat) with {repr;return;bind}
}
let lift_PURE_M (a:Type) (wp:pure_wp a) (f:unit -> PURE a wp)
  : Pure (repr a 1) (requires wp (fun _ -> True)) (ensures fun _ -> True) =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
  f ()
sub_effect PURE ~> M = lift_PURE_M

let ret (#a:Type) (x:a) : M a 1 = M?.reflect x

let test () : M int 2 =
  let x = ret 1 in
  ret x
