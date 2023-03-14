module ParametricST

type repr (a:Type) (s:Type0) = s -> a & s
let return a x s : repr a s = fun s -> x, s
let bind a b s (f:repr a s) (g:a -> repr b s) : repr b s =
  fun s ->
  let x, s = f s in
  (g x) s
reifiable
reflectable
effect {
  ST (a:Type) ([@@@ effect_param] s:Type0) with {repr;return;bind}
}
let lift_PURE_ST a wp s (f:unit -> PURE a wp)
  : Pure (repr a s) (requires wp (fun _ -> True)) (ensures fun _ -> True) =

  fun s -> f (), s
sub_effect PURE ~> ST = lift_PURE_ST

let get #s () : ST s s = ST?.reflect (fun s -> s, s)
let put #s (v:s) : ST unit s = ST?.reflect (fun _ -> (), v)
let incr () : ST unit int =
  let n = get () in
  put (n+1)

let main =
  let _, n = reify (incr ()) 1 in
  FStar.IO.print_string (FStar.Printf.sprintf "Output: %d\n" n)
