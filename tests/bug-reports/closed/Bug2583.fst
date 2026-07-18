module Bug2583

assume val bytes_like: Type0 -> Type0

assume val parser_serializer: Type0 -> Type0

type key (bytes:Type0) (pf:bytes_like bytes) (_:unit) = bytes
//assume val key: bytes:Type0 -> pf:bytes_like bytes -> unit -> Type0

assume val ps_unit: parser_serializer unit
assume val ps_key: #bytes:Type0 -> #pf:bytes_like bytes -> parser_serializer (key bytes pf ())

assume val bind: #a:Type0 -> #b:(a -> Type0) -> ps_a:parser_serializer a -> ps_b:(xa:a -> parser_serializer (b xa)) -> parser_serializer (dtuple2 a b)

assume val isomorphism:
  #a:Type0 -> b:Type0 ->
  ps_a:parser_serializer a ->
  a_to_b:(a -> b) ->
  b_to_a:(b -> a) ->
  parser_serializer b

noeq type test_record (bytes:Type0) (pf:bytes_like bytes) = {
  f1: unit;
  f2: key bytes pf ();
  f3: key bytes pf ();
}

// This definition makes F* loop, even in lax mode
val ps_test_record: #bytes:Type0 -> #pf:bytes_like bytes -> parser_serializer (test_record bytes pf)
let ps_test_record #bytes #pf =
  isomorphism (test_record bytes pf)
    (
      ps_unit;;
      ps_key;;
      ps_key
    )
    (fun (|f1, (|f2, f3|)|) -> {f1; f2; f3})
    (fun x -> (|x.f1, (|x.f2, x.f3|)|))

// Workaround:
// - Replace one of the `ps_key` with `ps_key #bytes`

// How to make it work?
// - Replace `type key ...` with the `assume val key: ...` just below
// - Remove `f1` (and update `ps_test_record`)
// - Change `f2` or `f3` type to `unit` (and update `ps_test_record`)
// - Make `f1` with type `key ...` and `f2` or `f3` with type `unit`
// - Remove the `(_:unit)` in the definition of `key`, and update the rest
// - Remove the `pf` in the definition of `key`, and update the rest
// - Remove the `a_to_b` function in `isomorphism`
// - Swap the `a_to_b` and `b_to_a` arguments in `isomorphism` (very surprising!)

// How to minimize further
// - Remove the `b_to_a` argument in `isomorphism`
//   (kept it because it works if we swap `a_to_b` and `b_to_a`)
