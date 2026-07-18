module Bug3130f

(* A shrunk down version of Comparse.Tests.TacticFeatures. *)

class bytes_like (bytes:Type0) = {
  length: bytes -> nat;
}

assume val test_ei: bytes:Type0 -> {|bytes_like bytes|} -> Type0
assume val ps_test_dep_nat_e: #bytes:Type0 -> {|bytes_like bytes|} -> nat

assume
val fun_test_with_parser (bytes:Type0) {|d : bytes_like bytes|} :
  (f1: option (test_ei bytes)) ->
  [@@@ (ps_test_dep_nat_e #bytes)](u : unit) ->
  unit

noeq type test_with_parser (bytes:Type0) {|d : bytes_like bytes|} = {
  f1: option (test_ei bytes);
  [@@@ (ps_test_dep_nat_e #bytes) ]
  u : unit;
}
