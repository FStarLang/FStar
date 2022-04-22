module Bug2478

class bytes_like (bytes:Type0) = {
  toto: unit
}

assume new type test_type (bytes:Type0) {|bytes_like bytes|} (a:Type)
assume val bind: #a:Type -> #b:(a -> Type) -> #bytes:Type0 -> {| bytes_like bytes |} -> tt_a:test_type bytes a -> tt_b:(xa:a -> test_type bytes (b xa)) -> (test_type bytes (xa:a&(b xa)))
assume val tt_bytes: #bytes:Type0 -> {|bytes_like bytes|} -> test_type bytes bytes

// Works fine
let tt_pair2 (bytes:Type0) {|bytes_like bytes|}: (test_type bytes (x1:bytes & bytes)) =
    tt_bytes;;
    tt_bytes

// This hangs.
// If we remove the `bytes` indirection, it works
// If we change the dependant pair to a non-dependant pair, it works
// If we remove the typeclass, it works

let tt_pair3 (bytes:Type0) {|bytes_like bytes|}: Tot (test_type bytes (x1:bytes & (x2:bytes & bytes))) =
  tt_bytes;;
  tt_bytes;;
  tt_bytes

let key0 (bytes:Type0) (#pf: bytes_like bytes) = bytes

// assume
// val ps_key0: #bytes:Type0 -> (#pf: bytes_like bytes ) -> test_type bytes (key0 bytes #pf)

// //#push-options "--debug Bug2478 --debug_level Rel,RelCheck,Tac --lax"
// let ps_pair3_0 (bytes:Type0) (#pf: bytes_like bytes ): (test_type bytes (x0:bytes & (x1:bytes & bytes))) =
//     ps_key0 #_ #_;;
//     ps_key0 ;;
//     ps_key0

let key (bytes:Type0) {|bytes_like bytes|} = bytes


assume val ps_key: #bytes:Type0 -> {|bytes_like bytes|} -> test_type bytes (key bytes)

// #push-options "--debug Bug2478 --debug_level Rel,RelCheck,Tac --lax"
let ps_pair3 (bytes:Type0) {| pf: bytes_like bytes|}: (test_type bytes (x0:bytes & (x1:bytes & bytes))) =
    ps_key #_ #_;;
    ps_key;;
    ps_key
