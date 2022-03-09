module Bug2478.Alt

assume
val bytes_like (bytes:Type0)
  : Type0

assume
val test_type (bytes:Type0)
              (pf : bytes_like bytes )
              (a:Type0)
  : Type0


assume
val bind (#a:Type0)
         (#b:(a -> Type0))
         (#bytes:Type0)
         (#pf: bytes_like bytes)
         (tt_a:test_type bytes pf a)
         (tt_b:(xa:a -> test_type bytes pf (b xa)))
 : (test_type bytes pf (xa:a&(b xa)))

assume
val ps_bytes (#bytes:Type0) (#pf: bytes_like bytes )
  : test_type bytes pf bytes

(* works fine *)
let test2 (bytes:Type0) (#pf: bytes_like bytes ): (test_type bytes pf (x0:bytes & (x1:bytes & bytes))) =
    ps_bytes;;
    ps_bytes;;
    ps_bytes

(* now, add an indirection *)
let key (bytes:Type0) (pf: bytes_like bytes) = bytes

assume
val ps_key (#bytes:Type0) (#pf: bytes_like bytes )
  : test_type bytes pf (key bytes pf)

(* Works with a non-dependent bind *)
assume
val bind2 (#a:Type0)
         (#b:Type0)
         (#bytes:Type0)
         (#pf: bytes_like bytes)
         (tt_a:test_type bytes pf a)
         (tt_b:(a -> test_type bytes pf b))
 : (test_type bytes pf (a&b))

let test_non_dep (bytes:Type0) (#pf: bytes_like bytes ): (test_type bytes pf (bytes & (bytes & bytes))) =
    bind2 ps_key (fun _ ->
    bind2 ps_key (fun _ ->
    ps_key))

(* But dependent bind with ps_key loops *)
let test4 (bytes:Type0) (pf:bytes_like bytes) : (test_type bytes pf (x0:bytes & (x1:bytes & bytes))) =
    bind (ps_key #bytes #_) (fun (x0:bytes) ->
    bind (ps_key #_ #_) (fun x1 ->
    ps_key #_ #_))
