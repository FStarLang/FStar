module FStar.Exn

(* providing the signature of raise, that is implemented natively in FStar_Exn.ml as primitive raise *)
assume
val raise: e: exn -> Exn 'a (requires True) (ensures (fun r -> r == E e))

