module FStar.Exn

(* providing the signature of raise, that is implemented natively in FStar_Exn.ml as primitive raise *)
assume val raise: exn -> Ex 'a       (* TODO: refine with the Exn monad *)
