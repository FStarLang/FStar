module FStar.Erase.Exn

module E = FStar.DM4F.Exceptions


let catch_all_pre_post (#a:Type) (#pre:Type0) (#post:E.EXN?.post a) ($f:unit -> E.Exn a pre post) : Type0 =
  pre ==> Inl? (reify (f ()) ())

let erase_exn (#a:Type) (#pre:Type0) (#post:E.EXN?.post a) (f:unit -> E.Exn a pre post) ()
  : Pure a (requires (catch_all_pre_post #a #pre #post f /\ pre))
    (ensures (fun x -> pre /\ post (Inl x)))
= Inl?.v (reify (f ()) ())

let null_post = fun _ -> True
let pure_post p = function |Inr _ -> False | Inl x -> p x

let pure_st_null #a #b : Lemma (forall p (x:either a b). pure_post p x ==> null_post x) = ()

let catch_all (#a:Type) (#wp:E.EXN?.wp a) ($f:unit -> E.EXN a wp) : Type0 =
  wp () null_post /\ wp () (fun _ -> True) ==> Inl? (reify (f ()) ())

let monotonic (#a:Type) (wp:E.EXN?.wp a) = forall p1 p2. (forall x. p1 x ==> p2 x) ==> wp () p2 ==> wp () p1

(* Does not work yet : seem to require monotonicity of wp in a trickuy way *)
(* let erase_exn (#a:Type) (#wp:E.EXN?.wp a) (f:unit -> E.EXN a wp) () *)
(*   : PURE a (fun p -> monotonic wp /\ catch_all #a #wp f /\ wp () (pure_post p)) *)
(* = reify (f ()) () *)
