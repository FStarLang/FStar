module Cont4

assume type ans

let repr (a:Type) = (a -> ans) -> ans

let return (a:Type) (x:a) = fun k -> k x

let bind (a : Type) (b : Type)
    (l : repr a) (f : a -> repr b) =
    fun k -> l (fun x -> f x k)

let wpty a = (a -> pure_wp ans) -> pure_wp ans

unfold
let return_wp (a:Type) (x:a) : wpty a =
  fun p -> p x

unfold
let bind_wp (_:range) (a b : Type) (m : wpty a) (f : a -> wpty b) : wpty b =
  fun p -> m (fun x -> f x p)

(* Monadic relation *)
unfold
let rel (#a : Type) (l : repr a) (w : wpty a) : Type =
  forall (k : a -> ans) (p : ans -> Type). (w (fun x q -> q (k x)) p ==> p (l k)) /\
                                    (p (l k) ==> w (fun x q -> q (k x)) p)

total
reifiable
reflectable
new_effect {
  CONT : a:Type -> Effect
  with
       repr      = repr
     ; return    = return
     ; bind      = bind

     ; wp_type   = wpty
     ; return_wp = return_wp
     ; bind_wp   = bind_wp

     ; mrelation = rel
}

let test1 (f : unit -> CONT int (fun kwp post -> kwp 1 post)) =
  reify (f ())

(* #set-options "--debug Cont2 --debug_level SMTQuery" *)

open FStar.Tactics

(* #set-options "--ugly --prn --print_full_names" *)

let test2 () : CONT int (fun kwp post -> kwp 1 post) =
  let f : repr int = fun k -> k 1 in
  let wp : wpty int = fun kwp post -> kwp 1 post in
  CONT?.reflect #wp f
  // inference failure here, should fix
  //CONT?.reflect #(fun kwp post -> kwp 1 post) f

let call_cc (#a:Type) (f : (a -> repr ans) -> repr ans) : repr a =
  fun k -> f (fun (r:a) k' -> k' (k r)) (fun x -> x)

let call_cc_wp (#a:Type) (wpf : (a -> wpty ans) -> wpty ans) : wpty a =
  fun (k : a -> pure_wp ans) (post : ans -> Type)
       -> wpf (fun (r:a) (ww : ans -> pure_wp ans) -> pure_bind_wp range_0 _ _ (k r) ww) (fun x -> pure_return _ x) post
       (* -> (fun _ -> null) (fun (r:a) (ww : ans -> pure_wp ans) -> pure_bind_wp range_0 _ _ (k r) ww) (fun x -> pure_return _ x) post *)
       (* -> null (fun x -> pure_return _ x) post *)
       (* -> forall x. pure_return _ x post *)
       (* -> forall x. post x *)


(* rel @ a -> repr ans *)
let rel_1 (#a:Type) (f : a -> repr ans) (wpf : a -> wpty ans) : Type =
  forall (x:a). rel (f x) (wpf x)

(* rel @ (a -> repr ans) -> ans *)
let rel_2 (#a:Type) (f : (a -> repr ans) -> repr ans) (wpf : (a -> wpty ans) -> wpty ans) : Type =
  forall g wpg. rel_1 g wpg ==> rel (f g) (wpf wpg)

open FStar.Tactics
open Predicates

(* this is admitted *)
let call_cc_related #a (f : (a -> repr ans) -> repr ans) (wpf : (a -> wpty ans) -> wpty ans)
  : Lemma (requires (rel_2 f wpf /\ monotonic wpf))
          (ensures (rel (call_cc f) (call_cc_wp wpf)))
  = assert (rel (call_cc f) (call_cc_wp wpf)) by (compute (); explode (); dump "Final";
                                                  ignore (repeat tadmit));
    ()

(* #set-options "--print_full_names" *)

let null #a : wpty a = fun kwp post -> forall x. kwp x post

#set-options "--print_implicits --debug Cont4" // --debug_level SMTQuery"

let callcc (#a:Type0) (f : (a -> CONT ans null) -> CONT ans null)
            : CONT a (call_cc_wp #a (fun _ -> null #ans))
            by (compute ())
           =
  let rf : (a -> repr ans) -> repr ans = fun c ->
    reify (f (fun x -> CONT?.reflect #(null #a) (c x)))
  in
  assume (rel_2 rf (fun _ -> null));
  call_cc_related rf (fun _ -> null);
  CONT?.reflect #(call_cc_wp #a (fun _ -> null)) (call_cc rf)

assume val callcc' : #a:Type -> (#wpf:((a -> wpty ans) -> wpty ans)) ->
                    (f : (#wpg:(a -> wpty ans) -> (x:a -> CONT ans (wpg x)) -> CONT ans (wpf wpg))) ->
                    CONT a (call_cc_wp wpf)

#set-options "--print_implicits --print_effect_args"

let em0 (#a:Type) () : CONT (c_or a (a -> CONT ans (fun kwp post -> False))) (fun kwp post -> False)
=
  callcc #_ (fun (f : (c_or a (a -> CONT ans (fun kwp post -> False))) -> CONT ans (fun kwp post -> False)) ->
                        f (Right (fun (x:a) -> f (Left x))))

let kk #a (f : (x : c_or a (a -> CONT ans null)) -> CONT ans null) : CONT ans null =
  f (Right (fun (x:a) -> f (Left x)))

let em1 (#a:Type) () : CONT (c_or a (a -> CONT ans null))
                            (call_cc_wp #(c_or a (a -> CONT ans null)) (fun _wpg -> null))
=
  callcc #(c_or a (a -> CONT ans null)) kk
