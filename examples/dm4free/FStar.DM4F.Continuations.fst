module FStar.DM4F.Continuations

open FStar.FunctionalExtensionality


let kont (ans:Type) (a:Type) : Tot Type = (a -> M ans) -> M ans

let return (ans:Type) (a:Type) (x:a) (p : (a -> M ans)) : M ans = p x

let bind (ans:Type) (a:Type) (b:Type) (m : kont ans a) (f : a -> Tot (kont ans b)) (k: b -> M ans) : M ans =
                   m (fun (x:a) -> let fx = f x in fx k)
(* let bind1 a b m f : Tot (kont b) = fun k -> bind a b m f k *)

(* Sum type with explicit type anotations to bypass current lack of implicit arguments *)
noeq type either : Type -> Type -> Type =
| L : (a:Type) -> (b:Type) -> a -> either a b
| R : (a:Type) -> (b:Type) -> b -> either a b

// Excluded-middle relative to ans : kont (either a (a -> M ans))
// This could eventually be an action for CONT but does not respect current limitations of DM
let em (ans:Type) (a:Type) (k : (either a (a -> M ans)) -> M ans) : M ans =
    let devil (x:a) : M ans = k (L a (a -> M ans) x) in
  k (R a (a -> M ans) devil)


(* Instanciating ans with False *)
reifiable reflectable new_effect_for_free {
  CONT (ans:Type) : a:Type -> Effect
  with repr = kont ans
     ; return = return ans
     ; bind = bind ans
  and effect_actions
}


reifiable reflectable new_effect_for_free CONTINUATION = CONT False

(*
let repr (a:Type)
         (wp_a:((uu___:(uu___:a@0 -> uu___:(uu___:l_False -> Tot Type) -> Tot Type) -> uu___:(uu___:l_False -> Tot Type) -> Tot Type) <: Type))
  : PURE (Type) (fun p ->
              ((l_Forall #Type (fun y -> ((l_imp (eq2 #Type y@0 (uu___-w':(uu___:a@3 -> uu___:(uu___:l_False -> Tot Type) -> Tot Type) -> uu___:(uu___-x:a@4 -> PURE (l_False) (uu___-w'@1 uu___-x@0)) -> PURE (l_False) (wp_a@4 uu___-w'@1))) (p@1 y@0)) $$ Tot Type))) $$ Tot Type))
  = uu___-w':(uu___:a@1 -> uu___:(uu___:l_False -> Tot Type) -> Tot Type) ->
    uu___:(uu___-x:a@2 -> PURE (l_False) (uu___-w'@1 uu___-x@0)) ->
    PURE (l_False) (wp_a@2 uu___-w'@1)

unfold let  CONTINUATION_pre  : Type = (uu___:(uu___:l_False -> Tot Type) -> Tot Type)
unfold let  CONTINUATION_post  : (a:Type -> PURE (Type) (fun p -> ((l_Forall #Type (fun y -> ((l_imp (eq2 #Type y@0 (uu___:a@2 -> uu___:(uu___:l_False -> Tot Type) -> Tot Type)) (p@1 y@0)) $$ Tot Type))) $$ Tot Type))) = (fun a -> ((uu___:a@0 -> uu___:(uu___:l_False -> Tot Type) -> Tot Type) $$ Tot Type))


*)

(* Trying to recover em by explicit reflection *)
let em_wp (a:Type)
          (pbpost : (either a (a -> Tot False)) -> (False -> Tot Type0) -> Tot Type0)
          (post : False -> Tot Type0)
          : Tot Type0 =
          (* em_wp must be crafted so that *)
          (* 1] the inner function devil below is total (condition on pbpost) *)
          (* i.e. pbpost (L _) _ == True *)
          (* 2] the overall result satisfies kspec (R _) _ *)
          (forall (x: either a (a -> Tot False)) (post' : False -> Type0). pbpost x post')


let em2 (a:Type) : CONTINUATION.repr (either a (a -> Tot False)) (em_wp a)
  = fun (kspec : (either a (a -> Tot False)) -> (False -> Tot Type0) -> Tot Type0)
      (k : (x:(either a (a -> Tot False))) -> PURE False (kspec x)) ->
      begin
        let devil (x:a) : Tot False = k (L a (a -> Tot False) x) in
        k (R a (a -> Tot False) devil)
        //<: PURE False (em_wp kspec)
      end


(*
// TODO : to be investigated ./FStar.DM4F.Continuations.fst(19,2-19,3): (Error) assertion failed
reifiable let excluded_middle (a:Type)
  : CONTINUATION (either a (a -> Tot False)) (em_wp a)
  = CONTINUATION.reflect (em2 a)
*)
