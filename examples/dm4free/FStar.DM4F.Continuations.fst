module FStar.DM4F.Continuations

open FStar.FunctionalExtensionality


let cont (ans:Type) (a:Type) : Tot Type = (a -> M ans) -> M ans

let return (ans:Type) (a:Type) (x:a) (p : (a -> M ans)) : M ans = p x

let bind (ans:Type) (a:Type) (b:Type) (m : cont ans a) (f : a -> Tot (cont ans b)) (k: b -> M ans) : M ans =
                   m (fun (x:a) -> let fx = f x in fx k)
(* let bind1 a b m f : Tot (cont b) = fun k -> bind a b m f k *)

(* Sum type with explicit type anotations to bypass current lack of implicit arguments *)
noeq type either : Type 'ua -> Type 'ub -> Type u#(1 + max 'ua 'ub) =
| L : (a:Type 'ua) -> (b:Type 'ub) -> a -> either a b
| R : (a:Type 'ua) -> (b:Type 'ub) -> b -> either a b

// Excluded-middle relative to ans : cont (either a (a -> M ans))
// This could eventually be an action for CONT
// but it does not respect current limitations of DM wrt. sums of C-types
let em (ans:Type) (a:Type) (k : (either a (a -> M ans)) -> M ans) : M ans =
    let devil (x:a) : M ans = k (L a (a -> M ans) x) in
  k (R a (a -> M ans) devil)


// This could eventually be an action for CONT
// but it does not respect current limitations of DM wrt. simply-typedness
// (a and b occurs in the type of the argument f)
let callcc (ans:Type) (a:Type) (b:Type) (f : ((a -> Tot (cont ans b)) -> Tot (cont ans a))) (k : a -> M ans) : M ans =
  let g (x:a) (k0: b -> M ans) : M ans = k x in
  let fg : cont ans a = f g in
  fg k

// This could eventually be an action for CONT
// but it does not respect current limitations of DM wrt. simply-typedness
// (a occurs in the type of the argument h)
let shift (ans:Type) (a:Type) (h : ((a -> Tot (cont ans ans)) -> Tot (cont ans ans))) (k: a -> M ans) : M ans =
  let f (v:a) (k0:(ans -> M ans)) : M ans = k0 (k v) in
  let hf : cont ans ans = h f in
  let id (x:ans) : M ans = x in
  hf id

// (Error) Bound variables 'id#32998' escapes; add a type annotation
let reset (ans:Type) (h:(unit -> Tot (cont ans ans))) (k: ans -> M ans) : M ans =
  let h0 : cont ans ans = h () in
  let id (x:ans) : M ans = x in
  let h1 = (h0 id <: M ans) in
  k h1

reifiable reflectable new_effect_for_free {
  CONT (ans:Type) : a:Type -> Effect
  with repr = cont ans
     ; return = return ans
     ; bind = bind ans
  and effect_actions
//    callcc = callcc ans
//    em     = em ans
//    shift  = shift ans
//    reset  = reset ans
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


let em2 (a:Type) : CONTINUATION?.repr (either a (a -> Tot False)) (em_wp a)
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
  = CONTINUATION?.reflect (em2 a)
*)
