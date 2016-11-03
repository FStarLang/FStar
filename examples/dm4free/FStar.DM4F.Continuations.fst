module FStar.DM4F.Continuations

open FStar.FunctionalExtensionality


irreducible let ans : Type0 = int

let kont (a:Type0) : Tot Type = (a -> M ans) -> M ans

let return (a:Type0) (x:a) (p : (a -> M ans)) : M ans = p x

let bind (a:Type0) (b:Type0) (m : kont a) (f : a -> Tot (kont b)) (k: b -> M ans) : M ans =
                   m (fun (x:a) -> let fx = f x in fx k)
(* let bind1 a b m f : Tot (kont b) = fun k -> bind a b m f k *)

(* Sum type with explicit type anotations to bypass current lack of implicit arguments *)
noeq type either : Type -> Type -> Type =
| L : (a:Type) -> (b:Type) -> a -> either a b
| R : (a:Type) -> (b:Type) -> b -> either a b

// Excluded-middle relative to ans : kont (either a (a -> M ans))
let em (a:Type) (k : (either a (a -> M ans)) -> M ans) : M ans =
  let devil (x:a) : M ans = k (L a (a -> M ans) x) in
  k (R a (a -> M ans) devil)

reifiable new_effect_for_free {
  CONT: a:Type -> Effect
  with repr = kont
     ; return = return
     ; bind = bind
  and effect_actions
(* Send FStar in an infinite loop when typechecking *)
//      em = em
}

(*
Error: [check (m (fun x -> let  fx#1811 <> : ((uu___:(uu___:b -> M (Type(unknown))) -> M (Type(unknown))) : Type(unknown)) = (f x@0)
in
(fx@0 k)))]: got an effectful computation [Type(unknown)] in lieu of a pure computation [Tm_unknown]
*)

(*

let bind : (a:Type -> b:Type -> m:(kont a@1) -> f:(uu___:a@2 -> Tot (kont b@2)) -> Tot (kont b@2))
Checked: visible let  bind  : (a:Type -> b:Type -> m:(kont a@1) -> f:(uu___:a@2 -> Tot (kont b@2)) -> Tot (kont b@2)) =
(fun a b m f -> (((fun k -> ((m@2 (fun x -> (
                                let  fx#653  : (kont b@4) = (f@2 x@0) in
                                  (fx@0 k@2) $$ M (Type)))) $$ Tot Type)    <-- should be M Type
                  ) : (kont b@2)) $$ Tot (kont b@2)))

*)
