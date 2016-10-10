module FStar.DM4F.Continuations

open FStar.FunctionalExtensionality

let kont (a:Type) = (a -> M Type0) -> M Type0

let return (a:Type) (x:a) : kont a = fun (p : a -> M Type0) -> p x

val bind : a:Type -> b:Type -> m:kont a -> f:(a -> kont b) -> kont b
let bind a b m f = fun k -> 
(* This does not work. cf. #712: m (fun (x:a) -> f x k) *)
(* Silly workaround: *)
  //let mm : cont a = m in
  m (fun (x:a) -> f x k)
    (* let fx (\* : cont b *\) = f x in *)
    (* fx k) *)

(* val left_unit : a:Type -> b:Type -> x:a -> f:(a -> Tot (kont b)) -> *)
(*                 Lemma (bind a b (return a x) f == f x) *)
(* let left_unit a b x f = admit() *)

reifiable new_effect_for_free {
  CONT: Type -> Effect
  with repr = kont
     ; return = return
     ; bind = bind
}

(* Error: The following term is outside of the definition language:
(f#74:(uu___:(uu___:a -> M (Type)) -> M (Type)){(x#894:Prims.unit{(x:(uu___:a -> Type) -> Tot (x#894:Prims.unit{(x:(uu___:a -> Type) -> Tot (x#894:Prims.unit{(uu___:(x#894:Prims.unit{(x:a -> GTot {:pattern (x@5 x@0)\/(x@3 x@0)} (Prims.eq2 (x@5 x@0) (x@3 x@0)))}) -> GTot (Prims.eq2 (f@6 x@4) (f@6 x@2)))}))}))})}) *)
