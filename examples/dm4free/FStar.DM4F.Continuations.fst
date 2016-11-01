module FStar.DM4F.Continuations

open FStar.FunctionalExtensionality

let kont (a:Type0) : Tot Type = (a -> M Type0) -> M Type0

let return (a:Type0) (x:a) : Tot (kont a) = fun (p : a -> M Type0) -> p x

let bind (a:Type0) (b:Type0) (m : kont a) (f : a -> kont b) : Tot (kont b) =
                   fun k -> m (fun (x:a) -> let fx = f x in fx k)

reifiable new_effect_for_free {
  CONT: Type -> Effect
  with repr = kont
     ; return = return
     ; bind = bind
}

(*
Error: [check (m (fun x -> let  fx#1811 <> : ((uu___:(uu___:b -> M (Type(unknown))) -> M (Type(unknown))) : Type(unknown)) = (f x@0)
in
(fx@0 k)))]: got an effectful computation [Type(unknown)] in lieu of a pure computation [Tm_unknown]
*)
