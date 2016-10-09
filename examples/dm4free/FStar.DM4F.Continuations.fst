module FStar.DM4F.Continuations

open FStar.FunctionalExtensionality

let cont (a:Type0) = (a -> M Type0) -> M Type0
let kont (a:Type0) = f:(cont a){forall k1 k2. feq k1 k2 ==> f k1 == f k2}

let return (a:Type0) (x:a) = fun (p : a -> M Type0) -> p x

(* Does not work. cf. #712 *)
let bind (a:Type0) (b:Type0)
         (m : kont a) (f : a -> Tot (kont b)) (k : b -> M Type0) =
         m (fun (x:a) -> f x k)

val left_unit : a:Type -> b:Type -> x:a -> f:(a -> Tot (kont b)) ->
                Lemma (bind a b (return a x) f == f x)
let left_unit a b x f = ()

reifiable new_effect_for_free {
  CONT: Type -> Effect
  with repr = kont
     ; return = return
     ; bind = bind
}

(* Error: [check (m (fun x -> (f x@0 k)))]: got an effectful computation [Type] in lieu of a pure computation [Tm_unknown] *)
