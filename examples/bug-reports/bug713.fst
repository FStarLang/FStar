module Bug713

let r = int
let cont (a:Type0) = (a -> M r) -> M r

let return (a:Type0) (x:a) = fun (p : a -> M r) -> p x

let bind (a:Type0) (b:Type0)
         (m : cont a) (f : a -> Tot (cont b)) (k : b -> M r) =
         m (fun (x:a) -> f x k)

reifiable new_effect_for_free {
  CONT: Type -> Effect
  with repr = cont
     ; return = return
     ; bind = bind
}
