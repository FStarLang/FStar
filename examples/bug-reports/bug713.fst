module Bug713

let r = int
let cont (a:Type0) : Type = (a -> M r) -> M r

let return (a:Type0) (x:a) (p : a -> M r) : M r = p x

let bind (a:Type0) (b:Type0)
         (m : cont a) (f : a -> Tot (cont b)) (k : b -> M r) : M r =
         m (fun (x:a) -> let fx = f x in fx k)

reifiable new_effect {
  CONT: Type -> Effect
  with repr = cont
     ; return = return
     ; bind = bind
}
