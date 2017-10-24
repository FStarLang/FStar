module Bug710

type label =
  | Low
  | High

let ifc (a:Type) = label -> M (option (a * label))

let eq_ifc (a:Type) (f:ifc a) (g:ifc a) =
   forall l. f l == g l

let return_ifc (a:Type) (x:a) : ifc a = fun l -> Some (x, l)
let bind_ifc (a:Type) (b:Type) (f:ifc a) (g: a -> Tot (ifc b)) : ifc b
  = fun l0 -> let fl0 = f l0 in match fl0 with
           | None -> None
           | Some (x, l1) ->
             let gxl1 = g x l1 in match gxl1 with
             | None -> None
             | Some (y, l2) -> Some(y, l2)

val left_unit: a:Type -> b:Type -> x:a -> f:(a -> Tot (ifc b))
            -> Lemma (eq_ifc b (bind_ifc a b (return_ifc a x) f) (f x))
let left_unit a b x f = ()
