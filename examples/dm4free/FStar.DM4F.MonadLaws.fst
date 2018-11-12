module FStar.DM4F.MonadLaws

open FStar.FunctionalExtensionality

(* State *)

let st (s:Type) (a:Type) = s -> Tot (a * s)

let return_st (#s:Type) (#a:Type) (x:a) : st s a = fun s0 -> x, s0

let bind_st (#s:Type) (#a:Type) (#b:Type) (f:st s a) (g:a -> st s b) : st s b
  = fun s0 -> let x, s1 = f s0 in g x s1

let right_unit_st (s:Type) (a:Type) (f:st s a) =
  assert (feq (bind_st f (return_st)) f)

let left_unit_st (s:Type) (a:Type) (b:Type) (x:a) (f:(a -> st s b)) =
  assert (feq (bind_st (return_st x) f) (f x))

let assoc_st (s:Type) (a:Type) (b:Type) (c:Type)
             (f:st s a) (g:(a -> st s b)) (h:(b -> st s c))
   = assert (feq (bind_st f (fun x -> bind_st (g x) h))
                 (bind_st (bind_st f g) h))

(* IFC, done in a nicer style, using Lemmas instead of assert *)

type label =
  | Low
  | High

let ifc (a:Type) = label -> Tot (option (a * label))

let return_ifc (#a:Type) (x:a) : ifc a = fun l -> Some (x, l)
let bind_ifc (#a:Type) (#b:Type) (f:ifc a) (g: a -> Tot (ifc b)) : ifc b
  = fun l0 -> let fl0 = f l0 in match fl0 with
           | None -> None
           | Some (x, l1) ->
             let gxl1 = g x l1 in match gxl1 with
             | None -> None
             | Some (y, l2) -> Some(y, l2)

val left_unit: a:Type -> b:Type -> x:a -> f:(a -> Tot (ifc b))
            -> Lemma (feq (bind_ifc (return_ifc x) f) (f x))
let left_unit a b x f = ()

val right_unit: a:Type -> f:ifc a -> Lemma (feq (bind_ifc f (return_ifc)) f)
let right_unit a f = ()

val associativity: a:Type -> b:Type -> c:Type ->
                   f:ifc a -> g:(a -> Tot (ifc b)) -> h:(b -> Tot (ifc c))
                 -> Lemma (feq (bind_ifc f (fun x -> bind_ifc (g x) h))
                                    (bind_ifc (bind_ifc f g) h))
let associativity a b c f g h = ()
