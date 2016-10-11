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
