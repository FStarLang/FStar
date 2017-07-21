module FStar.DM4F.MonadTransformers

noeq
type monad =
  | MkMonad :
    t:(Type -> Type) ->
    ret:(a:Type -> a -> M (t a)) ->
    bind:(a:Type -> b:Type -> t a -> (a -> M (t b)) -> M (t b)) ->
    monad

let id_t (a:Type) = a
let return_id_t (a:Type) (x:a) : M (id_t a) = x
let bind_id_t (a b:Type) (m:id_t a) (f:a -> M (id_t b)) : M (id_t b) = f m

let id_monad : monad = MkMonad id_t return_id_t bind_id_t

let int_st_t (m:monad) (a:Type) = int -> M (MkMonad?.t m (a * int))
let return_st_t (m:monad) (a:Type) (x:a) : int_st_t m a = fun s -> MkMonad?.ret m (a * int) (x,s)
let bind_st_t (m:monad) (a b:Type) (x:int_st_t m a) (f:a -> int_st_t m b) : int_st_t m b=
  fun s0 -> let x' = x s0 in
    let f0 : (a * int) -> M (MkMonad?.t m (b * int)) = fun (x'', s1) -> f x'' s1 in
    MkMonad?.bind m (a * int) (b * int) x' f0

let ex_t (m:monad) (a:Type) = unit -> M (MkMonad?.t m (either a exn))
let bind_ex_t (m:monad) (a b:Type) (x:ex_t m a) (a -> ex_t m b) =
  let x = x () in
  MkMonad?.bind a b x (function
    | Inl x' -> 
  )
(* noeq *)
(* type monad = *)
(*   | MkMonad : *)
(*     t:(Type -> Type) -> *)
(*     ret:(a:Type -> a -> t a) -> *)
(*     bind:(a:Type -> b:Type -> t a -> (a -> t b) -> t b) -> *)
(*     monad *)

(* let int_st_t (m:monad) (a:Type) = int -> M (MkMonad?.t m (a * int)) *)
(* let bind_st_t (m:monad) (a b:Type) (x:int_st_t m a) (f:a -> int_st_t m b) = *)
(*   fun s0 -> let x' = x s in *)
(*     MkMonad?.bind m (fun (x'', s1) -> *)
(*       (\* This has type M (MkMonad?.t m (a * int)) and not MkMonad?.t m (a * int) *\) *)
(*       f x'' s1 *)
(*     ) *)

(* let id_t (a:Type) = a *)
(* let return_id_t (a:Type) (x:a) : id_t a = x *)
(* let bind_id_t (a b:Type) (m:id_t a) (f:a -> id_t b) : id_t b = f m *)

(* let id_monad : monad = MkMonad id_t return_id_t bind_id_t *)


(* let ex_t (m:monad) (a:Type) = unit -> M (MkMonad?.t m (either a exn)) *)
(* let bind_ex_t (m:monad) (a b:Type) (x:ex_t m a) (a -> ex_t m b) = *)
(*   let x = x () in *)
(*   MkMonad?.bind a b x (function *)
(*     | Inl x' ->  *)
(*   ) *)
