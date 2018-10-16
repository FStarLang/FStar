module FStar.DM4F.StExn

(**********************************************************
 * Dijkstra Monads for Free : State with exceptions
 *
 * (Integer) state over exceptions (state kept when raising).
 *
 **********************************************************)

(* The underlying representation type *)
let stexn a =
  int -> M (option a * int)

(* Monad definition *)
val return : (a:Type) -> (x:a) -> stexn a
let return a x = fun s -> Some x, s

val bind : (a:Type) -> (b:Type) ->
           (f:stexn a) -> (g:a -> stexn b) -> stexn b
let bind a b f g =
  fun s0 ->
    let tmp = f s0 in
    match tmp with
    | None, s1_fail -> None, s1_fail
    | Some r, s1_proceed -> g r s1_proceed

let get (_:unit) : stexn int = fun s0 -> (Some s0, s0)

let put (s:int) : stexn unit = fun _ -> (Some (), s)

let raise (a:Type) : stexn a = fun s -> (None, s)

(* Define the new effect using DM4F *)
total reifiable reflectable new_effect {
  STEXN: a:Type -> Effect
  with repr    = stexn
     ; return  = return
     ; bind    = bind
     ; get     = get
     ; put     = put
     ; raise   = raise
}

(* A lift from Pure *)
unfold let lift_pure_stexn (a:Type) (wp:pure_wp a) (h0:int) (p:STEXN?.post a) =
        wp (fun a -> p (Some a, h0))
sub_effect PURE ~> STEXN = lift_pure_stexn

(* Pre-/postcondition variant *)
effect StExn (a:Type) (req:STEXN?.pre) (ens:int -> option a -> int -> GTot Type0) =
  STEXN a (fun (h0:int) (p:STEXN?.post a) -> req h0 /\
    (forall (r:option a) (h1:int). (req h0 /\ ens h0 r h1) ==> p (r, h1)))

(* Total variant *)
effect S (a:Type) = STEXN a (fun h0 p -> forall x. p x)

val div_intrinsic : i:nat -> j:int -> StExn int
  (requires (fun h -> True))
  (ensures (fun h0 x h1 -> match x with
                        | None -> h0 = h1 /\ j = 0
                        | Some z -> h0 = h1 /\ j <> 0 /\ z = i / j))
let div_intrinsic i j =
  if j = 0 then STEXN?.raise int
  else i / j

 let div_extrinsic (i:nat) (j:int) : S int =
  if j = 0 then STEXN?.raise int
  else i / j

let lemma_div_extrinsic (i:nat) (j:int) (h0:int) :
  Lemma (match reify (div_extrinsic i j) h0 with
         | None, h1 -> h0 = h1 /\ j = 0
         | Some z, h1 -> h0 = h1 /\ j <> 0 /\ z = i / j) = ()
