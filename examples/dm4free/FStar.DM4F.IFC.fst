module FStar.DM4F.IFC

(********************************************************************************)
(* Effect (ifc a) : A monad for dynamic information-flow control                *)
(********************************************************************************)

(* TODO: This has not been whitelisted
type label =
  | Low
  | High
*)
type label = bool
inline let low = true
inline let high = false

(* working around the whitelist *)
inline let eq l1 l2 =
  match l1, l2 with
  | true, true
  | false, false -> true
  | _, _ -> false

inline let join l1 l2 =
  if l1 `eq` high || l2 `eq` high then high else low

inline let flows l1 l2 = not(l1 `eq` high && l2 `eq` low)

let ifc (a:Type) = label -> M (option (a * label))

(* open FStar.FunctionalExtensionality *)

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
let left_unit a b x f = admit() (* #710 *)

val right_unit: a:Type -> f:ifc a -> Lemma (eq_ifc a (bind_ifc a a f (return_ifc a)) f)
let right_unit a f = admit() (* #710 *)

val associativity: a:Type -> b:Type -> c:Type -> f:ifc a -> g:(a -> Tot (ifc b)) -> h:(b -> Tot (ifc c))
                 -> Lemma (eq_ifc c (bind_ifc a c f (fun x -> bind_ifc b c (g x) h)) (bind_ifc b c (bind_ifc a b f g) h))
let associativity a b c f g h = ()

// Some dummy implementations of actions for illustration purposes
// Probably better to just take them axiomatically
let read (l:label) : ifc bool =
  (* fun l0 -> Some (true, join l0 l) -- needed to manually inline this; #711 *)
  fun l0 -> match l0, l with
            | low, low -> Some (true, low)
            | _, _ -> Some (true, high)

let write (l:label) (b:bool) : ifc unit =
  (* fun l0 -> if flows l0 l then (Some ((), l0)) else None
     -- needed to manually inline this; #711 *)
  fun l0 -> match l0, l with
            | high, low -> None
            | _, _ -> Some ((), l0)

let xor (b1:bool) (b2:bool) : Tot bool = not (b1 = b2)

// A sample monadic program (normally would write this after
// elaboration, but whatever, can write this in DM too)
val p : unit -> Pure (ifc unit) (requires True) (ensures (fun r -> forall l. r l = None))
(* Weak type (works): unit -> Tot (ifc unit) *)
(* Alternative strong type (doesn't work), (Valid(ApplyTT@2 @0))
  unit -> Tot (label -> Pure (err (unit * label)) (requires True) (ensures (fun r -> r = None))) *)
(* let p () = bind_ifc _ _ (read low)              (fun b1 -> *)
(*            bind_ifc _ _ (read low)              (fun b2 -> *)
(*            bind_ifc _ _ (write low (b1 && b2))  (fun _  -> *)
(*            bind_ifc _ _ (read high)             (fun b3 -> *)
(*            bind_ifc _ _ (write high (b1 || b3)) (fun _  -> *)
(*                         (write low (xor b3 b3))  ))))) *)
let p () = admit() (* #710 *)

(* TODO: without reifiable, this fails weirdly. Cf #709 *)

reifiable new_effect_for_free {
  IFC : a:Type -> Effect
  with
       repr         = ifc
     ; bind         = bind_ifc
     ; return       = return_ifc
  and effect_actions
      read = read
    ; write = write
}

effect Ifc (a:Type) (req:IFC.pre) (ens:label -> option (a * label) -> GTot Type0) =
  IFC a (fun (h0:label) (p:IFC.post a) -> req h0 /\
             (forall r. (req h0 /\ ens h0 r) ==> p r))

inline let lift_pure_exnst (a:Type) (wp:pure_wp a) (h0:label) (p:IFC.post a) =
  wp (fun a -> p (Some (a, h0)))
sub_effect PURE ~> IFC = lift_pure_exnst

val p' : unit ->  Ifc unit (requires (fun l   -> True))
                           (ensures  (fun l r -> r = None))
let p' () =
  let b1 = IFC.read low in
  let b2 = IFC.read low in
  IFC.write low (b1 && b2);
  let b3 = IFC.read high in
  IFC.write high (b1 || b3);
  IFC.write low (xor b3 b3)

(* just a sanity check for Guido: this works with the pure to Ifc coercion;
   btw. can't we get the pure to X coercion for free too ?*)
val p'' : unit -> Ifc unit (requires (fun l   -> True))
                           (ensures  (fun l r -> True))
let p'' () = ()
