module FStar.DM4F.IFC

(********************************************************************************)
(* Effect (ifc a) : A monad for dynamic information-flow control                *)
(********************************************************************************)

type label =
  | Low
  | High

let ifc (a:Type) = label -> M (option (a * label))

let return_ifc (a:Type) (x:a) : ifc a = fun l -> Some (x, l)
let bind_ifc (a:Type) (b:Type) (f:ifc a) (g: a -> Tot (ifc b)) : ifc b
  = fun l0 -> let fl0 = f l0 in
              match fl0 with
              | None -> None
              | Some (x, l1) ->
                let gxl1 = g x l1 in
                match gxl1 with
                | None -> None
                | Some (y, l2) -> Some(y, l2)

reifiable new_effect_for_free {
  IFC : a:Type -> Effect
  with
       repr         = ifc
     ; bind         = bind_ifc
     ; return       = return_ifc
}

effect Ifc (a:Type) (req:IFC..pre) (ens:label -> option (a * label) -> GTot Type0) =
  IFC a (fun (h0:label) (p:IFC..post a) -> req h0 /\
             (forall r. (req h0 /\ ens h0 r) ==> p r))

unfold let lift_pure_exnst (a:Type) (wp:pure_wp a) (h0:label) (p:IFC..post a) =
  wp (fun a -> p (Some (a, h0)))
sub_effect PURE ~> IFC = lift_pure_exnst

// read and write are assumed, since we don't model I/O precisely here

let join l1 l2 = if l1 = High || l2 = High then High else Low

let flows l1 l2 = not(l1=High && l2=Low)

assume val read : l:label -> IFC bool
  (fun l0 p -> forall b. p (Some (b, join l0 l)))

assume val write : l:label -> bool -> IFC unit
  (fun l0 p -> if flows l0 l then p (Some ((), l0)) else p None)

// A simple program using the IFC effect

let xor (b1:bool) (b2:bool) : Tot bool = not (b1 = b2)

val p : unit ->  Ifc unit (requires (fun l   -> True))
                          (ensures  (fun l r -> r = None))
let p () =
  let b1 = read Low in
  let b2 = read Low in
  write Low (b1 && b2);
  let b3 = read High in
  write High (b1 || b3);
  write Low (xor b3 b3)
