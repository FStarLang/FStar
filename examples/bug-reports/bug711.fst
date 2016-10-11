module Bug711

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

let return_ifc (a:Type) (x:a) : ifc a = fun l -> Some (x, l)

let bind_ifc (a:Type) (b:Type) (f:ifc a) (g: a -> Tot (ifc b)) : ifc b
  = fun l0 -> let fl0 = f l0 in match fl0 with
           | None -> None
           | Some (x, l1) ->
             let gxl1 = g x l1 in match gxl1 with
             | None -> None
             | Some (y, l2) -> Some(y, l2)

let read (l:label) : ifc bool =
  fun l0 -> Some (true, join l0 l)
(* manually inlined variant this works: *)
  (* fun l0 -> match l0, l with *)
  (*           | low, low -> Some (true, low) *)
  (*           | _, _ -> Some (true, high) *)

let write (l:label) (b:bool) : ifc unit =
  fun l0 -> if flows l0 l then (Some ((), l0)) else None
(* manually inlined variant this works: *)
  (* fun l0 -> match l0, l with *)
  (*           | high, low -> None *)
  (*           | _, _ -> Some ((), l0) *)

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
