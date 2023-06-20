open Prims
let rec (vprop_as_list :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term Prims.list) =
  fun vp ->
    match vp.Pulse_Syntax_Base.t with
    | Pulse_Syntax_Base.Tm_Emp -> []
    | Pulse_Syntax_Base.Tm_Star (vp0, vp1) ->
        FStar_List_Tot_Base.op_At (vprop_as_list vp0) (vprop_as_list vp1)
    | uu___ -> [vp]
let rec (list_as_vprop :
  Pulse_Syntax_Base.term Prims.list -> Pulse_Syntax_Base.term) =
  fun vps ->
    match vps with
    | [] -> Pulse_Syntax_Base.tm_emp
    | hd::tl -> Pulse_Syntax_Base.tm_star hd (list_as_vprop tl)
let (canon_vprop : Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term) =
  fun vp -> list_as_vprop (vprop_as_list vp)

