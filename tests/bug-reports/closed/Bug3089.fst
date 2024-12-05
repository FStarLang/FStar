module Bug3089

(* Found by Amos Robinson. F* would fail with the error

  * Error 114 at example/No.Norm.fst(32,8-32,12):
    - Type of pattern (Prims.bool) does not match type of scrutinee (match 0 = 0 with
      | true -> FStar.List.Tot.Base.hd [Prims.bool; Prims.bool]
      | _ -> FStar.List.Tot.Base.index (FStar.List.Tot.Base.tl [Prims.bool; Prims.bool]) (0 - 1))

due to not enabling primop reduction in the unifier. Now the `0 = 0` reduces
as it should. *)

module List = FStar.List.Tot

let rec row (l: list eqtype): Type =
  match l with
  | [] -> unit
  | t :: ts -> t & row ts

let rec index (l: list eqtype) (r: row l) (i: nat { i < List.length l}): List.index l i =
  match l with
  | t :: ts ->
    let r': t & row (List.tl l) = r in
    match r' with
    | (r0, rs) ->
      if i = 0
      then r0
      else (
        // Why coerce required?
        let res: List.index ts (i - 1) = index ts rs (i - 1) in
        coerce_eq #_ #(List.index l i) () res)


let stepx (b1 b2: bool): bool =
   let estop =
         (index [bool; bool]
         (b1, (b2, ()))
         0)
   in
      match estop with
      | true -> false
      | false -> true
