module Bug1866

open FStar.Tactics

let rec not_do_much e: Tac term =
  match inspect e with
  | Tv_App _ _ ->
      let e, es = collect_app e in
      let e = not_do_much e in
      let es = map (fun (e, q) -> not_do_much e, q) es in
      mk_app e es

  | Tv_Var _ | Tv_BVar _ | Tv_FVar _
  | Tv_Const _ ->
    e

  | Tv_Abs b e ->
      let e = not_do_much e in
      let e = pack (Tv_Abs b e) in
      e

  | Tv_Match scrut branches ->
      let scrut = not_do_much scrut in
      let pats, es = List.Tot.split branches in
      let es = map not_do_much es in
      let branches = zip pats es in
      pack (Tv_Match scrut branches)

  | Tv_Let r attrs bv e1 e2 ->
      let e1 = not_do_much e1 in
      let e2 = not_do_much e2 in
      let e = pack (Tv_Let r attrs bv e1 e2) in
      e

  | Tv_AscribedT e t tac ->
      let e = not_do_much e in
      let e = pack (Tv_AscribedT e t tac) in
      e

  | Tv_AscribedC e c tac ->
      let e = not_do_much e in
      let e = pack (Tv_AscribedC e c tac) in
      e

  | Tv_Arrow _ _
  | Tv_Type _
  | Tv_Uvar _ _
  | Tv_Refine _ _
  | Tv_Unknown ->
      // Looks like we ended up visiting a type argument of an application.
      e


let base0 =
    let (x,y,z) = (1,2,3) in
    x

let base1 =
    let Mktuple3 x y z = (1,2,3) in
    x

let base2 =
    let Mktuple3 #_ #_ #_ x y z = (1,2,3) in
    x

val base3 : #a:Type -> #b:Type -> a & b -> a
let base3 #a #b p =
    let (x, _) = p in
    x

val base4 : 'a & 'b -> 'a
let base4 p =
    let (x, _) = p in
    x

let traverse (name:string) : Tac decls =
  let d = lookup_typ (top_env ()) (cur_module () @ [ name ]) in
  let d = match d with Some d -> d | None -> fail "0" in
  let d, us = match inspect_sigelt d with
    | Sg_Let _ _ us _ d -> d, us
    | _ -> fail "1"
  in
  let name = pack_fv (cur_module () @ [ "test_" ^ name ]) in
  let r = not_do_much d in
  (* dump ("r = " ^ term_to_string r); *)
  let s = pack_sigelt (Sg_Let false name us (pack Tv_Unknown) r) in
  [s]

%splice[test_base0](traverse "base0")
%splice[test_base1](traverse "base1")
%splice[test_base2](traverse "base2")
%splice[test_base3](traverse "base3")
%splice[test_base4](traverse "base4")
