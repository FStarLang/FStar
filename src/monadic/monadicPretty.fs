(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"
module Microsoft.FStar.MonadicPretty

open Util
open Absyn


(*****************************************************************************)
(*                             Pretty-printing                               *)
(*****************************************************************************)

let lident2string (l:lident) : string = l.str

let bvdef2string b : string =
  if !Options.print_real_names 
  then spr "%A" b.realname
  else spr "%A" b.ppname

let bvar2string (b:bvar<'a,'t>) : string =
  bvdef2string b.v

let var2string (v:var<'t>) : string =
  lident2string v.v

let rec kind2string (k:kind) (tabs:string) : string = 
  (* TODO: fill this in *)
  if !Options.silent then ""
  else spr "%A" k

and typ2string (t:typ) (tabs:string) : string =
  if !Options.silent then "" 
  else Pretty.strTyp t
    

(*
  let newtabs = tabs + "  " in
  let res = 
  match t.v with
    | Typ_btvar b -> spr "(btvar %s)" (bvar2string b)
    | Typ_const (v,_) -> spr "(const %s)" (var2string v)
    | Typ_record (flist, topt) ->
        let flist' = 
          List.map 
            (fun (f,t) -> spr "%s:%s" (lident2string f) (typ2string t tabs)) 
            flist in
        spr "(rec %s)" (String.concat "; " flist') 
    | Typ_fun (bopt, t1, t2) ->
        let v = 
          match bopt with Some b -> spr "%s:" (bvdef2string b) | None -> "" in
        spr "(tfun %s%s -> %s)" v (typ2string t1 tabs) (typ2string t2 tabs)
    | Typ_univ (b,k,_,t) -> (* NS -- ignoring formula *)
        spr "(forall %s. %s)" (bvdef2string b) (typ2string t tabs)
    | Typ_dtuple elts ->
        let elt2string (o,t) = 
          let bstr = 
            match o with 
              | Some b -> spr "%s:" (bvdef2string b) 
              | _ -> "" 
          in
          spr "%s%s" bstr (typ2string t tabs)
        in
        let elts' = List.map elt2string elts in
        spr "(dtuple %s)" (String.concat " * " elts')
    | Typ_refine (bv, t, f, b) -> 
        let t_str = typ2string t newtabs in
        let f_str = typ2string f newtabs in
        spr "(refine %s:%s {%s})" (bvdef2string bv) t_str f_str
    | Typ_app (t1, t2) -> spr "(app %s %s)" (typ2string t1 tabs) (typ2string t2 tabs)
    | Typ_dep (t,e) -> spr "(dep %s %s)" (typ2string t tabs) (exp2string e newtabs)
    | Typ_affine t -> spr "(affine %s)" (typ2string t tabs)
    | Typ_lam (b, t1, t2) -> 
        spr "(tlam %s:%s => %s)" (bvdef2string b) (typ2string t1 tabs) (typ2string t2 tabs)
    | Typ_tlam (b, k, t) ->
        spr "(%s::%s => %s)" (bvdef2string b) "_" (typ2string t tabs)
    | Typ_ascribed (t,k) -> spr "(ascribed %s::%s)" (typ2string t tabs) "_"
    | Typ_unknown -> "unknown"
    | Typ_uvar _ -> spr "(uvar %s)" (Pretty.strTyp t)
    | _ -> failwith (spr "unexpected %A" t.v)
*)

and exp2string (e:exp) (tabs:string) : string = 
  if !Options.silent 
  then ""
  else 
    let newtabs = tabs + "  " in
    let terminalWidth = 80 in
      match e.v with
        | Exp_bvar bvar -> spr "(bvar %A)" (bvar.v.ppname)
        | Exp_fvar (fvar, ext) -> spr "(fvar %A)" (fvar.v)
        | Exp_constant c -> spr "(constant %A)" c
        | Exp_constr_app (v, tlist, _, elist) ->
            "(constr_app "
            + (String.concat 
                 " " 
                 ([(spr "%A" v.v)] 
                  @ (List.map (fun x -> "_") tlist) 
                  @ (List.map (fun (x:exp) -> (exp2string x tabs)) elist)))
            + ")"
        | Exp_abs (b, t, e) -> 
            let s = exp2string e tabs in
            let t_str = typ2string t tabs in
              if (String.length s) + (String.length t_str) <= terminalWidth - 10
              then spr "(abs %A:%s %s)" (bvdef2string b) t_str s
              else spr "(abs %A:%s \n%s%s)" (bvdef2string b) t_str newtabs (exp2string e newtabs)
        | Exp_tabs (b, k, _, e) ->  (* NS -- ignoring formula *)
            let s = exp2string e tabs in
              if String.length s <= terminalWidth - 11
              then spr "(tabs %A _ %s)" (bvdef2string b) s
              else spr "(tabs %A _ \n%s%s)" (bvdef2string b) newtabs (exp2string e newtabs)
        | Exp_app (e1, e2) ->
            let s1 = exp2string e1 newtabs in
            let s2 = exp2string e2 newtabs in
              if (String.length s1) + (String.length s2) <= terminalWidth - 6
              then spr "(app %s %s)" s1 s2
              else spr "(app \n%s%s \n%s%s)" newtabs s1 newtabs s2
        | Exp_tapp (e,t) -> 
            let s1 = exp2string e newtabs in
            let s2 = typ2string t newtabs in
              if (String.length s1) + (String.length s2) <= terminalWidth - 7
              then spr "(tapp %s %s)" s1 s2
              else spr "(tapp \n%s%s \n%s%s)" newtabs s1 newtabs s2
        | Exp_match (e, l, d) ->
            (* TODO: make this nicer *)
            let p2string (Pat_variant (id, tlist, elist, bvlist, b)) = 
              spr "%s %s %s %s"
                (lident2string id)
                (String.concat " " (List.map (fun x -> typ2string x newtabs) tlist))
                (String.concat " " (List.map (fun x -> exp2string x newtabs) elist))
                (String.concat " " (List.map (fun x -> bvar2string x) bvlist)) 
            in
              spr "(match %s with\n%s%s\n%s%s)" 
                (exp2string e tabs) newtabs
                (String.concat ("\n" + newtabs) 
                   (List.map (fun (p,e) -> spr "%s -> %s" (p2string p) (exp2string e newtabs)) l))
                tabs (exp2string d newtabs)
        | Exp_ascribed (e,t,ev) ->
            let e' = exp2string e newtabs in
            let t' = typ2string t newtabs in
              if (String.length e') + (String.length t') + 5 <= terminalWidth
              then spr "(asc %s : %s)" e' t'
              else spr "(asc %s \n%s: %s)" e' tabs t'
        | Exp_let (false, [bvd, t, e], d) ->
            spr "(let %A : %s = %s in \n%s%s)" (bvdef2string bvd) (typ2string t newtabs) (exp2string e newtabs) tabs (exp2string d tabs)
        | Exp_let (true, h::t, d) ->
            let (bvd, _, e) = h in
            let hstr = spr "(let rec %A = %s " (bvdef2string bvd) (exp2string e newtabs) in
            let tStrList = List.map (fun (bvd, t, e) -> spr "AND %A = %s" (bvd.ppname) (exp2string e newtabs)) t in
            let dstr = exp2string d tabs in 
              (String.concat ("\n" + tabs) (hstr::tStrList)) + " in " + dstr + ")"
        | Exp_extern_call (r, id, t, tlist, elist) -> 
            (spr "(extern_call %A %A\n" r id)
            + (String.concat ("\n" + tabs) (List.map (fun e -> (exp2string e newtabs)) elist))
            + ")"
        | Exp_primop (id, elist) ->
            let slist = List.map (fun e -> (exp2string e newtabs)) elist in
            let sumlen = List.fold (fun sum s -> sum + (String.length s)) 0 slist in
              if sumlen <= terminalWidth - 10
              then
                (spr "(primop %A" id)
                + (String.concat " " slist)
                + ")"
              else
                (spr "(primop %A\n%s" id newtabs)
                + (String.concat ("\n" + newtabs) slist)
                + ")"
        | Exp_cond (e1, e2, e3) -> 
            spr "(cond \n%s%s \n%s%s \n%s%s)" 
              tabs (exp2string e1 newtabs) 
              tabs (exp2string e2 newtabs) 
              tabs (exp2string e3 newtabs)
        | Exp_recd (optid, tlist, explist, flist) -> 
            (spr "(recd %s" (match optid with Some id -> spr "%A " id | None -> ""))
            + (String.concat " " (List.map (fun t -> typ2string t tabs) tlist)) + " "
            + (String.concat " " (List.map (fun e -> exp2string e tabs) explist))
            + (spr " with\n%s" tabs)
            + (String.concat "; " (List.map (fun (f,e) -> spr "%A=%s" f (exp2string e newtabs)) flist))
            + ")"
        | Exp_proj (e, f) -> spr "(proj %s.%A)" (exp2string e tabs) f
        | Exp_gvar _ -> failwith "unexpected Exp_gvar"
        | Exp_bot -> "(bottom)"
        | x -> failwith (spr "missing %A" x)

let letbinding2string ((lb,r):letbinding * bool) : string =
  if !Options.silent then ""
  else 
    let rstr = if r then "rec " else "" in
      match lb with 
        | (bv, t, e)::tl ->
            let hstr = 
              spr "let %s%A = \n  %A\n  : %A\n" 
                rstr 
                (bv.ppname) 
                (e.ToString())
                (Pretty.strTyp t)
            in
            let tstrList = 
              List.map 
                (fun (bv,t,e) -> 
                   spr "%A = \n  %A\n  : %A" 
                     (bv.ppname) 
                      (exp2string e) (Pretty.strTyp t))
                tl
            in
              (String.concat "\nand " (hstr::tstrList)) + "\n"
        | _ -> failwith "unexpected %A" lb

let signature2string (s:signature) : string =
  if !Options.silent then ""
  else 
    let rec sigelt2string (se:sigelt) : string =
      let tp2string tp = 
        match tp with 
          | Tparam_typ (b,k) -> 
              spr "(Tparam_typ %s %s)" (bvdef2string b) (kind2string k "")
          | Tparam_term (b,t) -> 
              spr "(Tparam_term %s %s)" (bvdef2string b) (typ2string t "")
      in
        match se with
          | Sig_tycon_kind (id, tplist, k, b, _, _) ->
              let tplist' = List.map tp2string tplist in
                spr "(tycon_kind %s %s _ _)" 
                  (lident2string id) 
                  (String.concat " " tplist')
          | Sig_typ_abbrev (id, tplist, k, t) ->
              let tplist' = List.map tp2string tplist in
                spr "(typ_abbrev %s %s _ %s)"
                  (lident2string id)
                  (String.concat " " tplist')
                  (typ2string t "")
          | Sig_record_typ (id, tplist, k, t, eref) ->
              let tplist' = List.map tp2string tplist in
                spr "(record_typ %s %s _ %s)" 
                  (lident2string id)
                  (String.concat " " tplist')
                  (typ2string t "")
          | Sig_datacon_typ (id, tplist, t, b, a, idopt, erefopt, flist) ->
              let tplist' = String.concat " " (List.map tp2string tplist) in
              let flist' = String.concat " " (List.map (function Inl x -> typ2string x "" | Inr e -> exp2string e "") flist) in
                spr "(datacon_typ %s %s %s %s)" (lident2string id) (typ2string t "") tplist' flist'
          | Sig_value_decl (id, t) -> 
              spr "(value_decl %s %s)" (lident2string id) (typ2string t "")
          | Sig_extern_value (eref, id, t) ->
              spr "(extern_value %s %s)" (lident2string id) (typ2string t "")
          | Sig_extern_typ (eref, se) -> 
              spr "(extern_typ %s)" (sigelt2string se)
          | Sig_query (id, f) -> 
              spr "(query %s %s)" (lident2string id) (typ2string f "")
          | Sig_ghost_assume (id, f, a) ->
              spr "(ghost_assume %s TODO)" (lident2string id)
    in 
    let sigList = List.map sigelt2string s in
      String.concat "\n" sigList


