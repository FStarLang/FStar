(*
   Copyright 2017-2019 Microsoft Research

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

module FStar.TypeChecker.NBETerm
open FStar.Pervasives
open FStar.Compiler.Effect
open FStar
open FStar.Compiler
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Errors
open FStar.Char
open FStar.String

(**** NOTE: Don't say I didn't warn you! ***)
(* FV and Construct accumulate arguments *in reverse order*.
 * Therefore the embeddings must be aware of this and match/construct
 * them properly
 *
 * For example, this is how we embed/unembed an `option a`:
 *
    embed:
    match o with
    | Some x ->
         lid_as_constr PC.some_lid [U_zero] [as_arg (embed ea cb x); as_iarg (type_of ea)]

    unembed:
    match t with
    | Construct (fvar, us, [(a, _); _]) when S.fv_eq_lid fvar PC.some_lid
         BU.bind_opt (unembed ea cb a) (fun a -> Some (Some a))
 *
 * Note how the implicit argument is seemingly *after* the explicit one.
 *)

module PC = FStar.Parser.Const
module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module P = FStar.Syntax.Print
module BU = FStar.Compiler.Util
module Env = FStar.TypeChecker.Env
module Z = FStar.BigInt
module C = FStar.Const
module Range = FStar.Compiler.Range
module SE = FStar.Syntax.Embeddings
open FStar.VConfig

// NBE term manipulation

let isAccu (trm:t) =
match trm.nbe_t with
| Accu _ -> true
| _ -> false

let isNotAccu (x:t) =
match x.nbe_t with
| Accu (_, _) -> false
| _ -> true

let mk_rt r t = { nbe_t = t; nbe_r = r }
let mk_t t = mk_rt Range.dummyRange t
let nbe_t_of_t t = t.nbe_t
let mkConstruct i us ts = mk_t <| Construct(i, us, ts)
let mkFV i us ts = mk_rt (S.range_of_fv i) (FV(i, us, ts))

let mkAccuVar (v:var) = mk_rt (S.range_of_bv v) (Accu(Var v, []))
let mkAccuMatch (s:t) (ret:(unit -> option match_returns_ascription)) (bs:(unit -> list branch))
  (rc:unit -> option S.residual_comp) =
  mk_t <| Accu(Match (s, ret, bs, rc), [])

// Term equality

let equal_if = function
  | true -> U.Equal
  | _ -> U.Unknown

let equal_iff = function
  | true -> U.Equal
  | _ -> U.NotEqual

let eq_inj r1 r2 =
  match r1, r2 with
  | U.Equal, U.Equal -> U.Equal
  |  U.NotEqual, _
  | _, U.NotEqual -> U.NotEqual
  | U.Unknown, _
  | _, U.Unknown -> U.Unknown

let eq_and f g =
  match f with
  | U.Equal -> g()
  | _ -> U.Unknown

let eq_constant (c1 : constant) (c2 : constant) =
match c1, c2 with
| Unit, Unit -> U.Equal
| Bool b1, Bool b2 -> equal_iff (b1 = b2)
| Int i1, Int i2 -> equal_iff (i1 = i2)
| String (s1, _), String (s2, _) -> equal_iff (s1 = s2)
| Char c1, Char c2 -> equal_iff (c1 = c2)
| Range r1, Range r2 -> U.Unknown (* Seems that ranges are opaque *)
| _, _ -> U.NotEqual


let rec eq_t (t1 : t) (t2 : t) : U.eq_result =
  match t1.nbe_t, t2.nbe_t with
  | Lam _, Lam _ -> U.Unknown
  | Accu(a1, as1), Accu(a2, as2) -> eq_and (eq_atom a1 a2) (fun () -> eq_args as1 as2)
  | Construct(v1, us1, args1), Construct(v2, us2, args2) ->
    if S.fv_eq v1 v2 then begin
        if List.length args1 <> List.length args2 then
            failwith "eq_t, different number of args on Construct";
        List.fold_left (fun acc ((a1, _), (a2, _)) ->
                            eq_inj acc (eq_t a1 a2)) U.Equal <| List.zip args1 args2
    end else U.NotEqual

  | FV(v1, us1, args1), FV(v2, us2, args2) ->
    if S.fv_eq v1 v2 then
     eq_and (equal_iff (U.eq_univs_list us1 us2)) (fun () -> eq_args args1 args2)
    else U.Unknown

  | Constant c1, Constant c2 -> eq_constant c1 c2
  | Type_t u1, Type_t u2
  | Univ u1, Univ u2 -> equal_iff (U.eq_univs u1 u2)
  | Refinement(r1, t1), Refinement(r2, t2) ->
    let x =  S.new_bv None S.t_unit in (* bogus type *)
    eq_and (eq_t (fst (t1 ())) (fst (t2 ()))) (fun () -> eq_t (r1 (mkAccuVar x)) (r2 (mkAccuVar x)))
  | Unknown, Unknown -> U.Equal
  | _, _ -> U.Unknown (* XXX following eq_tm *)

and eq_atom (a1 : atom) (a2 : atom) : U.eq_result =
  match a1, a2 with
  | Var bv1, Var bv2 -> equal_if (bv_eq bv1 bv2) (* ZP : TODO if or iff?? *)
  | _, _ -> U.Unknown (* XXX Cannot compare suspended matches (?) *)

and eq_arg (a1 : arg) (a2 : arg) = eq_t (fst a1) (fst a2)
and eq_args (as1 : args) (as2 : args) : U.eq_result =
match as1, as2 with
| [], [] -> U.Equal
| x :: xs, y :: ys -> eq_and (eq_arg x y) (fun () -> eq_args xs ys)
| _, _ -> U.Unknown (* ZP: following tm_eq, but why not U.NotEqual? *)


// Printing functions

let constant_to_string (c: constant) =
  match c with
  | Unit -> "Unit"
  | Bool b -> if b then "Bool true" else "Bool false"
  | Int i -> Z.string_of_big_int i
  | Char c -> BU.format1 "'%s'" (BU.string_of_char c)
  | String (s, _) -> BU.format1 "\"%s\"" s
  | Range r -> BU.format1 "Range %s" (Range.string_of_range r)
  | SConst s -> P.const_to_string s

let rec t_to_string (x:t) =
  match x.nbe_t with
  | Lam (b, _, arity) -> BU.format1 "Lam (_, %s args)"  (BU.string_of_int arity)
  | Accu (a, l) ->
    "Accu (" ^ (atom_to_string a) ^ ") (" ^
    (String.concat "; " (List.map (fun x -> t_to_string (fst x)) l)) ^ ")"
  | Construct (fv, us, l) ->
    "Construct (" ^ (P.fv_to_string fv) ^ ") [" ^
    (String.concat "; "(List.map P.univ_to_string us)) ^ "] [" ^
    (String.concat "; " (List.map (fun x -> t_to_string (fst x)) l)) ^ "]"
  | FV (fv, us, l) ->
    "FV (" ^ (P.fv_to_string fv) ^ ") [" ^
    (String.concat "; "(List.map P.univ_to_string us)) ^ "] [" ^
    (String.concat "; " (List.map (fun x -> t_to_string (fst x)) l)) ^ "]"
  | Constant c -> constant_to_string c
  | Univ u -> "Universe " ^ (P.univ_to_string u)
  | Type_t u -> "Type_t " ^ (P.univ_to_string u)
  | Arrow _ -> "Arrow" // TODO : revisit
  | Refinement (f, t) ->
    let x =  S.new_bv None S.t_unit in (* bogus type *)
    let t = fst (t ()) in
    "Refinement " ^ (P.bv_to_string x) ^ ":" ^ (t_to_string t) ^ "{" ^ (t_to_string (f (mkAccuVar x))) ^ "}"
  | Unknown -> "Unknown"
  | Reflect t -> "Reflect " ^ t_to_string t
  | Quote _ -> "Quote _"
  | Lazy (Inl li, _) -> BU.format1 "Lazy (Inl {%s})" (P.term_to_string (U.unfold_lazy li))
  | Lazy (Inr (_, et), _) -> BU.format1 "Lazy (Inr (?, %s))" (P.emb_typ_to_string et)
  | LocalLetRec (_, l, _, _, _, _, _) -> "LocalLetRec (" ^ (FStar.Syntax.Print.lbs_to_string [] (true, [l])) ^ ")"
  | TopLevelLet (lb, _, _) -> "TopLevelLet (" ^ FStar.Syntax.Print.fv_to_string (BU.right lb.lbname) ^ ")"
  | TopLevelRec (lb, _, _, _) -> "TopLevelRec (" ^ FStar.Syntax.Print.fv_to_string (BU.right lb.lbname) ^ ")"
  | Meta (t, _) -> "Meta " ^ t_to_string t
and atom_to_string (a: atom) =
  match a with
  | Var v -> "Var " ^ (P.bv_to_string v)
  | Match (t, _, _, _) -> "Match " ^ (t_to_string t)
  | UnreducedLet (var, typ, def, body, lb) -> "UnreducedLet(" ^ (FStar.Syntax.Print.lbs_to_string [] (false, [lb])) ^ " in ...)"
  | UnreducedLetRec (_, body, lbs) -> "UnreducedLetRec(" ^ (FStar.Syntax.Print.lbs_to_string [] (true, lbs)) ^ " in " ^ (t_to_string body) ^ ")"
  | UVar _ -> "UVar"

let arg_to_string (a : arg) = a |> fst |> t_to_string

let args_to_string args = args |> List.map arg_to_string |> String.concat " "

// Embedding and de-embedding

let iapp_cb cbs    h a = cbs.iapp h a
let translate_cb cbs t = cbs.translate t

let embed   (e:embedding 'a) (cb:nbe_cbs) (x:'a) : t = e.em cb x
let unembed (e:embedding 'a) (cb:nbe_cbs) (trm:t) : option 'a = e.un cb trm
let type_of (e:embedding 'a) : t = e.typ


let mk_emb em un typ et = {em = em; un = un; typ = typ; emb_typ=et}
let mk_emb' em un = mk_emb (fun cbs t -> mk_t <| em cbs t) (fun cbs t -> un cbs t.nbe_t)


let embed_as (ea:embedding 'a)
             (ab : 'a -> 'b)
             (ba : 'b -> 'a)
             (ot:option t)
             : embedding 'b
 = mk_emb (fun cbs (x:'b) -> embed ea cbs (ba x))
          (fun cbs t -> BU.map_opt (unembed ea cbs t) ab)
          (match ot with | Some t -> t | None -> ea.typ)
          ea.emb_typ

let lid_as_constr (l:lident) (us:list universe) (args:args) : t =
    mkConstruct (lid_as_fv l S.delta_constant (Some Data_ctor)) us args

let lid_as_typ (l:lident) (us:list universe) (args:args) : t =
    mkFV (lid_as_fv l S.delta_constant None) us args

let as_iarg (a:t) : arg = (a, S.as_aqual_implicit true)
let as_arg (a:t) : arg = (a, None)

//  Non-dependent total arrow
let make_arrow1 t1 (a:arg) : t = mk_t <| Arrow (Inr ([a], Tot (t1, None)))

let lazy_embed (et:emb_typ) (x:'a) (f:unit -> t) =
    if !Options.debug_embedding
    then BU.print1 "Embedding\n\temb_typ=%s\n"
                         (P.emb_typ_to_string et);
    if !Options.eager_embedding
    then f()
    else let thunk = Thunk.mk f in
         let li = FStar.Compiler.Dyn.mkdyn x, et in
         mk_t <| Lazy (Inr li, thunk)

let lazy_unembed cb (et:emb_typ) (x:t) (f:t -> option 'a) : option 'a =
    match x.nbe_t with
    | Lazy (Inl li, thunk) ->
      f (Thunk.force thunk)

    | Lazy (Inr (b, et'), thunk) ->
      if et <> et'
      || !Options.eager_embedding
      then let res = f (Thunk.force thunk) in
           let _ = if !Options.debug_embedding
                   then BU.print2 "Unembed cancellation failed\n\t%s <> %s\n"
                                (P.emb_typ_to_string et)
                                (P.emb_typ_to_string et')
           in
           res
      else let a = FStar.Compiler.Dyn.undyn b in
           let _ = if !Options.debug_embedding
                   then BU.print1 "Unembed cancelled for %s\n"
                                     (P.emb_typ_to_string et)
           in
           Some a
    | _ ->
      let aopt = f x in
      let _ = if !Options.debug_embedding
              then BU.print1 "Unembedding:\n\temb_typ=%s\n"
                               (P.emb_typ_to_string et) in
      aopt


// Emdebbing for polymorphic types
let mk_any_emb (ty:t) : embedding t =
    let em = (fun _cb a -> a) in
    let un = (fun _cb t -> Some t) in
    mk_emb em un ty ET_abstract

// Emdebbing at abstract types
let e_any : embedding t =
    let em = (fun _cb a -> a) in
    let un = (fun _cb t -> Some t) in
    mk_emb em un (lid_as_typ PC.term_lid [] []) ET_abstract

// Emdebbing at type unit
let e_unit : embedding unit =
    let em _cb a = Constant Unit in
    let un _cb t = Some () in // No runtime typecheck here
    mk_emb' em un (lid_as_typ PC.unit_lid [] []) (SE.emb_typ_of SE.e_unit)

// Embedding at type bool
let e_bool : embedding bool =
    let em _cb a = Constant (Bool a) in
    let un _cb t =
      match t with
      | Constant (Bool a) -> Some a
      | _ -> None
    in
    mk_emb' em un (lid_as_typ PC.bool_lid [] []) (SE.emb_typ_of SE.e_unit)

// Embeddind at type char
let e_char : embedding char =
    let em _cb c = Constant (Char c) in
    let un _cb c =
      match c with
      | Constant (Char a) -> Some a
      | _ -> None
    in
    mk_emb' em un (lid_as_typ PC.char_lid [] []) (SE.emb_typ_of SE.e_char)

// Embeddind at type string
let e_string : embedding string =
  let em _cb s = Constant (String (s, Range.dummyRange)) in
  let un _cb s =
    match s with
    | Constant (String (s, _)) -> Some s
    | _ -> None
  in
  mk_emb' em un (lid_as_typ PC.string_lid [] []) (SE.emb_typ_of SE.e_string)

// Embeddind at type int
let e_int : embedding Z.t =
    let em _cb c = Constant (Int c) in
    let un _cb c =
        match c with
        | Constant (Int a) -> Some a
        | _ -> None
    in
    mk_emb' em un (lid_as_typ PC.int_lid [] [])  (SE.emb_typ_of SE.e_int)

// Embedding at option type
let e_option (ea : embedding 'a) =
    let etyp =
        ET_app(PC.option_lid |> Ident.string_of_lid, [ea.emb_typ])
    in
    let em cb (o:option 'a) : t =
        lazy_embed etyp o (fun () ->
        match o with
        | None ->
          lid_as_constr PC.none_lid [U_zero] [as_iarg (type_of ea)]
        | Some x ->
          lid_as_constr PC.some_lid [U_zero] [as_arg (embed ea cb x);
                                              as_iarg (type_of ea)])
    in
    let un cb (trm:t) : option (option 'a) =
        lazy_unembed cb etyp trm (fun trm ->
        match trm.nbe_t with
        | Construct (fvar, us, args) when S.fv_eq_lid fvar PC.none_lid ->
          Some None
        | Construct (fvar, us, [(a, _); _]) when S.fv_eq_lid fvar PC.some_lid ->
          BU.bind_opt (unembed ea cb a) (fun a -> Some (Some a))
        | _ -> None)
    in
    mk_emb em un (lid_as_typ PC.option_lid [U_zero] [as_arg (type_of ea)]) etyp


// Emdedding tuples
let e_tuple2 (ea:embedding 'a) (eb:embedding 'b) =
    let etyp =
        ET_app(PC.lid_tuple2 |> Ident.string_of_lid, [ea.emb_typ; eb.emb_typ])
    in
    let em cb (x:'a * 'b) : t =
        lazy_embed etyp x (fun () ->
        lid_as_constr (PC.lid_Mktuple2)
                      [U_zero; U_zero]
                      [as_arg (embed eb cb (snd x));
                       as_arg (embed ea cb (fst x));
                       as_iarg (type_of eb);
                       as_iarg (type_of ea)])
    in
    let un cb (trm:t) : option ('a * 'b) =
        lazy_unembed cb etyp trm (fun trm ->
        match trm.nbe_t with
        | Construct (fvar, us, [(b, _); (a, _); _; _]) when S.fv_eq_lid fvar PC.lid_Mktuple2 ->
          BU.bind_opt (unembed ea cb a) (fun a ->
          BU.bind_opt (unembed eb cb b) (fun b ->
          Some (a, b)))
        | _ -> None)
    in
    mk_emb em un (lid_as_typ PC.lid_tuple2 [U_zero;U_zero] [as_arg (type_of eb); as_arg (type_of ea)]) etyp

let e_tuple3 (ea:embedding 'a) (eb:embedding 'b) (ec:embedding 'c) =
    let etyp =
        ET_app(PC.lid_tuple3 |> Ident.string_of_lid, [ea.emb_typ; eb.emb_typ; ec.emb_typ])
    in
    let em cb ((x1, x2, x3):('a * 'b * 'c)) : t =
        lazy_embed etyp (x1, x2, x3) (fun () ->
        lid_as_constr (PC.lid_Mktuple3)
                      [U_zero; U_zero; U_zero]
                      [as_arg (embed ec cb x3);
                       as_arg (embed eb cb x2);
                       as_arg (embed ea cb x1);
                       as_iarg (type_of ec);
                       as_iarg (type_of eb);
                       as_iarg (type_of ea)])
    in
    let un cb (trm:t) : option ('a * 'b * 'c) =
        lazy_unembed cb etyp trm (fun trm ->
        match trm.nbe_t with
        | Construct (fvar, us, [(c, _); (b, _); (a, _); _; _]) when S.fv_eq_lid fvar PC.lid_Mktuple3 ->
          BU.bind_opt (unembed ea cb a) (fun a ->
          BU.bind_opt (unembed eb cb b) (fun b ->
          BU.bind_opt (unembed ec cb c) (fun c ->
          Some (a, b, c))))
        | _ -> None)
    in
    mk_emb em un (lid_as_typ PC.lid_tuple3 [U_zero;U_zero;U_zero] [as_arg (type_of ec); as_arg (type_of eb); as_arg (type_of ea)]) etyp

let e_either (ea:embedding 'a) (eb:embedding 'b) =
    let etyp =
        ET_app(PC.either_lid |> Ident.string_of_lid, [ea.emb_typ; eb.emb_typ])
    in
    let em cb (s:either 'a 'b) : t =
        lazy_embed etyp s (fun () ->
        match s with
        | Inl a ->
        lid_as_constr (PC.inl_lid)
                      [U_zero; U_zero]
                      [as_arg (embed ea cb a);
                       as_iarg (type_of eb);
                       as_iarg (type_of ea)]
        | Inr b ->
        lid_as_constr (PC.inr_lid)
                      [U_zero; U_zero]
                      [as_arg (embed eb cb b);
                       as_iarg (type_of eb);
                       as_iarg (type_of ea)])
    in
    let un cb (trm:t) : option (either 'a 'b) =
        lazy_unembed cb etyp trm (fun trm ->
        match trm.nbe_t with
        | Construct (fvar, us, [(a, _); _; _]) when S.fv_eq_lid fvar PC.inl_lid ->
          BU.bind_opt (unembed ea cb a) (fun a ->
          Some (Inl a))
        | Construct (fvar, us, [(b, _); _; _]) when S.fv_eq_lid fvar PC.inr_lid ->
          BU.bind_opt (unembed eb cb b) (fun b ->
          Some (Inr b))
        | _ -> None)
    in
    mk_emb em un (lid_as_typ PC.either_lid [U_zero;U_zero] [as_arg (type_of eb); as_arg (type_of ea)]) etyp

// Embedding range
let e_range : embedding Range.range =
    let em cb r = Constant (Range r) in
    let un cb t =
    match t with
    | Constant (Range r) -> Some r
    | _ ->
        None
    in
    mk_emb' em un (lid_as_typ PC.range_lid [] []) (SE.emb_typ_of SE.e_range)

// vconfig, NYI
let e_vconfig : embedding vconfig =
    let em cb r = failwith "e_vconfig NBE" in
    let un cb t = failwith "e_vconfig NBE" in
    mk_emb' em un (lid_as_typ PC.vconfig_lid [] []) (SE.emb_typ_of SE.e_vconfig)

// Emdedding lists
let e_list (ea:embedding 'a) =
    let etyp =
        ET_app(PC.list_lid |> Ident.string_of_lid, [ea.emb_typ])
    in
    let em cb (l:list 'a) : t =
        lazy_embed etyp l (fun () ->
        let typ = as_iarg (type_of ea) in
        let nil = lid_as_constr PC.nil_lid [U_zero] [typ] in
        let cons hd tl = lid_as_constr PC.cons_lid [U_zero] [as_arg tl; as_arg (embed ea cb hd); typ] in
        List.fold_right cons l nil)
    in
    let rec un cb (trm:t) : option (list 'a) =
        lazy_unembed cb etyp trm (fun trm ->
        match trm.nbe_t with
        | Construct (fv, _, _) when S.fv_eq_lid fv PC.nil_lid -> Some []
        | Construct (fv, _, [(tl, None); (hd, None); (_, Some ({ aqual_implicit = true }))])
          // Zoe: Not sure why this case is need; following Emdeddings.fs
          // GM: Maybe it's not, but I'm unsure on whether we can rely on all these terms being type-correct
        | Construct (fv, _, [(tl, None); (hd, None)])
            when S.fv_eq_lid fv PC.cons_lid ->
          BU.bind_opt (unembed ea cb hd) (fun hd ->
          BU.bind_opt (un cb tl) (fun tl ->
          Some (hd :: tl)))
        | _ -> None)
    in
    mk_emb em un (lid_as_typ PC.list_lid [U_zero] [as_arg (type_of ea)]) etyp

let e_string_list = e_list e_string

let e_arrow (ea:embedding 'a) (eb:embedding 'b) : embedding ('a -> 'b) =
    let etyp = ET_fun(ea.emb_typ, eb.emb_typ) in
    let em cb (f : 'a -> 'b) : t =
        lazy_embed etyp f (fun () ->
        mk_t <| Lam ((fun tas -> match unembed ea cb (tas |> List.hd |> fst) with
                             | Some a -> embed eb cb (f a)
                             | None -> failwith "cannot unembed function argument"),
               Inr [as_arg (type_of eb)],
               1))
    in
    let un cb (lam : t) : option ('a -> 'b) =
        let k (lam:t) : option ('a -> 'b) =
            Some (fun (x:'a) -> match unembed eb cb (cb.iapp lam [as_arg (embed ea cb x)]) with
                                | Some y -> y
                                | None -> failwith "cannot unembed function result")
        in
        lazy_unembed cb etyp lam k
    in
    mk_emb em un (make_arrow1 (type_of ea) (as_iarg (type_of eb))) etyp

let e_norm_step =
    let em cb (n:SE.norm_step) : t =
        match n with
        | SE.Simpl   -> mkFV (lid_as_fv PC.steps_simpl     S.delta_constant None) [] []
        | SE.Weak    -> mkFV (lid_as_fv PC.steps_weak      S.delta_constant None) [] []
        | SE.HNF     -> mkFV (lid_as_fv PC.steps_hnf       S.delta_constant None) [] []
        | SE.Primops -> mkFV (lid_as_fv PC.steps_primops   S.delta_constant None) [] []
        | SE.Delta   -> mkFV (lid_as_fv PC.steps_delta     S.delta_constant None) [] []
        | SE.Zeta    -> mkFV (lid_as_fv PC.steps_zeta      S.delta_constant None) [] []
        | SE.Iota    -> mkFV (lid_as_fv PC.steps_iota      S.delta_constant None) [] []
        | SE.Reify   -> mkFV (lid_as_fv PC.steps_reify     S.delta_constant None) [] []
        | SE.NBE     -> mkFV (lid_as_fv PC.steps_nbe       S.delta_constant None) [] []
        | SE.UnfoldOnly l ->
                     mkFV (lid_as_fv PC.steps_unfoldonly S.delta_constant None)
                          [] [as_arg (embed (e_list e_string) cb l)]
        | SE.UnfoldFully l ->
                     mkFV (lid_as_fv PC.steps_unfoldfully S.delta_constant None)
                          [] [as_arg (embed (e_list e_string) cb l)]
        | SE.UnfoldAttr l ->
                     mkFV (lid_as_fv PC.steps_unfoldattr S.delta_constant None)
                          [] [as_arg (embed (e_list e_string) cb l)]
        | SE.ZetaFull -> mkFV (lid_as_fv PC.steps_zeta_full S.delta_constant None) [] []
        | SE.Unascribe -> mkFV (lid_as_fv PC.steps_unascribe S.delta_constant None) [] []
    in
    let un cb (t0:t) : option SE.norm_step =
        match t0.nbe_t with
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_simpl ->
            Some SE.Simpl
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_weak ->
            Some SE.Weak
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_hnf ->
            Some SE.HNF
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_primops ->
            Some SE.Primops
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_delta ->
            Some SE.Delta
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_zeta ->
            Some SE.Zeta
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_iota ->
            Some SE.Iota
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_nbe ->
            Some SE.NBE
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_reify ->
            Some SE.Reify
        | FV (fv, _, [(l, _)]) when S.fv_eq_lid fv PC.steps_unfoldonly ->
            BU.bind_opt (unembed (e_list e_string) cb l) (fun ss ->
            Some <| SE.UnfoldOnly ss)
        | FV (fv, _, [(l, _)]) when S.fv_eq_lid fv PC.steps_unfoldfully ->
            BU.bind_opt (unembed (e_list e_string) cb l) (fun ss ->
            Some <| SE.UnfoldFully ss)
        | FV (fv, _, [(l, _)]) when S.fv_eq_lid fv PC.steps_unfoldattr ->
            BU.bind_opt (unembed (e_list e_string) cb l) (fun ss ->
            Some <| SE.UnfoldAttr ss)
        | _ ->
            Errors.log_issue Range.dummyRange (Errors.Warning_NotEmbedded, (BU.format1 "Not an embedded norm_step: %s" (t_to_string t0)));
            None
    in
    mk_emb em un (mkFV (lid_as_fv PC.norm_step_lid delta_constant None) [] []) (SE.emb_typ_of SE.e_norm_step)

(* Interface for building primitive steps *)

let bogus_cbs = {
    iapp = (fun h _args -> h);
    translate = (fun _ -> failwith "bogus_cbs translate");
}

let arg_as_int    (a:arg) = fst a |> unembed e_int bogus_cbs

let arg_as_bool   (a:arg) = fst a |> unembed e_bool bogus_cbs

let arg_as_char   (a:arg) = fst a |> unembed e_char  bogus_cbs

let arg_as_string (a:arg) = fst a |> unembed e_string  bogus_cbs

let arg_as_list   (e:embedding 'a) (a:arg) = fst a |> unembed (e_list e) bogus_cbs

let arg_as_bounded_int ((a, _) : arg) : option (fv * Z.t * option S.meta_source_info) =
    let (a, m) =
      (match a.nbe_t with
       | Meta(t, tm) ->
         (match Thunk.force tm with
          | Meta_desugared m -> (t, Some m)
          | _ -> (a, None))
       | _ -> (a, None)) in
    match a.nbe_t with
    | FV (fv1, [], [({nbe_t=Constant (Int i)}, _)])
      when BU.ends_with (Ident.string_of_lid fv1.fv_name.v)
                        "int_to_t" ->
      Some (fv1, i, m)
    | _ -> None

let int_as_bounded int_to_t n =
    let c = embed e_int bogus_cbs n in
    let int_to_t args = mk_t <| FV(int_to_t, [], args) in
    int_to_t [as_arg c]

let with_meta_ds t (m:option meta_source_info) =
      match m with
      | None -> t
      | Some m -> mk_t (Meta(t, Thunk.mk (fun _ -> Meta_desugared m)))


(* XXX a lot of code duplication. Same code as in cfg.fs *)
let lift_unary (f : 'a -> 'b) (aopts : list (option 'a)) : option 'b =
        match aopts with
        | [Some a] -> Some (f a)
        | _ -> None


let lift_binary (f : 'a -> 'a -> 'b) (aopts : list (option 'a)) : option 'b =
        match aopts with
        | [Some a0; Some a1] -> Some (f a0 a1)
        | _ -> None

let unary_op (as_a : arg -> option 'a) (f : 'a -> t) (args : args) : option t =
    lift_unary f (List.map as_a args)

let binary_op (as_a : arg -> option 'a) (f : 'a -> 'a -> t) (args : args) : option t =
    lift_binary f (List.map as_a args)

let unary_int_op (f:Z.t -> Z.t) =
    unary_op arg_as_int (fun x -> embed e_int bogus_cbs (f x))

let binary_int_op (f:Z.t -> Z.t -> Z.t) =
    binary_op arg_as_int (fun x y -> embed e_int bogus_cbs (f x y))

let unary_bool_op (f:bool -> bool) =
    unary_op arg_as_bool (fun x -> embed e_bool bogus_cbs (f x))

let binary_bool_op (f:bool -> bool -> bool) =
    binary_op arg_as_bool (fun x y -> embed e_bool bogus_cbs (f x y))

let binary_string_op (f : string -> string -> string) =
    binary_op arg_as_string (fun x y -> embed e_string bogus_cbs (f x y))

let mixed_binary_op (as_a : arg -> option 'a) (as_b : arg -> option 'b)
       (embed_c : 'c -> t) (f : 'a -> 'b -> option 'c) (args : args) : option t =
             match args with
             | [a;b] ->
                begin
                match as_a a, as_b b with
                | Some a, Some b ->
                  (match f a b with
                   | Some c -> Some (embed_c c)
                   | _ -> None)
                | _ -> None
                end
             | _ -> None

let list_of_string' (s:string) : t =
  embed (e_list e_char) bogus_cbs (list_of_string s)
  // let name l = mk (Tm_fvar (lid_as_fv l delta_constant None)) rng in
  // let char_t = name PC.char_lid in
  // let charterm c = mk (Tm_constant (Const_char c)) rng in
  // U.mk_list char_t rng <| List.map charterm (list_of_string s)

let string_of_list' (l:list char) : t =
    let s = string_of_list l in
    mk_t <| Constant (String (s, Range.dummyRange))

let string_compare' (s1:string) (s2:string) : t =
    let r = String.compare s1 s2 in
    embed e_int bogus_cbs (Z.big_int_of_string (BU.string_of_int r))


let string_concat' args : option t =
    match args with
    | [a1; a2] ->
        begin match arg_as_string a1 with
        | Some s1 ->
            begin match arg_as_list e_string a2 with
            | Some s2 ->
                let r = String.concat s1 s2 in
                Some (embed e_string bogus_cbs r)
            | _ -> None
            end
        | _ -> None
        end
    | _ -> None

let string_of_int (i:Z.t) : t =
    embed e_string bogus_cbs (Z.string_of_big_int i)

let string_of_bool (b:bool) : t =
    embed e_string bogus_cbs (if b then "true" else "false")

let string_lowercase (s:string) : t =
    embed e_string bogus_cbs (String.lowercase s)

let string_uppercase (s:string) : t =
    embed e_string bogus_cbs (String.lowercase s)

let decidable_eq (neg:bool) (args:args) : option t =
  let tru = embed e_bool bogus_cbs true in
  let fal = embed e_bool bogus_cbs false in
  match args with
  | [(_typ, _); (a1, _); (a2, _)] ->
     //BU.print2 "Comparing %s and %s.\n" (t_to_string a1) (t_to_string a2);
     begin match eq_t a1 a2 with
     | U.Equal -> Some (if neg then fal else tru)
     | U.NotEqual -> Some (if neg then tru else fal)
     | _ -> None
     end
  | _ ->
   failwith "Unexpected number of arguments"


let interp_prop_eq2 (args:args) : option t =
    match args with
    | [(_u, _); (_typ, _); (a1, _); (a2, _)] ->  //eq2
      begin match eq_t a1 a2 with
      | U.Equal -> Some (embed e_bool bogus_cbs true)
      | U.NotEqual -> Some (embed e_bool bogus_cbs false)
      | U.Unknown -> None
      end
   | _ -> failwith "Unexpected number of arguments"

let dummy_interp (lid : Ident.lid) (args : args) : option t =
    failwith ("No interpretation for " ^ (Ident.string_of_lid lid))

let prims_to_fstar_range_step (args:args) : option t =
    match args with
    | [(a1, _)] ->
      begin match unembed e_range bogus_cbs a1 with
      | Some r -> Some (embed e_range bogus_cbs r)
      | None ->
        None
      end
   | _ -> failwith "Unexpected number of arguments"


let string_split' args : option t =
    match args with
    | [a1; a2] ->
        begin match arg_as_list e_char a1 with
        | Some s1 ->
            begin match arg_as_string a2 with
            | Some s2 ->
                let r = String.split s1 s2 in
                Some (embed (e_list e_string) bogus_cbs r)
            | _ -> None
            end
        | _ -> None
        end
    | _ -> None


let string_index args : option t =
    match args with
    | [a1; a2] ->
        begin match arg_as_string a1, arg_as_int a2 with
        | Some s, Some i ->
          begin
          try
            let r = String.index s i in
            Some (embed e_char bogus_cbs r)
          with
          | _ -> None
          end
        | _ -> None
        end
    | _ -> None

let string_index_of args : option t =
    match args with
    | [a1; a2] ->
        begin match arg_as_string a1, arg_as_char a2 with
        | Some s, Some c ->
          begin
          try
            let r = String.index_of s c in
            Some (embed e_int bogus_cbs r)
          with
          | _ -> None
          end
        | _ -> None
        end
    | _ -> None


let string_substring' args : option t =
  match args with
  | [a1; a2; a3] ->
      begin match arg_as_string a1, arg_as_int a2, arg_as_int a3 with
      | Some s1, Some n1, Some n2 ->
        let n1 = Z.to_int_fs n1 in
        let n2 = Z.to_int_fs n2 in
        begin
        try let r = String.substring s1 n1 n2 in
            Some (embed e_string bogus_cbs r)
        with | _ -> None
        end
    | _ -> None
    end

| _ -> None

let mk_range args : option t =
  match args with
  | [fn; from_line; from_col; to_line; to_col] -> begin
    match arg_as_string fn,
          arg_as_int from_line,
          arg_as_int from_col,
          arg_as_int to_line,
          arg_as_int to_col with
    | Some fn, Some from_l, Some from_c, Some to_l, Some to_c ->
      let r = FStar.Compiler.Range.mk_range fn
                (FStar.Compiler.Range.mk_pos (Z.to_int_fs from_l) (Z.to_int_fs from_c))
                (FStar.Compiler.Range.mk_pos (Z.to_int_fs to_l) (Z.to_int_fs to_c)) in
      Some (embed e_range bogus_cbs r)
    | _ -> None
    end
| _ -> None

let and_op (args:args) : option t =
  match args with
  | [a1; a2] -> begin
    match arg_as_bool a1 with
    | Some false ->
      Some (embed e_bool bogus_cbs false)
    | Some true ->
      Some (fst a2)
    | _ -> None
    end
  | _ -> failwith "Unexpected number of arguments"

let or_op (args:args) : option t =
  match args with
  | [a1; a2] -> begin
    match arg_as_bool a1 with
    | Some true ->
      Some (embed e_bool bogus_cbs true)
    | Some false ->
      Some (fst a2)
    | _ -> None
    end
  | _ -> failwith "Unexpected number of arguments"

let division_op (args:args) : option t =
  match args with
  | [a1; a2] -> begin
    match arg_as_int a1, arg_as_int a2 with
    | Some m, Some n ->
      if Z.to_int_fs n <> 0
      then Some (embed e_int bogus_cbs (Z.div_big_int m n))
      else None
    | _ -> None
    end
  | _ -> failwith "Unexpected number of arguments"

// let e_arrow2 (ea:embedding 'a) (eb:embedding 'b) (ec:embedding 'c) =
//   let em (f : 'a -> 'b -> 'c) : t = Lam((fun (ta:t) -> match unembed ea ta with
//                                            | Some a -> embed eb (f a)
//                                            | None -> failwith "Cannot unembed argument"),
//                                     (fun _ -> type_of ea), None)
//   in
//   let un (lam : t) : option ('a -> 'b) =
//       match lam with
//       | Lam (ft, _, _) -> Some (fun (x:'a) -> match unembed eb (ft (embed ea x)) with
//                                          | Some b -> b
//                                          | None -> failwith "Cannot unembed function result")
//       | _ -> None
//   in
//   mk_emb em un (make_arrow1 (type_of ea) (as_iarg (type_of eb)))



let arrow_as_prim_step_1 (ea:embedding 'a) (eb:embedding 'b)
                         (f:'a -> 'b) (n_tvars:int) (_fv_lid:Ident.lid) cb
   : args -> option t =
    let f_wrapped args =
        let _tvar_args, rest_args = List.splitAt n_tvars args in
        let x, _ = List.hd rest_args in //arity mismatches are handled by code that dispatches here
        BU.map_opt
                (unembed ea cb x) (fun x ->
                 embed eb cb (f x))
    in
    f_wrapped

let arrow_as_prim_step_2 (ea:embedding 'a) (eb:embedding 'b) (ec:embedding 'c)
                         (f:'a -> 'b -> 'c) (n_tvars:int) (_fv_lid:Ident.lid) cb
   : args -> option t =
    let f_wrapped args =
        let _tvar_args, rest_args = List.splitAt n_tvars args in
        let x, _ = List.hd rest_args in //arity mismatches are handled by code that dispatches here
        let y, _ = List.hd (List.tl rest_args) in
        BU.bind_opt (unembed ea cb x) (fun x ->
        BU.bind_opt (unembed eb cb y) (fun y ->
        Some (embed ec cb (f x y))))
    in
    f_wrapped


let arrow_as_prim_step_3 (ea:embedding 'a) (eb:embedding 'b)
                         (ec:embedding 'c) (ed:embedding 'd)
                         (f:'a -> 'b -> 'c -> 'd) (n_tvars:int) (_fv_lid:Ident.lid) cb
   : args -> option t =
    let f_wrapped args =
        let _tvar_args, rest_args = List.splitAt n_tvars args in
        let x, _ = List.hd rest_args in //arity mismatches are handled by code that dispatches here
        let y, _ = List.hd (List.tl rest_args) in
        let z, _ = List.hd (List.tl (List.tl rest_args)) in
        BU.bind_opt (unembed ea cb x) (fun x ->
        BU.bind_opt (unembed eb cb y) (fun y ->
        BU.bind_opt (unembed ec cb z) (fun z ->
        Some (embed ed cb (f x y z)))))
    in
    f_wrapped
