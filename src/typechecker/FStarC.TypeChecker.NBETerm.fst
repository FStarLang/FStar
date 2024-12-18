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

module FStarC.TypeChecker.NBETerm
open FStar open FStarC
open FStarC.Compiler
open FStarC.Compiler.Effect
open FStarC.Syntax.Syntax
open FStarC.Errors
open FStar.Char
open FStar.String

friend FStar.Pervasives (* To expose norm_step *)

module PC = FStarC.Parser.Const
module S = FStarC.Syntax.Syntax
module P = FStarC.Syntax.Print
module BU = FStarC.Compiler.Util
module C = FStarC.Const
module SE = FStarC.Syntax.Embeddings
module TEQ = FStarC.TypeChecker.TermEqAndSimplify

open FStarC.VConfig

open FStarC.Class.Show

// NBE term manipulation

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
let interleave_hack = 123

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
  | true -> TEQ.Equal
  | _ -> TEQ.Unknown

let equal_iff = function
  | true -> TEQ.Equal
  | _ -> TEQ.NotEqual

let eq_inj r1 r2 =
  match r1, r2 with
  | TEQ.Equal, TEQ.Equal -> TEQ.Equal
  |  TEQ.NotEqual, _
  | _, TEQ.NotEqual -> TEQ.NotEqual
  | TEQ.Unknown, _
  | _, TEQ.Unknown -> TEQ.Unknown

let eq_and f g =
  match f with
  | TEQ.Equal -> g()
  | _ -> TEQ.Unknown

let eq_constant (c1 : constant) (c2 : constant) =
match c1, c2 with
| Unit, Unit -> TEQ.Equal
| Bool b1, Bool b2 -> equal_iff (b1 = b2)
| Int i1, Int i2 -> equal_iff (i1 = i2)
| String (s1, _), String (s2, _) -> equal_iff (s1 = s2)
| Char c1, Char c2 -> equal_iff (c1 = c2)
| Range r1, Range r2 -> TEQ.Unknown (* Seems that ranges are opaque *)
| Real r1, Real r2 -> equal_if (r1 = r2) (* conservative, cannot use iff since strings could be 1.0 and 01.0 *)
| _, _ -> TEQ.NotEqual


let rec eq_t env (t1 : t) (t2 : t) : TEQ.eq_result =
  match t1.nbe_t, t2.nbe_t with
  | Lam _, Lam _ -> TEQ.Unknown
  | Accu(a1, as1), Accu(a2, as2) -> eq_and (eq_atom a1 a2) (fun () -> eq_args env as1 as2)
  | Construct(v1, us1, args1), Construct(v2, us2, args2) ->
    if S.fv_eq v1 v2 then begin
        if List.length args1 <> List.length args2 then
            failwith "eq_t, different number of args on Construct";
        match Env.num_datacon_non_injective_ty_params env (lid_of_fv v1) with
        | None -> TEQ.Unknown
        | Some n ->
          if n <= List.length args1
          then (
            let eq_args as1 as2 =
              List.fold_left2
                (fun acc (a1, _) (a2, _) -> eq_inj acc (eq_t env a1 a2))
                TEQ.Equal
                as1 as2
            in
            let parms1, args1 = List.splitAt n args1 in
            let parms2, args2 = List.splitAt n args2 in
            eq_args args1 args2
          )
          else TEQ.Unknown
    end else TEQ.NotEqual

  | FV(v1, us1, args1), FV(v2, us2, args2) ->
    if S.fv_eq v1 v2 then
     eq_and (equal_iff (U.eq_univs_list us1 us2)) (fun () -> eq_args env args1 args2)
    else TEQ.Unknown

  | Constant c1, Constant c2 -> eq_constant c1 c2
  | Type_t u1, Type_t u2
  | Univ u1, Univ u2 -> equal_iff (U.eq_univs u1 u2)
  | Refinement(r1, t1), Refinement(r2, t2) ->
    let x =  S.new_bv None S.t_unit in (* bogus type *)
    eq_and (eq_t env (fst (t1 ())) (fst (t2 ()))) (fun () -> eq_t env (r1 (mkAccuVar x)) (r2 (mkAccuVar x)))
  | Unknown, Unknown -> TEQ.Equal
  | _, _ -> TEQ.Unknown (* XXX following eq_tm *)

and eq_atom (a1 : atom) (a2 : atom) : TEQ.eq_result =
  match a1, a2 with
  | Var bv1, Var bv2 -> equal_if (bv_eq bv1 bv2) (* ZP : TODO if or iff?? *)
  | _, _ -> TEQ.Unknown (* XXX Cannot compare suspended matches (?) *)

and eq_arg env (a1 : arg) (a2 : arg) = eq_t env (fst a1) (fst a2)
and eq_args env (as1 : args) (as2 : args) : TEQ.eq_result =
  match as1, as2 with
  | [], [] -> TEQ.Equal
  | x :: xs, y :: ys -> eq_and (eq_arg env x y) (fun () -> eq_args env xs ys)
  | _, _ -> TEQ.Unknown (* ZP: following tm_eq, but why not TEQ.NotEqual? *)


// Printing functions

let constant_to_string (c: constant) =
  match c with
  | Unit -> "Unit"
  | Bool b -> if b then "Bool true" else "Bool false"
  | Int i -> Z.string_of_big_int i
  | Char c -> BU.format1 "'%s'" (BU.string_of_char c)
  | String (s, _) -> BU.format1 "\"%s\"" s
  | Range r -> BU.format1 "Range %s" (Range.string_of_range r)
  | SConst s -> show s
  | Real s -> BU.format1 "Real %s" s

let rec t_to_string (x:t) =
  match x.nbe_t with
  | Lam {interp=b; arity} -> BU.format1 "Lam (_, %s args)"  (BU.string_of_int arity)
  | Accu (a, l) ->
    "Accu (" ^ (atom_to_string a) ^ ") (" ^
    (String.concat "; " (List.map (fun x -> t_to_string (fst x)) l)) ^ ")"
  | Construct (fv, us, l) ->
    "Construct (" ^ (show fv) ^ ") [" ^
    (String.concat "; "(List.map show us)) ^ "] [" ^
    (String.concat "; " (List.map (fun x -> t_to_string (fst x)) l)) ^ "]"
  | FV (fv, us, l) ->
    "FV (" ^ (show fv) ^ ") [" ^
    (String.concat "; "(List.map show us)) ^ "] [" ^
    (String.concat "; " (List.map (fun x -> t_to_string (fst x)) l)) ^ "]"
  | Constant c -> constant_to_string c
  | Univ u -> "Universe " ^ (show u)
  | Type_t u -> "Type_t " ^ (show u)
  | Arrow _ -> "Arrow" // TODO : revisit
  | Refinement (f, t) ->
    let x =  S.new_bv None S.t_unit in (* bogus type *)
    let t = fst (t ()) in
    "Refinement " ^ (show x) ^ ":" ^ (t_to_string t) ^ "{" ^ (t_to_string (f (mkAccuVar x))) ^ "}"
  | Unknown -> "Unknown"
  | Reflect t -> "Reflect " ^ t_to_string t
  | Quote _ -> "Quote _"
  | Lazy (Inl li, _) -> BU.format1 "Lazy (Inl {%s})" (show (U.unfold_lazy li))
  | Lazy (Inr (_, et), _) -> BU.format1 "Lazy (Inr (?, %s))" (show et)
  | LocalLetRec (_, l, _, _, _, _, _) -> "LocalLetRec (" ^ (show (true, [l])) ^ ")"
  | TopLevelLet (lb, _, _) -> "TopLevelLet (" ^ show (BU.right lb.lbname) ^ ")"
  | TopLevelRec (lb, _, _, _) -> "TopLevelRec (" ^ show (BU.right lb.lbname) ^ ")"
  | Meta (t, _) -> "Meta " ^ t_to_string t
and atom_to_string (a: atom) =
  match a with
  | Var v -> "Var " ^ (show v)
  | Match (t, _, _, _) -> "Match " ^ (t_to_string t)
  | UnreducedLet (var, typ, def, body, lb) -> "UnreducedLet(" ^ (show (false, [lb])) ^ " in ...)"
  | UnreducedLetRec (_, body, lbs) -> "UnreducedLetRec(" ^ (show (true, lbs)) ^ " in " ^ (t_to_string body) ^ ")"
  | UVar _ -> "UVar"

let arg_to_string (a : arg) = a |> fst |> t_to_string

let args_to_string args = args |> List.map arg_to_string |> String.concat " "

instance showable_t = {
  show = t_to_string;
}
instance showable_args = {
  show = args_to_string;
}

// Embedding and de-embedding

let iapp_cb cbs    h a = cbs.iapp h a
let translate_cb cbs t = cbs.translate t

let embed   (#a:Type0) (e:embedding a) (cb:nbe_cbs) (x:a) : t = e.em cb x
let unembed (#a:Type0) (e:embedding a) (cb:nbe_cbs) (trm:t) : option a = e.un cb trm

let type_of (e:embedding 'a) : t = e.typ ()
let set_type (ty:t) (e:embedding 'a) : embedding 'a = { e with typ = (fun () -> ty) }


let mk_emb em un typ et = {em = em; un = un; typ = typ; e_typ=et}
let mk_emb' em un = mk_emb (fun cbs t -> mk_t <| em cbs t) (fun cbs t -> un cbs t.nbe_t)


let embed_as (ea:embedding 'a)
             (ab : 'a -> 'b)
             (ba : 'b -> 'a)
             (ot:option t)
             : embedding 'b
 = mk_emb (fun cbs (x:'b) -> embed ea cbs (ba x))
          (fun cbs t -> BU.map_opt (unembed ea cbs t) ab)
          (fun () -> match ot with | Some t -> t | None -> ea.typ ())
          ea.e_typ

let lid_as_constr (l:lident) (us:list universe) (args:args) : t =
    mkConstruct (lid_as_fv l (Some Data_ctor)) us args

let lid_as_typ (l:lident) (us:list universe) (args:args) : t =
    mkFV (lid_as_fv l None) us args

let as_iarg (a:t) : arg = (a, S.as_aqual_implicit true)
let as_arg (a:t) : arg = (a, None)

//  Non-dependent total arrow
let make_arrow1 t1 (a:arg) : t = mk_t <| Arrow (Inr ([a], Tot t1))

let lazy_embed (et:unit -> emb_typ) (x:'a) (f:unit -> t) =
    if !Options.debug_embedding
    then BU.print1 "Embedding\n\temb_typ=%s\n"
                         (show (et ()));
    if !Options.eager_embedding
    then f()
    else let thunk = Thunk.mk f in
         let li = FStarC.Dyn.mkdyn x, et () in
         mk_t <| Lazy (Inr li, thunk)

let lazy_unembed (et:unit -> emb_typ) (x:t) (f:t -> option 'a) : option 'a =
    match x.nbe_t with
    | Lazy (Inl li, thunk) ->
      f (Thunk.force thunk)

    | Lazy (Inr (b, et'), thunk) ->
      if et () <> et'
      || !Options.eager_embedding
      then let res = f (Thunk.force thunk) in
           let _ = if !Options.debug_embedding
                   then BU.print2 "Unembed cancellation failed\n\t%s <> %s\n"
                                (show (et ()))
                                (show et')
           in
           res
      else let a = FStarC.Dyn.undyn b in
           let _ = if !Options.debug_embedding
                   then BU.print1 "Unembed cancelled for %s\n"
                                     (show (et ()))
           in
           Some a
    | _ ->
      let aopt = f x in
      let _ = if !Options.debug_embedding
              then BU.print1 "Unembedding:\n\temb_typ=%s\n"
                               (show (et ())) in
      aopt

let lazy_unembed_lazy_kind (#a:Type) (k:lazy_kind) (x:t) : option a =
  match x.nbe_t with
  | Lazy (Inl li, _) ->
    if li.lkind = k
    then Some (FStarC.Dyn.undyn li.blob)
    else None
  | _ -> None

// Emdebbing for polymorphic types
let mk_any_emb (ty:t) : embedding t =
    let em = (fun _cb a -> a) in
    let un = (fun _cb t -> Some t) in
    mk_emb em un (fun () -> ty) (fun () -> ET_abstract)

// Emdebbing at abstract types
let e_any : embedding t =
    let em = (fun _cb a -> a) in
    let un = (fun _cb t -> Some t) in
    mk_emb em un (fun () -> lid_as_typ PC.term_lid [] []) (fun () -> ET_abstract)

// Emdebbing at type unit
let e_unit : embedding unit =
    let em _cb a = Constant Unit in
    let un _cb t = Some () in // No runtime typecheck here
    mk_emb' em un (fun () -> lid_as_typ PC.unit_lid [] []) (SE.emb_typ_of unit)

// Embedding at type bool
let e_bool : embedding bool =
    let em _cb a = Constant (Bool a) in
    let un _cb t =
      match t with
      | Constant (Bool a) -> Some a
      | _ -> None
    in
    mk_emb' em un (fun () -> lid_as_typ PC.bool_lid [] []) (SE.emb_typ_of bool)

// Embeddind at type char
let e_char : embedding char =
    let em _cb c = Constant (Char c) in
    let un _cb c =
      match c with
      | Constant (Char a) -> Some a
      | _ -> None
    in
    mk_emb' em un (fun () -> lid_as_typ PC.char_lid [] []) (SE.emb_typ_of char)

// Embeddind at type string
let e_string : embedding string =
  let em _cb s = Constant (String (s, Range.dummyRange)) in
  let un _cb s =
    match s with
    | Constant (String (s, _)) -> Some s
    | _ -> None
  in
  mk_emb' em un (fun () -> lid_as_typ PC.string_lid [] []) (SE.emb_typ_of string)

// Embeddind at type int
let e_int : embedding Z.t =
    let em _cb c = Constant (Int c) in
    let un _cb c =
        match c with
        | Constant (Int a) -> Some a
        | _ -> None
    in
    mk_emb' em un (fun () -> lid_as_typ PC.int_lid [] [])  (SE.emb_typ_of int)

let e_real : embedding Compiler.Real.real =
    let em _cb (Compiler.Real.Real c) = Constant (Real c) in
    let un _cb c =
        match c with
        | Constant (Real a) -> Some (Compiler.Real.Real a)
        | _ -> None
    in
    mk_emb' em un (fun () -> lid_as_typ PC.real_lid [] [])  (SE.emb_typ_of Compiler.Real.real)

let e_fsint = embed_as e_int Z.to_int_fs Z.of_int_fs None

// Embedding at option type
let e_option (ea : embedding 'a) : Prims.Tot _ =
    let etyp () =
        ET_app(PC.option_lid |> Ident.string_of_lid, [ea.e_typ ()])
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
        lazy_unembed etyp trm (fun trm ->
        match trm.nbe_t with
        | Construct (fvar, us, args) when S.fv_eq_lid fvar PC.none_lid ->
          Some None
        | Construct (fvar, us, [(a, _); _]) when S.fv_eq_lid fvar PC.some_lid ->
          BU.bind_opt (unembed ea cb a) (fun a -> Some (Some a))
        | _ -> None)
    in
    mk_emb em un (fun () -> lid_as_typ PC.option_lid [U_zero] [as_arg (type_of ea)]) etyp


// Emdedding tuples
let e_tuple2 (ea:embedding 'a) (eb:embedding 'b) =
    let etyp () =
        ET_app(PC.lid_tuple2 |> Ident.string_of_lid, [ea.e_typ (); eb.e_typ ()])
    in
    let em cb (x:'a & 'b) : t =
        lazy_embed etyp x (fun () ->
        lid_as_constr (PC.lid_Mktuple2)
                      [U_zero; U_zero]
                      [as_arg (embed eb cb (snd x));
                       as_arg (embed ea cb (fst x));
                       as_iarg (type_of eb);
                       as_iarg (type_of ea)])
    in
    let un cb (trm:t) : option ('a & 'b) =
        lazy_unembed etyp trm (fun trm ->
        match trm.nbe_t with
        | Construct (fvar, us, [(b, _); (a, _); _; _]) when S.fv_eq_lid fvar PC.lid_Mktuple2 ->
          let open FStarC.Class.Monad in
          let! a = unembed ea cb a in
          let! b = unembed eb cb b in
          Some (a, b)
        | _ -> None)
    in
    mk_emb em un
           (fun () -> lid_as_typ PC.lid_tuple2 [U_zero;U_zero] [as_arg (type_of eb); as_arg (type_of ea)])
           etyp

let e_tuple3 (ea:embedding 'a) (eb:embedding 'b) (ec:embedding 'c) =
    let etyp () =
        ET_app(PC.lid_tuple3 |> Ident.string_of_lid, [ea.e_typ (); eb.e_typ (); ec.e_typ ()])
    in
    let em cb ((x1, x2, x3):('a & 'b & 'c)) : t =
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
    let un cb (trm:t) : option ('a & 'b & 'c) =
        lazy_unembed etyp trm (fun trm ->
        match trm.nbe_t with
        | Construct (fvar, us, [(c, _); (b, _); (a, _); _; _; _]) when S.fv_eq_lid fvar PC.lid_Mktuple3 ->
          let open FStarC.Class.Monad in
          let! a = unembed ea cb a in
          let! b = unembed eb cb b in
          let! c = unembed ec cb c in
          Some (a, b, c)
        | _ -> None)
    in
    mk_emb em un (fun () -> lid_as_typ PC.lid_tuple3 [U_zero;U_zero;U_zero] [as_arg (type_of ec); as_arg (type_of eb); as_arg (type_of ea)]) etyp

let e_tuple4 (ea:embedding 'a) (eb:embedding 'b) (ec:embedding 'c) (ed:embedding 'd) =
    let etyp () =
        ET_app(PC.lid_tuple4 |> Ident.string_of_lid, [ea.e_typ (); eb.e_typ (); ec.e_typ (); ed.e_typ ()])
    in
    let em cb (x1, x2, x3, x4) : t =
        lazy_embed etyp (x1, x2, x3, x4) (fun () ->
        lid_as_constr (PC.lid_Mktuple4)
                      [U_zero; U_zero; U_zero; U_zero]
                      [as_arg (embed ed cb x4);
                       as_arg (embed ec cb x3);
                       as_arg (embed eb cb x2);
                       as_arg (embed ea cb x1);
                       as_iarg (type_of ed);
                       as_iarg (type_of ec);
                       as_iarg (type_of eb);
                       as_iarg (type_of ea)])
    in
    let un cb (trm:t) : option ('a & 'b & 'c & 'd) =
        lazy_unembed etyp trm (fun trm ->
        match trm.nbe_t with
        | Construct (fvar, us, [(d, _); (c, _); (b, _); (a, _); _; _; _; _]) when S.fv_eq_lid fvar PC.lid_Mktuple4 ->
          let open FStarC.Class.Monad in
          let! a = unembed ea cb a in
          let! b = unembed eb cb b in
          let! c = unembed ec cb c in
          let! d = unembed ed cb d in
          Some (a, b, c, d)
        | _ -> None)
    in
    mk_emb em un (fun () -> lid_as_typ PC.lid_tuple4 [U_zero;U_zero;U_zero;U_zero] [as_arg (type_of ed); as_arg (type_of ec); as_arg (type_of eb); as_arg (type_of ea)]) etyp

let e_tuple5 (ea:embedding 'a) (eb:embedding 'b) (ec:embedding 'c) (ed:embedding 'd) (ee:embedding 'e) =
    let etyp () =
        ET_app(PC.lid_tuple5 |> Ident.string_of_lid, [ea.e_typ (); eb.e_typ (); ec.e_typ (); ed.e_typ (); ee.e_typ ()])
    in
    let em cb (x1, x2, x3, x4, x5) : t =
        lazy_embed etyp (x1, x2, x3, x4, x5) (fun () ->
        lid_as_constr (PC.lid_Mktuple5)
                      [U_zero; U_zero; U_zero; U_zero;U_zero]
                      [as_arg (embed ee cb x5);
                       as_arg (embed ed cb x4);
                       as_arg (embed ec cb x3);
                       as_arg (embed eb cb x2);
                       as_arg (embed ea cb x1);
                       as_iarg (type_of ee);
                       as_iarg (type_of ed);
                       as_iarg (type_of ec);
                       as_iarg (type_of eb);
                       as_iarg (type_of ea)])
    in
    let un cb (trm:t) : option ('a & 'b & 'c & 'd & 'e) =
        lazy_unembed etyp trm (fun trm ->
        match trm.nbe_t with
        | Construct (fvar, us, [(e, _); (d, _); (c, _); (b, _); (a, _); _; _; _; _; _]) when S.fv_eq_lid fvar PC.lid_Mktuple5 ->
          let open FStarC.Class.Monad in
          let! a = unembed ea cb a in
          let! b = unembed eb cb b in
          let! c = unembed ec cb c in
          let! d = unembed ed cb d in
          let! e = unembed ee cb e in
          Some (a, b, c, d, e)
        | _ -> None)
    in
    mk_emb em un
      (fun () -> lid_as_typ PC.lid_tuple5 [U_zero;U_zero;U_zero;U_zero;U_zero] [as_arg (type_of ee); as_arg (type_of ed); as_arg (type_of ec); as_arg (type_of eb); as_arg (type_of ea)])
      etyp

let e_either (ea:embedding 'a) (eb:embedding 'b) =
    let etyp () =
        ET_app(PC.either_lid |> Ident.string_of_lid, [ea.e_typ (); eb.e_typ ()])
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
        lazy_unembed etyp trm (fun trm ->
        match trm.nbe_t with
        | Construct (fvar, us, [(a, _); _; _]) when S.fv_eq_lid fvar PC.inl_lid ->
          BU.bind_opt (unembed ea cb a) (fun a ->
          Some (Inl a))
        | Construct (fvar, us, [(b, _); _; _]) when S.fv_eq_lid fvar PC.inr_lid ->
          BU.bind_opt (unembed eb cb b) (fun b ->
          Some (Inr b))
        | _ -> None)
    in
    mk_emb em un (fun () -> lid_as_typ PC.either_lid [U_zero;U_zero] [as_arg (type_of eb); as_arg (type_of ea)]) etyp

// Embedding range (unsealed)
let e___range : embedding Range.range =
    let em cb r = Constant (Range r) in
    let un cb t =
    match t with
    | Constant (Range r) -> Some r
    | _ ->
        None
    in
    mk_emb' em un (fun () -> lid_as_typ PC.__range_lid [] []) (SE.emb_typ_of Range.range)

// Embedding a sealed term. This just calls the embedding for a but also
// adds a `seal` marker to the result. The unembedding removes it.
let e_sealed (ea : embedding 'a) : Prims.Tot (embedding (Sealed.sealed 'a)) =
    let etyp () =
        ET_app(PC.sealed_lid |> Ident.string_of_lid, [ea.e_typ ()])
    in
    let em cb (x: Sealed.sealed 'a) : t =
        lazy_embed etyp x (fun () ->
          lid_as_constr PC.seal_lid [U_zero] [as_arg (embed ea cb (Sealed.unseal x));
                                          as_iarg (type_of ea)])
    in
    let un cb (trm:t) : option (Sealed.sealed 'a) =
        lazy_unembed etyp trm (fun trm ->
        match trm.nbe_t with
        | Construct (fvar, us, [(a, _); _]) when S.fv_eq_lid fvar PC.seal_lid ->
          Class.Monad.fmap Sealed.seal <| unembed ea cb a
        | _ -> None)
    in
    mk_emb em un (fun () -> lid_as_typ PC.sealed_lid [U_zero] [as_arg (type_of ea)]) etyp

let e_range : embedding Range.range =
  embed_as (e_sealed e___range) Sealed.unseal Sealed.seal None

let e_issue : embedding FStarC.Errors.issue =
    let t_issue = SE.type_of SE.e_issue in
    let li blob rng = { blob=Dyn.mkdyn blob; lkind = Lazy_issue; ltyp = t_issue; rng } in
    let em cb iss = Lazy (Inl (li iss Range.dummyRange), (Thunk.mk (fun _ -> failwith "Cannot unembed issue"))) in
    let un cb t =
    match t with
    | Lazy (Inl { lkind=Lazy_issue; blob }, _) -> Some (Dyn.undyn blob)
    | _ -> None
    in
    mk_emb' em un (fun () -> lid_as_typ PC.issue_lid [] []) (SE.emb_typ_of issue)

let e_document : embedding FStarC.Pprint.document =
    let t_document = SE.type_of SE.e_document in
    let li blob rng = { blob=Dyn.mkdyn blob; lkind = Lazy_doc; ltyp = t_document; rng } in
    let em cb doc = Lazy (Inl (li doc Range.dummyRange), (Thunk.mk (fun _ -> failwith "Cannot unembed document"))) in
    let un cb t =
    match t with
    | Lazy (Inl { lkind=Lazy_doc; blob }, _) -> Some (Dyn.undyn blob)
    | _ -> None
    in
    mk_emb' em un (fun () -> lid_as_typ PC.document_lid [] []) (SE.emb_typ_of Pprint.document)

// vconfig, NYI
let e_vconfig : embedding vconfig =
    let em cb r = failwith "e_vconfig NBE" in
    let un cb t = failwith "e_vconfig NBE" in
    mk_emb' em un (fun () -> lid_as_typ PC.vconfig_lid [] []) (SE.emb_typ_of vconfig)

// Emdedding lists
let e_list (ea:embedding 'a) =
    let etyp () =
        ET_app(PC.list_lid |> Ident.string_of_lid, [ea.e_typ ()])
    in
    let em cb (l:list 'a) : t =
        lazy_embed etyp l (fun () ->
        let typ = as_iarg (type_of ea) in
        let nil = lid_as_constr PC.nil_lid [U_zero] [typ] in
        let cons hd tl = lid_as_constr PC.cons_lid [U_zero] [as_arg tl; as_arg (embed ea cb hd); typ] in
        List.fold_right cons l nil)
    in
    let rec un cb (trm:t) : option (list 'a) =
        lazy_unembed etyp trm (fun trm ->
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
    mk_emb em un (fun () -> lid_as_typ PC.list_lid [U_zero] [as_arg (type_of ea)]) etyp
  
let e_string_list = e_list e_string

let e_arrow (ea:embedding 'a) (eb:embedding 'b) : Prims.Tot (embedding ('a -> 'b)) =
    let etyp () = ET_fun(ea.e_typ (), eb.e_typ ()) in
    let em cb (f : 'a -> 'b) : t =
        lazy_embed etyp f (fun () ->
        mk_t <| Lam {
          interp = (fun tas -> match unembed ea cb (tas |> List.hd |> fst) with
                             | Some a -> embed eb cb (f a)
                             | None -> failwith "cannot unembed function argument");
          shape = Lam_args [as_arg (type_of eb)];
          arity = 1;
        })
    in
    let un cb (lam : t) : option ('a -> 'b) =
        let k (lam:t) : option ('a -> 'b) =
            Some (fun (x:'a) -> match unembed eb cb (cb.iapp lam [as_arg (embed ea cb x)]) with
                                | Some y -> y
                                | None -> failwith "cannot unembed function result")
        in
        lazy_unembed etyp lam k
    in
    mk_emb em un (fun () -> make_arrow1 (type_of ea) (as_iarg (type_of eb))) etyp

let e_abstract_nbe_term =
  embed_as e_any (fun x -> AbstractNBE x) (fun x -> match x with AbstractNBE x -> x) None

let e_unsupported #a : embedding a =
    let em = (fun _cb a -> failwith "Unsupported NBE embedding") in
    let un = (fun _cb t -> failwith "Unsupported NBE embedding") in
    mk_emb em un (fun () -> lid_as_typ PC.term_lid [] []) (fun () -> ET_abstract)

let e_norm_step =
    let em cb (n:Pervasives.norm_step) : t =
        match n with
        | Pervasives.Simpl   -> mkFV (lid_as_fv PC.steps_simpl     None) [] []
        | Pervasives.Weak    -> mkFV (lid_as_fv PC.steps_weak      None) [] []
        | Pervasives.HNF     -> mkFV (lid_as_fv PC.steps_hnf       None) [] []
        | Pervasives.Primops -> mkFV (lid_as_fv PC.steps_primops   None) [] []
        | Pervasives.Delta   -> mkFV (lid_as_fv PC.steps_delta     None) [] []
        | Pervasives.Zeta    -> mkFV (lid_as_fv PC.steps_zeta      None) [] []
        | Pervasives.Iota    -> mkFV (lid_as_fv PC.steps_iota      None) [] []
        | Pervasives.Reify   -> mkFV (lid_as_fv PC.steps_reify     None) [] []
        | Pervasives.NBE     -> mkFV (lid_as_fv PC.steps_nbe       None) [] []
        | Pervasives.UnfoldOnly l ->
                     mkFV (lid_as_fv PC.steps_unfoldonly None)
                          [] [as_arg (embed (e_list e_string) cb l)]
        | Pervasives.UnfoldFully l ->
                     mkFV (lid_as_fv PC.steps_unfoldfully None)
                          [] [as_arg (embed (e_list e_string) cb l)]
        | Pervasives.UnfoldAttr l ->
                     mkFV (lid_as_fv PC.steps_unfoldattr None)
                          [] [as_arg (embed (e_list e_string) cb l)]
        | Pervasives.UnfoldQual l ->
                     mkFV (lid_as_fv PC.steps_unfoldqual None)
                          [] [as_arg (embed (e_list e_string) cb l)]
        | Pervasives.UnfoldNamespace l ->
                     mkFV (lid_as_fv PC.steps_unfoldnamespace None)
                          [] [as_arg (embed (e_list e_string) cb l)]
        | Pervasives.ZetaFull -> mkFV (lid_as_fv PC.steps_zeta_full None) [] []
        | Pervasives.Unascribe -> mkFV (lid_as_fv PC.steps_unascribe None) [] []
    in
    let un cb (t0:t) : option Pervasives.norm_step =
        match t0.nbe_t with
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_simpl ->
            Some Pervasives.Simpl
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_weak ->
            Some Pervasives.Weak
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_hnf ->
            Some Pervasives.HNF
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_primops ->
            Some Pervasives.Primops
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_delta ->
            Some Pervasives.Delta
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_zeta ->
            Some Pervasives.Zeta
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_iota ->
            Some Pervasives.Iota
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_nbe ->
            Some Pervasives.NBE
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_reify ->
            Some Pervasives.Reify
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_zeta_full ->
            Some Pervasives.ZetaFull
        | FV (fv, _, []) when S.fv_eq_lid fv PC.steps_unascribe ->
            Some Pervasives.Unascribe
        | FV (fv, _, [(l, _)]) when S.fv_eq_lid fv PC.steps_unfoldonly ->
            BU.bind_opt (unembed (e_list e_string) cb l) (fun ss ->
            Some <| Pervasives.UnfoldOnly ss)
        | FV (fv, _, [(l, _)]) when S.fv_eq_lid fv PC.steps_unfoldfully ->
            BU.bind_opt (unembed (e_list e_string) cb l) (fun ss ->
            Some <| Pervasives.UnfoldFully ss)
        | FV (fv, _, [(l, _)]) when S.fv_eq_lid fv PC.steps_unfoldattr ->
            BU.bind_opt (unembed (e_list e_string) cb l) (fun ss ->
            Some <| Pervasives.UnfoldAttr ss)
        | FV (fv, _, [(l, _)]) when S.fv_eq_lid fv PC.steps_unfoldqual ->
            BU.bind_opt (unembed (e_list e_string) cb l) (fun ss ->
            Some <| Pervasives.UnfoldQual ss)
        | FV (fv, _, [(l, _)]) when S.fv_eq_lid fv PC.steps_unfoldnamespace ->
            BU.bind_opt (unembed (e_list e_string) cb l) (fun ss ->
            Some <| Pervasives.UnfoldNamespace ss)
        | _ ->
            Errors.log_issue0 Errors.Warning_NotEmbedded
              (BU.format1 "Not an embedded norm_step: %s" (t_to_string t0));
            None
    in
    mk_emb em un (fun () -> mkFV (lid_as_fv PC.norm_step_lid None) [] [])
                 (SE.emb_typ_of norm_step)

(* Interface for building primitive steps *)

let bogus_cbs = {
    iapp = (fun h _args -> h);
    translate = (fun _ -> failwith "bogus_cbs translate");
}

let arg_as_int    (a:arg) = fst a |> unembed e_int bogus_cbs

let arg_as_bool   (a:arg) = fst a |> unembed e_bool bogus_cbs

let arg_as_list   (e:embedding 'a) (a:arg) = fst a |> unembed (e_list e) bogus_cbs

(* XXX a lot of code duplication. Same code as in cfg.fs *)
let lift_unary (f : 'a -> 'b) (aopts : list (option 'a)) : option 'b =
        match aopts with
        | [Some a] -> Some (f a)
        | _ -> None


let lift_binary (f : 'a -> 'a -> 'b) (aopts : list (option 'a)) : option 'b =
        match aopts with
        | [Some a0; Some a1] -> Some (f a0 a1)
        | _ -> None

let mixed_binary_op (as_a : arg -> option 'a) (as_b : arg -> option 'b)
       (embed_c : 'c -> t) (f : universes -> 'a -> 'b -> option 'c)
       (us:universes) (args : args) : option t =
             match args with
             | [a;b] ->
                begin
                match as_a a, as_b b with
                | Some a, Some b ->
                  (match f us a b with
                   | Some c -> Some (embed_c c)
                   | _ -> None)
                | _ -> None
                end
             | _ -> None

let mixed_ternary_op (as_a : arg -> option 'a)
                     (as_b : arg -> option 'b)
                     (as_c : arg -> option 'c)                     
                     (embed_d : 'd -> t) 
                     (f : universes -> 'a -> 'b -> 'c -> option 'd)
                     (us: universes)
                     (args : args) : option t =
             match args with
             | [a;b;c] ->
                begin
                match as_a a, as_b b, as_c c with
                | Some a, Some b, Some c ->
                  (match f us a b c with
                   | Some d -> Some (embed_d d)
                   | _ -> None)
                | _ -> None
                end
             | _ -> None

let dummy_interp (lid : Ident.lid) (args : args) : option t =
    failwith ("No interpretation for " ^ (Ident.string_of_lid lid))

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
                         (f:'a -> 'b) (_fv_lid:Ident.lid) cb
   : universes -> args -> option t =
    let f_wrapped _us args =
        let x, _ = List.hd args in //arity mismatches are handled by code that dispatches here
        BU.map_opt
                (unembed ea cb x) (fun x ->
                 embed eb cb (f x))
    in
    f_wrapped

let arrow_as_prim_step_2 (ea:embedding 'a) (eb:embedding 'b) (ec:embedding 'c)
                         (f:'a -> 'b -> 'c) (_fv_lid:Ident.lid) cb
   : universes -> args -> option t =
    let f_wrapped _us args =
        let x, _ = List.hd args in //arity mismatches are handled by code that dispatches here
        let y, _ = List.hd (List.tl args) in
        BU.bind_opt (unembed ea cb x) (fun x ->
        BU.bind_opt (unembed eb cb y) (fun y ->
        Some (embed ec cb (f x y))))
    in
    f_wrapped


let arrow_as_prim_step_3 (ea:embedding 'a) (eb:embedding 'b)
                         (ec:embedding 'c) (ed:embedding 'd)
                         (f:'a -> 'b -> 'c -> 'd) (_fv_lid:Ident.lid) cb
   : universes -> args -> option t =
    let f_wrapped _us args =
        let x, _ = List.hd args in //arity mismatches are handled by code that dispatches here
        let y, _ = List.hd (List.tl args) in
        let z, _ = List.hd (List.tl (List.tl args)) in
        BU.bind_opt (unembed ea cb x) (fun x ->
        BU.bind_opt (unembed eb cb y) (fun y ->
        BU.bind_opt (unembed ec cb z) (fun z ->
        Some (embed ed cb (f x y z)))))
    in
    f_wrapped

(* TODO: move to, Syntax.Embeddings or somewhere better even *)
let e_order =
  let ord_Lt_lid = Ident.lid_of_path (["FStar"; "Order"; "Lt"]) Range.dummyRange in
  let ord_Eq_lid = Ident.lid_of_path (["FStar"; "Order"; "Eq"]) Range.dummyRange in
  let ord_Gt_lid = Ident.lid_of_path (["FStar"; "Order"; "Gt"]) Range.dummyRange in
  let ord_Lt = tdataconstr ord_Lt_lid in
  let ord_Eq = tdataconstr ord_Eq_lid in
  let ord_Gt = tdataconstr ord_Gt_lid in
  let ord_Lt_fv = lid_as_fv ord_Lt_lid (Some Data_ctor) in
  let ord_Eq_fv = lid_as_fv ord_Eq_lid (Some Data_ctor) in
  let ord_Gt_fv = lid_as_fv ord_Gt_lid (Some Data_ctor) in
  let open FStarC.Compiler.Order in
  let embed_order cb (o:order) : t =
      match o with
      | Lt -> mkConstruct ord_Lt_fv [] []
      | Eq -> mkConstruct ord_Eq_fv [] []
      | Gt -> mkConstruct ord_Gt_fv [] []
  in
  let unembed_order cb (t:t) : option order =
      match t.nbe_t with
      | Construct (fv, _, []) when S.fv_eq_lid fv ord_Lt_lid -> Some Lt
      | Construct (fv, _, []) when S.fv_eq_lid fv ord_Eq_lid -> Some Eq
      | Construct (fv, _, []) when S.fv_eq_lid fv ord_Gt_lid -> Some Gt
      | _ -> None
  in
  let fv_as_emb_typ fv = S.ET_app (FStarC.Ident.string_of_lid fv.fv_name.v, []) in
  let fv = lid_as_fv PC.order_lid None in
  mk_emb embed_order unembed_order (fun () -> mkFV fv [] []) (fun () -> fv_as_emb_typ fv)
