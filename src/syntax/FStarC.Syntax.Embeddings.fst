(*
   Copyright 2008-2014 Microsoft Research

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

module FStarC.Syntax.Embeddings

open FStar open FStarC
open FStarC.Compiler
open FStar.Pervasives
open FStarC.Compiler.Effect
open FStarC.Syntax.Syntax
open FStarC.Compiler.Range
open FStarC.VConfig

open FStarC.Class.Show

module BU    = FStarC.Compiler.Util
module C     = FStarC.Const
module Err   = FStarC.Errors
module Ident = FStarC.Ident
module PC    = FStarC.Parser.Const
module Print = FStarC.Syntax.Print
module S     = FStarC.Syntax.Syntax
module SS    = FStarC.Syntax.Subst
module U     = FStarC.Syntax.Util
module UF    = FStarC.Syntax.Unionfind
module Z     = FStarC.BigInt

open FStarC.Syntax.Embeddings.Base
module AE = FStarC.Syntax.Embeddings.AppEmb

friend FStar.Pervasives (* To expose norm_step *)

(*********************************************************************

             A NOTE ON FUNCTIONS AND SHADOW TERMS

Shadow terms exist to acomodate strong reduction of plugins.

Suppose we have this function, marked as a plugin to accelerate it
during typechecking:

    [@@plugin]
    let sort (l : list int) : list int = ...

(Plugins are usually tactics, but do not have to be. This discussion
is actually not so relevant for tactics as they do not run in open
contexts.)

Compilation will generate a version that works on _real_ concrete
lists of integers. To call it on a term, as we have to do during
typechecking, we need to wrap it with embeddings:

    sort_term t = embed_intlist (sort (unembed_intlist t))

This turns the term `t` into an actual `list int`, calls the native
sort function, and then reconstructs a term for the resulting list.

After loading the compiled version of that file, `sort_term` is now
loaded as a primitive step in the normalizer (under the name `sort`, of
course), and will be called everytime we find this symbol applied to an
argument. While its argument must have already been reduced (CBV), there
is no guarantee that it is an actual _value_ as we may be in an open
context, e.g. we may be typechecking this formula:

    forall l. sum (sort l) == sum l

or it can be applied to some abstract lid even in a closed
context, or to a Tm_let that we are not currently reducing (e.g. DIV),
etc. So, we may fail (and often do) to unembed the argument term
to obtain a concrete list, hence sort_term is closer to:

    sort_term t = match unembed_intlist t with
                  | None -> None
                  | Some l -> embed_intlist (sort l)

But, instead of stopping reduction with the None, we can instead
use the definition of sort itself, and call the normalizer with
the unfolded definition applied to the symbolic argument. Shadow
terms are term representations of whatever the embedded thing is,
which can be defaulted to when the embedding does not work.

(TODO: what does this do for recursive functions? sounds
  like it would not unfold? Actually, it seems broken:

    [@@plugin]
    let rec mylen (l : list int) : int =
      match l with
      | [] -> 0
      | x::xs -> 1 + mylen xs

    let test (a b c : int) =
      assert (mylen [a;b;c] == mylen [c;b;a]) by begin
        dump "1";
        compute ();
        dump "2";
        trefl ();
        ()
      end

this file works when mylen is not loaded as a plugin, but fails
otherwise since reduction is blocked.)


*********************************************************************)

let id_norm_cb : norm_cb = function
    | Inr x -> x
    | Inl l -> S.fv_to_tm (S.lid_as_fv l None)
exception Embedding_failure
exception Unembedding_failure

let map_shadow (s:shadow_term) (f:term -> term) : shadow_term =
    BU.map_opt s (Thunk.map f)
let force_shadow (s:shadow_term) = BU.map_opt s Thunk.force

type printer 'a = 'a -> string

let unknown_printer (typ:typ) _ =
    BU.format1 "unknown %s" (show typ)

let term_as_fv t =
    match (SS.compress t).n with
    | Tm_fvar fv -> fv
    | _ -> failwith (BU.format1 "Embeddings not defined for type %s" (show t))

let lazy_embed (pa:printer 'a) (et:unit -> emb_typ) rng (ta: unit -> term) (x:'a) (f:unit -> term) =
    if !Options.debug_embedding
    then BU.print3 "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n"
                         (show (ta ()))
                         (show (et ()))
                         (pa x);
    if !Options.eager_embedding
    then f()
    else let thunk = Thunk.mk f in
         U.mk_lazy x S.tun (Lazy_embedding (et (), thunk)) (Some rng)

let lazy_unembed (pa:printer 'a) (et: unit -> emb_typ) (x:term) (ta: unit -> term) (f:term -> option 'a) : option 'a =
    let et = et () in
    let x = unmeta_div_results x in
    match x.n with
    | Tm_lazy {blob=b; lkind=Lazy_embedding (et', t)}  ->
      if et <> et'
      || !Options.eager_embedding
      then let res = f (Thunk.force t) in
           let _ = if !Options.debug_embedding
                   then BU.print3 "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                                (show et)
                                (show et')
                                (match res with None -> "None" | Some x -> "Some " ^ (pa x))
           in
           res
      else let a = Dyn.undyn b in
           let _ = if !Options.debug_embedding
                   then BU.print2 "Unembed cancelled for %s\n\tvalue is %s\n"
                                (show et)
                                  (pa a)
           in
           Some a
    | _ ->
      let aopt = f x in
      let _ = if !Options.debug_embedding
              then BU.print3 "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                               (show et)
                               (show x)
                               (match aopt with None -> "None" | Some a -> "Some " ^ pa a) in
      aopt


let mk_any_emb typ =
    let em = fun t _r _shadow _norm ->
      if !Options.debug_embedding then
        BU.print1 "Embedding abstract: %s\n" (unknown_printer typ t);
      t
    in
    let un = fun t _n ->
      if !Options.debug_embedding then
        BU.print1 "Unembedding abstract: %s\n" (unknown_printer typ t);
      Some t
    in
    mk_emb_full
        em
        un
        (fun () -> typ)
        (unknown_printer typ)
        (fun () -> ET_abstract)

let e_any =
    let em = fun t r _shadow _norm -> { t with pos = r} in
    let un = fun t _n -> Some t in
    mk_emb_full
        em
        un
        (fun () -> S.t_term) // not correct
        show
        (fun () -> ET_app (PC.term_lid |> Ident.string_of_lid, []))

let e_unit =
    let em (u:unit) rng _shadow _norm : term = { U.exp_unit with pos = rng } in
    let un (t0:term) _norm : option unit =
        let t = U.unascribe t0 in
        match t.n with
        | S.Tm_constant C.Const_unit -> Some ()
        | _ -> None
    in
    mk_emb_full
        em
        un
        (fun () -> S.t_unit)
        (fun _ -> "()")
        (fun () -> ET_app(PC.unit_lid |> Ident.string_of_lid, []))

let e_bool =
    let em (b:bool) rng _shadow _norm : term =
        let t = if b then U.exp_true_bool else U.exp_false_bool in
        { t with pos = rng }
    in
    let un (t:term) _norm : option bool =
        match (SS.compress t).n with
        | Tm_constant(FStarC.Const.Const_bool b) -> Some b
        | _ -> None
    in
    mk_emb_full
        em
        un
        (fun () -> S.t_bool)
        BU.string_of_bool
        (fun () -> ET_app(PC.bool_lid |> Ident.string_of_lid, []))

let e_char =
    let em (c:char) (rng:range) _shadow _norm : term =
        let t = U.exp_char c in
        { t with pos = rng }
    in
    let un (t:term) _norm : option char =
        match (SS.compress t).n with
        | Tm_constant(FStarC.Const.Const_char c) -> Some c
        | _ -> None
    in
    mk_emb_full
        em
        un
        (fun () -> S.t_char)
        BU.string_of_char
        (fun () -> ET_app(PC.char_lid |> Ident.string_of_lid, []))

let e_int =
    let ty = S.t_int in
    let emb_t_int = ET_app(PC.int_lid |> Ident.string_of_lid, []) in
    let em (i:Z.t) (rng:range) _shadow _norm : term =
        lazy_embed
            BigInt.string_of_big_int
            (fun () -> emb_t_int)
            rng
            (fun () -> ty)
            i
            (fun () -> U.exp_int (Z.string_of_big_int i))
    in
    let un (t:term) _norm : option Z.t =
        lazy_unembed
            BigInt.string_of_big_int
            (fun () -> emb_t_int)
            t
            (fun () -> ty)
            (fun t ->
                match t.n with
                | Tm_constant(FStarC.Const.Const_int (s, _)) -> Some (Z.big_int_of_string s)
                | _ -> None)
    in
    mk_emb_full
        em
        un
        (fun () -> ty)
        BigInt.string_of_big_int
        (fun () -> emb_t_int)

let e_fsint = embed_as e_int Z.to_int_fs Z.of_int_fs None

let e_string =
    let emb_t_string = ET_app(PC.string_lid |> Ident.string_of_lid, []) in
    let em (s:string) (rng:range) _shadow _norm : term =
        S.mk (Tm_constant(FStarC.Const.Const_string(s, rng)))
             rng
    in
    let un (t:term) _norm : option string =
        match (SS.compress t).n with
        | Tm_constant(FStarC.Const.Const_string(s, _)) -> Some s
        | _ -> None
    in
    mk_emb_full
        em
        un
        (fun () -> S.t_string)
        (fun x -> "\"" ^ x ^ "\"")
        (fun () -> emb_t_string)

let e_real =
    let open FStarC.Compiler.Real in
    let ty = S.t_real in
    let emb_t_real = ET_app(PC.real_lid |> Ident.string_of_lid, []) in
    let em (r:real) (rng:range) _shadow _norm : term =
      let Real s = r in
      mk (Tm_constant (Const.Const_real s)) rng
    in
    let un (t:term) _norm : option real =
      match (unmeta_div_results t).n with
      | Tm_constant (Const.Const_real s) -> Some (Real s)
      | _ -> None
    in
    mk_emb_full
        em
        un
        (fun () -> ty)
        (fun _ -> "<real>")
        (fun () -> emb_t_real)

let e_option (ea : embedding 'a) : Tot _ =
    let typ () = S.t_option_of (type_of ea) in
    let emb_t_option_a () =
        ET_app(PC.option_lid |> Ident.string_of_lid, [emb_typ_of 'a ()])
    in
    let printer x = FStarC.Common.string_of_option (printer_of ea) x in
    let em (o:option 'a) (rng:range) shadow norm : term =
        lazy_embed
            printer
            emb_t_option_a
            rng
            (fun () -> S.t_option_of (type_of ea))
            o
            (fun () ->
                match o with
                | None ->
                  S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.none_lid) [U_zero])
                              [S.iarg (type_of ea)]
                              rng
                | Some a ->
                  let shadow_a = map_shadow shadow (fun t ->
                    let v = Ident.mk_ident ("v", rng) in
                    let some_v = U.mk_field_projector_name_from_ident PC.some_lid v in
                    let some_v_tm = S.fv_to_tm (lid_as_fv some_v None) in
                    S.mk_Tm_app (S.mk_Tm_uinst some_v_tm [U_zero])
                                [S.iarg (type_of ea); S.as_arg t]
                                rng)
                  in
                  S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.some_lid) [U_zero])
                              [S.iarg (type_of ea); S.as_arg (embed a rng shadow_a norm)]
                              rng)
    in
    let un (t:term)  norm : option (option 'a) =
        lazy_unembed
            printer
            emb_t_option_a
            t
            (fun () -> S.t_option_of (type_of ea))
            (fun t ->
                let hd, args = U.head_and_args_full t in
                match (U.un_uinst hd).n, args with
                | Tm_fvar fv, _ when S.fv_eq_lid fv PC.none_lid -> Some None
                | Tm_fvar fv, [_; (a, _)] when S.fv_eq_lid fv PC.some_lid ->
                     BU.bind_opt (try_unembed a norm) (fun a -> Some (Some a))
                | _ -> None)
    in
    mk_emb_full
        em
        un
        typ
        printer
        emb_t_option_a

let e_tuple2 (ea:embedding 'a) (eb:embedding 'b) =
    let typ () = S.t_tuple2_of (type_of ea) (type_of eb) in
    let emb_t_pair () =
        ET_app(PC.lid_tuple2 |> Ident.string_of_lid, [emb_typ_of 'a (); emb_typ_of 'b ()])
    in
    let printer (x, y) =
        BU.format2 "(%s, %s)" (printer_of ea x) (printer_of eb y)
    in
    let em (x:('a & 'b)) (rng:range) shadow norm : term =
        lazy_embed
            printer
            emb_t_pair
            rng
            typ
            x
            (fun () ->
                let proj i ab =
                    let proj_1 = U.mk_field_projector_name (PC.mk_tuple_data_lid 2 rng) (S.null_bv S.tun) i in
                    let proj_1_tm = S.fv_to_tm (lid_as_fv proj_1 None) in
                    S.mk_Tm_app (S.mk_Tm_uinst proj_1_tm [U_zero])
                                [S.iarg (type_of ea);
                                 S.iarg (type_of eb);
                                 S.as_arg ab] // ab == shadow
                                rng
                in
                let shadow_a = map_shadow shadow (proj 1) in
                let shadow_b = map_shadow shadow (proj 2) in
                S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.lid_Mktuple2) [U_zero;U_zero])
                            [S.iarg (type_of ea);
                             S.iarg (type_of eb);
                             S.as_arg (embed (fst x) rng shadow_a norm);
                             S.as_arg (embed (snd x) rng shadow_b norm)]
                            rng)
    in
    let un (t:term)  norm : option ('a & 'b) =
        lazy_unembed
            printer
            emb_t_pair
            t
            typ
            (fun t ->
                let hd, args = U.head_and_args_full t in
                match (U.un_uinst hd).n, args with
                | Tm_fvar fv, [_; _; (a, _); (b, _)] when S.fv_eq_lid fv PC.lid_Mktuple2 ->
                    let open FStarC.Class.Monad in
                    let! a = try_unembed a norm in
                    let! b = try_unembed b norm in
                    Some (a, b)
                | _ -> None)
    in
    mk_emb_full
        em
        un
        typ
        printer
        emb_t_pair

let e_tuple3 (ea:embedding 'a) (eb:embedding 'b) (ec:embedding 'c) =
    let typ () = S.t_tuple3_of (type_of ea) (type_of eb) (type_of ec) in
    let emb_t_pair () =
        ET_app(PC.lid_tuple3 |> Ident.string_of_lid, [emb_typ_of 'a (); emb_typ_of 'b (); emb_typ_of 'c ()])
    in
    let printer (x, y, z) =
        BU.format3 "(%s, %s, %s)" (printer_of ea x) (printer_of eb y) (printer_of ec z)
    in
    let em ((x1, x2, x3):('a & 'b & 'c)) (rng:range) shadow norm : term =
        lazy_embed
            printer
            emb_t_pair
            rng
            typ
            (x1, x2, x3)
            (fun () ->
                let proj i abc =
                    let proj_i = U.mk_field_projector_name (PC.mk_tuple_data_lid 3 rng) (S.null_bv S.tun) i in
                    let proj_i_tm = S.fv_to_tm (lid_as_fv proj_i None) in
                    S.mk_Tm_app (S.mk_Tm_uinst proj_i_tm [U_zero])
                                [S.iarg (type_of ea);
                                 S.iarg (type_of eb);
                                 S.iarg (type_of ec);
                                 S.as_arg abc] // abc == shadow
                                rng
                in
                let shadow_a = map_shadow shadow (proj 1) in
                let shadow_b = map_shadow shadow (proj 2) in
                let shadow_c = map_shadow shadow (proj 3) in
                S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.lid_Mktuple3) [U_zero;U_zero;U_zero])
                            [S.iarg (type_of ea);
                             S.iarg (type_of eb);
                             S.iarg (type_of ec);
                             S.as_arg (embed x1 rng shadow_a norm);
                             S.as_arg (embed x2 rng shadow_b norm);
                             S.as_arg (embed x3 rng shadow_c norm)]
                            rng)
    in
    let un (t:term) norm : option ('a & 'b & 'c) =
        lazy_unembed
            printer
            emb_t_pair
            t
            typ
            (fun t ->
                let hd, args = U.head_and_args_full t in
                match (U.un_uinst hd).n, args with
                | Tm_fvar fv, [_; _; _; (a, _); (b, _); (c, _)] when S.fv_eq_lid fv PC.lid_Mktuple3 ->
                    let open FStarC.Class.Monad in
                    let! a = try_unembed a norm in
                    let! b = try_unembed b norm in
                    let! c = try_unembed c norm in
                    Some (a, b, c)
                | _ -> None)
    in
    mk_emb_full
        em
        un
        typ
        printer
        emb_t_pair

let e_tuple4 (ea:embedding 'a) (eb:embedding 'b) (ec:embedding 'c) (ed:embedding 'd) =
    let typ () = S.t_tuple4_of (type_of ea) (type_of eb) (type_of ec) (type_of ed) in
    let emb_t_pair () =
        ET_app(PC.lid_tuple4 |> Ident.string_of_lid, [emb_typ_of 'a (); emb_typ_of 'b (); emb_typ_of 'c (); emb_typ_of 'd ()])
    in
    let printer (x, y, z, w) =
        BU.format4 "(%s, %s, %s, %s)" (printer_of ea x) (printer_of eb y) (printer_of ec z) (printer_of ed w)
    in
    let em (x1, x2, x3, x4) (rng:range) shadow norm : term =
        lazy_embed
            printer
            emb_t_pair
            rng
            typ
            (x1, x2, x3, x4)
            (fun () ->
                let proj i abcd =
                    let proj_i = U.mk_field_projector_name (PC.mk_tuple_data_lid 4 rng) (S.null_bv S.tun) i in
                    let proj_i_tm = S.fv_to_tm (lid_as_fv proj_i None) in
                    S.mk_Tm_app (S.mk_Tm_uinst proj_i_tm [U_zero])
                                [S.iarg (type_of ea);
                                 S.iarg (type_of eb);
                                 S.iarg (type_of ec);
                                 S.iarg (type_of ed);
                                 S.as_arg abcd] // abc == shadow
                                rng
                in
                let shadow_a = map_shadow shadow (proj 1) in
                let shadow_b = map_shadow shadow (proj 2) in
                let shadow_c = map_shadow shadow (proj 3) in
                let shadow_d = map_shadow shadow (proj 4) in
                S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.lid_Mktuple4) [U_zero;U_zero;U_zero;U_zero])
                            [S.iarg (type_of ea);
                             S.iarg (type_of eb);
                             S.iarg (type_of ec);
                             S.iarg (type_of ed);
                             S.as_arg (embed x1 rng shadow_a norm);
                             S.as_arg (embed x2 rng shadow_b norm);
                             S.as_arg (embed x3 rng shadow_c norm);
                             S.as_arg (embed x4 rng shadow_d norm)]
                            rng)
    in
    let un (t:term) norm : option ('a & 'b & 'c & 'd) =
        lazy_unembed
            printer
            emb_t_pair
            t
            typ
            (fun t ->
                let hd, args = U.head_and_args_full t in
                match (U.un_uinst hd).n, args with
                | Tm_fvar fv, [_; _; _; _; (a, _); (b, _); (c, _); (d, _)] when S.fv_eq_lid fv PC.lid_Mktuple4 ->
                    let open FStarC.Class.Monad in
                    let! a = try_unembed a norm in
                    let! b = try_unembed b norm in
                    let! c = try_unembed c norm in
                    let! d = try_unembed d norm in
                    Some (a, b, c, d)
                | _ -> None)
    in
    mk_emb_full
        em
        un
        typ
        printer
        emb_t_pair

let e_tuple5 (ea:embedding 'a) (eb:embedding 'b) (ec:embedding 'c) (ed:embedding 'd) (ee:embedding 'e) =
    let typ () = S.t_tuple5_of (type_of ea) (type_of eb) (type_of ec) (type_of ed) (type_of ee) in
    let emb_t_pair () =
        ET_app(PC.lid_tuple5 |> Ident.string_of_lid, [emb_typ_of 'a (); emb_typ_of 'b (); emb_typ_of 'c (); emb_typ_of 'd (); emb_typ_of 'e ()])
    in
    let printer (x, y, z, w, v) =
        BU.format5 "(%s, %s, %s, %s, %s)" (printer_of ea x) (printer_of eb y) (printer_of ec z) (printer_of ed w) (printer_of ee v)
    in
    let em (x1, x2, x3, x4, x5) (rng:range) shadow norm : term =
        lazy_embed
            printer
            emb_t_pair
            rng
            typ
            (x1, x2, x3, x4, x5)
            (fun () ->
                let proj i abcde =
                    let proj_i = U.mk_field_projector_name (PC.mk_tuple_data_lid 5 rng) (S.null_bv S.tun) i in
                    let proj_i_tm = S.fv_to_tm (lid_as_fv proj_i None) in
                    S.mk_Tm_app (S.mk_Tm_uinst proj_i_tm [U_zero])
                                [S.iarg (type_of ea);
                                 S.iarg (type_of eb);
                                 S.iarg (type_of ec);
                                 S.iarg (type_of ed);
                                 S.iarg (type_of ee);
                                 S.as_arg abcde] // abc == shadow
                                rng
                in
                let shadow_a = map_shadow shadow (proj 1) in
                let shadow_b = map_shadow shadow (proj 2) in
                let shadow_c = map_shadow shadow (proj 3) in
                let shadow_d = map_shadow shadow (proj 4) in
                let shadow_e = map_shadow shadow (proj 5) in
                S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.lid_Mktuple5) [U_zero;U_zero;U_zero;U_zero;U_zero])
                            [S.iarg (type_of ea);
                             S.iarg (type_of eb);
                             S.iarg (type_of ec);
                             S.iarg (type_of ed);
                             S.iarg (type_of ee);
                             S.as_arg (embed x1 rng shadow_a norm);
                             S.as_arg (embed x2 rng shadow_b norm);
                             S.as_arg (embed x3 rng shadow_c norm);
                             S.as_arg (embed x4 rng shadow_d norm);
                             S.as_arg (embed x5 rng shadow_e norm)]
                            rng)
    in
    let un (t:term) norm : option ('a & 'b & 'c & 'd & 'e) =
        lazy_unembed
            printer
            emb_t_pair
            t
            typ
            (fun t ->
                let hd, args = U.head_and_args_full t in
                match (U.un_uinst hd).n, args with
                | Tm_fvar fv, [_; _; _; _; _; (a, _); (b, _); (c, _); (d, _); (e, _)] when S.fv_eq_lid fv PC.lid_Mktuple5 ->
                    let open FStarC.Class.Monad in
                    let! a = try_unembed a norm in
                    let! b = try_unembed b norm in
                    let! c = try_unembed c norm in
                    let! d = try_unembed d norm in
                    let! e = try_unembed e norm in
                    Some (a, b, c, d, e)
                | _ -> None)
    in
    mk_emb_full
        em
        un
        typ
        printer
        emb_t_pair

let e_either (ea:embedding 'a) (eb:embedding 'b) =
    let typ () = S.t_either_of (type_of ea) (type_of eb) in
    let emb_t_sum_a_b () =
        ET_app(PC.either_lid |> Ident.string_of_lid, [emb_typ_of 'a (); emb_typ_of 'b ()])
    in
    let printer s =
        match s with
        | Inl a -> BU.format1 "Inl %s" (printer_of ea a)
        | Inr b -> BU.format1 "Inr %s" (printer_of eb b)
    in
    let em (s:either 'a 'b) (rng:range) shadow norm : term =
        lazy_embed
            printer
            emb_t_sum_a_b
            rng
            typ
            s
            (* Eagerly compute which closure we want, but thunk the actual embedding *)
            (match s with
             | Inl a ->
                (fun () ->
                let shadow_a = map_shadow shadow (fun t ->
                  let v = Ident.mk_ident ("v", rng) in
                  let some_v = U.mk_field_projector_name_from_ident PC.inl_lid v in
                  let some_v_tm = S.fv_to_tm (lid_as_fv some_v None) in
                  S.mk_Tm_app (S.mk_Tm_uinst some_v_tm [U_zero])
                              [S.iarg (type_of ea); S.iarg (type_of eb); S.as_arg t]
                              rng)
                in
                S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.inl_lid) [U_zero;U_zero])
                            [S.iarg (type_of ea);
                             S.iarg (type_of eb);
                             S.as_arg (embed a rng shadow_a norm)]
                            rng)
             | Inr b ->
                (fun () ->
                let shadow_b = map_shadow shadow (fun t ->
                  let v = Ident.mk_ident ("v", rng) in
                  let some_v = U.mk_field_projector_name_from_ident PC.inr_lid v in
                  let some_v_tm = S.fv_to_tm (lid_as_fv some_v None) in
                  S.mk_Tm_app (S.mk_Tm_uinst some_v_tm [U_zero])
                              [S.iarg (type_of ea); S.iarg (type_of eb); S.as_arg t]
                              rng)
                in
                S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.inr_lid) [U_zero;U_zero])
                            [S.iarg (type_of ea);
                             S.iarg (type_of eb);
                             S.as_arg (embed b rng shadow_b norm)]
                            rng)
             )
    in
    let un (t:term) norm : option (either 'a 'b) =
        lazy_unembed
            printer
            emb_t_sum_a_b
            t
            typ
            (fun t ->
                let hd, args = U.head_and_args_full t in
                match (U.un_uinst hd).n, args with
                | Tm_fvar fv, [_; _; (a, _)] when S.fv_eq_lid fv PC.inl_lid ->
                    BU.bind_opt (try_unembed a norm) (fun a ->
                    Some (Inl a))
                | Tm_fvar fv, [_; _; (b, _)] when S.fv_eq_lid fv PC.inr_lid ->
                    BU.bind_opt (try_unembed b norm) (fun b ->
                    Some (Inr b))
                | _ ->
                    None)
    in
    mk_emb_full
        em
        un
        typ
        printer
        emb_t_sum_a_b

let e_list (ea:embedding 'a) =
    let typ () = S.t_list_of (type_of ea) in
    let emb_t_list_a () =
        ET_app(PC.list_lid |> Ident.string_of_lid, [emb_typ_of 'a ()])
    in
    let printer =
        (fun (l:list 'a) -> "[" ^ (List.map (printer_of ea) l |> String.concat "; ") ^ "]")
    in
    let rec em (l:list 'a) (rng:range) shadow_l norm : term =
        lazy_embed
            printer
            emb_t_list_a
            rng
            typ
            l
            (fun () ->
                let t = S.iarg (type_of ea) in
                match l with
                | [] ->
                  S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.nil_lid) [U_zero]) //NS: the universe here is bogus
                              [t]
                              rng
                | hd::tl ->
                  let cons =
                      S.mk_Tm_uinst (S.tdataconstr PC.cons_lid) [U_zero]
                  in
                  let proj f cons_tm =
                    let fid = Ident.mk_ident (f, rng) in
                    let proj = U.mk_field_projector_name_from_ident PC.cons_lid fid in
                    let proj_tm = S.fv_to_tm (lid_as_fv proj None) in
                    S.mk_Tm_app (S.mk_Tm_uinst proj_tm [U_zero])
                                [S.iarg (type_of ea);
                                 S.as_arg cons_tm]
                                rng
                  in
                  let shadow_hd = map_shadow shadow_l (proj "hd") in
                  let shadow_tl = map_shadow shadow_l (proj "tl") in
                  S.mk_Tm_app cons
                              [t;
                               S.as_arg (embed hd rng shadow_hd norm);
                               S.as_arg (em tl rng shadow_tl norm)]
                              rng)
    in
    let rec un (t:term) norm : option (list 'a) =
        lazy_unembed
            printer
            emb_t_list_a
            t
            typ
            (fun t ->
                let hd, args = U.head_and_args_full t in
                match (U.un_uinst hd).n, args with
                | Tm_fvar fv, _
                    when S.fv_eq_lid fv PC.nil_lid -> Some []

                | Tm_fvar fv, [(_, Some ({aqual_implicit=true})); (hd, None); (tl, None)]
                | Tm_fvar fv, [(hd, None); (tl, None)]
                    when S.fv_eq_lid fv PC.cons_lid ->
                    BU.bind_opt (try_unembed hd norm) (fun hd ->
                    BU.bind_opt (un tl norm) (fun tl ->
                    Some (hd :: tl)))
                | _ ->
                    None)
    in
    mk_emb_full
        em
        un
        typ
        printer
        emb_t_list_a

let e_string_list = e_list e_string

(* the steps as terms *)
let steps_Simpl         = tconst PC.steps_simpl
let steps_Weak          = tconst PC.steps_weak
let steps_HNF           = tconst PC.steps_hnf
let steps_Primops       = tconst PC.steps_primops
let steps_Delta         = tconst PC.steps_delta
let steps_Zeta          = tconst PC.steps_zeta
let steps_ZetaFull      = tconst PC.steps_zeta_full
let steps_Iota          = tconst PC.steps_iota
let steps_Reify         = tconst PC.steps_reify
let steps_NormDebug     = tconst PC.steps_norm_debug
let steps_UnfoldOnly    = tconst PC.steps_unfoldonly
let steps_UnfoldFully   = tconst PC.steps_unfoldonly
let steps_UnfoldAttr    = tconst PC.steps_unfoldattr
let steps_UnfoldQual    = tconst PC.steps_unfoldqual
let steps_UnfoldNamespace = tconst PC.steps_unfoldnamespace
let steps_Unascribe     = tconst PC.steps_unascribe
let steps_NBE           = tconst PC.steps_nbe
let steps_Unmeta        = tconst PC.steps_unmeta

let e_norm_step : embedding Pervasives.norm_step =
    let typ () = S.t_norm_step in
    let emb_t_norm_step () = ET_app (PC.norm_step_lid |> Ident.string_of_lid, []) in
    let printer _ = "norm_step" in
    let em (n:Pervasives.norm_step) (rng:range) _shadow norm : term =
        lazy_embed
            printer
            emb_t_norm_step
            rng
            typ
            n
            (fun () ->
                match n with
                | Simpl ->
                    steps_Simpl
                | Weak ->
                    steps_Weak
                | HNF ->
                    steps_HNF
                | Primops ->
                    steps_Primops
                | Delta ->
                    steps_Delta
                | Zeta ->
                    steps_Zeta
                | ZetaFull ->
                    steps_ZetaFull
                | Iota ->
                    steps_Iota
                | Unascribe ->
                    steps_Unascribe
                | NBE ->
                    steps_NBE
                | Unmeta ->
                    steps_Unmeta
                | Reify ->
                    steps_Reify
                | NormDebug ->
                    steps_NormDebug
                | UnfoldOnly l ->
                    S.mk_Tm_app steps_UnfoldOnly [S.as_arg (embed l rng None norm)]
                                rng
                | UnfoldFully l ->
                    S.mk_Tm_app steps_UnfoldFully [S.as_arg (embed l rng None norm)]
                                rng
                | UnfoldAttr l ->
                    S.mk_Tm_app steps_UnfoldAttr [S.as_arg (embed l rng None norm)]
                                rng
                | UnfoldQual l ->
                    S.mk_Tm_app steps_UnfoldQual [S.as_arg (embed l rng None norm)]
                                rng
                | UnfoldNamespace l ->
                    S.mk_Tm_app steps_UnfoldNamespace [S.as_arg (embed l rng None norm)]
                                rng


                )
    in
    let un (t:term) norm : option Pervasives.norm_step =
        lazy_unembed
            printer
            emb_t_norm_step
            t
            typ
            (fun t ->
                let hd, args = U.head_and_args t in
                match (U.un_uinst hd).n, args with
                | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_simpl ->
                    Some Simpl
                | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_weak ->
                    Some Weak
                | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_hnf ->
                    Some HNF
                | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_primops ->
                    Some Primops
                | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_delta ->
                    Some Delta
                | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_zeta ->
                    Some Zeta
                | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_zeta_full ->
                    Some ZetaFull
                | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_iota ->
                    Some Iota
                | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_unascribe ->
                    Some Unascribe
                | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_nbe ->
                    Some NBE
                | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_unmeta ->
                    Some Unmeta
                | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_reify ->
                    Some Reify
                | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_norm_debug ->
                    Some NormDebug
                | Tm_fvar fv, [(l, _)] when S.fv_eq_lid fv PC.steps_unfoldonly ->
                    BU.bind_opt (try_unembed l norm) (fun ss ->
                    Some <| UnfoldOnly ss)
                | Tm_fvar fv, [(l, _)] when S.fv_eq_lid fv PC.steps_unfoldfully ->
                    BU.bind_opt (try_unembed l norm) (fun ss ->
                    Some <| UnfoldFully ss)
                | Tm_fvar fv, [(l, _)] when S.fv_eq_lid fv PC.steps_unfoldattr ->
                    BU.bind_opt (try_unembed l norm) (fun ss ->
                    Some <| UnfoldAttr ss)
                | Tm_fvar fv, [(l, _)] when S.fv_eq_lid fv PC.steps_unfoldqual ->
                    BU.bind_opt (try_unembed l norm) (fun ss ->
                    Some <| UnfoldQual ss)
                | Tm_fvar fv, [(l, _)] when S.fv_eq_lid fv PC.steps_unfoldnamespace ->
                    BU.bind_opt (try_unembed l norm) (fun ss ->
                    Some <| UnfoldNamespace ss)
                | _ -> None)
    in
    mk_emb_full
        em
        un
        typ
        printer
        emb_t_norm_step

let e_vconfig =
    let em (vcfg:vconfig) (rng:Range.range) _shadow norm : term =
      (* The order is very important here, even if this is a record. *)
      S.mk_Tm_app (tdataconstr PC.mkvconfig_lid) // TODO: should this be a record constructor? does it matter?
                  [S.as_arg (embed vcfg.initial_fuel                              rng None norm);
                   S.as_arg (embed vcfg.max_fuel                                  rng None norm);
                   S.as_arg (embed vcfg.initial_ifuel                             rng None norm);
                   S.as_arg (embed vcfg.max_ifuel                                 rng None norm);
                   S.as_arg (embed vcfg.detail_errors                             rng None norm);
                   S.as_arg (embed vcfg.detail_hint_replay                        rng None norm);
                   S.as_arg (embed vcfg.no_smt                                    rng None norm);
                   S.as_arg (embed vcfg.quake_lo                                  rng None norm);
                   S.as_arg (embed vcfg.quake_hi                                  rng None norm);
                   S.as_arg (embed vcfg.quake_keep                                rng None norm);
                   S.as_arg (embed vcfg.retry                                     rng None norm);
                   S.as_arg (embed vcfg.smtencoding_elim_box                      rng None norm);
                   S.as_arg (embed vcfg.smtencoding_nl_arith_repr                 rng None norm);
                   S.as_arg (embed vcfg.smtencoding_l_arith_repr                  rng None norm);
                   S.as_arg (embed vcfg.smtencoding_valid_intro                   rng None norm);
                   S.as_arg (embed vcfg.smtencoding_valid_elim                    rng None norm);
                   S.as_arg (embed vcfg.tcnorm                                    rng None norm);
                   S.as_arg (embed vcfg.no_plugins                                rng None norm);
                   S.as_arg (embed vcfg.no_tactics                                rng None norm);
                   S.as_arg (embed vcfg.z3cliopt                                  rng None norm);
                   S.as_arg (embed vcfg.z3smtopt                                  rng None norm);
                   S.as_arg (embed vcfg.z3refresh                                 rng None norm);
                   S.as_arg (embed vcfg.z3rlimit                                  rng None norm);
                   S.as_arg (embed vcfg.z3rlimit_factor                           rng None norm);
                   S.as_arg (embed vcfg.z3seed                                    rng None norm);
                   S.as_arg (embed vcfg.z3version                                 rng None norm);
                   S.as_arg (embed vcfg.trivial_pre_for_unannotated_effectful_fns rng None norm);
                   S.as_arg (embed vcfg.reuse_hint_for                            rng None norm);
                  ]
                  rng
    in
    let un (t:term) norm : option vconfig =
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        (* Sigh *)
        | Tm_fvar fv, [
            (initial_fuel, _);
            (max_fuel, _);
            (initial_ifuel, _);
            (max_ifuel, _);
            (detail_errors, _);
            (detail_hint_replay, _);
            (no_smt, _);
            (quake_lo, _);
            (quake_hi, _);
            (quake_keep, _);
            (retry, _);
            (smtencoding_elim_box, _);
            (smtencoding_nl_arith_repr, _);
            (smtencoding_l_arith_repr, _);
            (smtencoding_valid_intro, _);
            (smtencoding_valid_elim, _);
            (tcnorm, _);
            (no_plugins, _);
            (no_tactics, _);
            (z3cliopt, _);
            (z3smtopt, _);
            (z3refresh, _);
            (z3rlimit, _);
            (z3rlimit_factor, _);
            (z3seed, _);
            (z3version, _);
            (trivial_pre_for_unannotated_effectful_fns, _);
            (reuse_hint_for, _)
            ] when S.fv_eq_lid fv PC.mkvconfig_lid ->
                  BU.bind_opt (try_unembed initial_fuel norm) (fun initial_fuel ->
                  BU.bind_opt (try_unembed max_fuel norm) (fun max_fuel ->
                  BU.bind_opt (try_unembed initial_ifuel norm) (fun initial_ifuel ->
                  BU.bind_opt (try_unembed max_ifuel norm) (fun max_ifuel ->
                  BU.bind_opt (try_unembed detail_errors norm) (fun detail_errors ->
                  BU.bind_opt (try_unembed detail_hint_replay norm) (fun detail_hint_replay ->
                  BU.bind_opt (try_unembed no_smt norm) (fun no_smt ->
                  BU.bind_opt (try_unembed quake_lo norm) (fun quake_lo ->
                  BU.bind_opt (try_unembed quake_hi norm) (fun quake_hi ->
                  BU.bind_opt (try_unembed quake_keep norm) (fun quake_keep ->
                  BU.bind_opt (try_unembed retry norm) (fun retry ->
                  BU.bind_opt (try_unembed smtencoding_elim_box norm) (fun smtencoding_elim_box ->
                  BU.bind_opt (try_unembed smtencoding_nl_arith_repr norm) (fun smtencoding_nl_arith_repr ->
                  BU.bind_opt (try_unembed smtencoding_l_arith_repr norm) (fun smtencoding_l_arith_repr ->
                  BU.bind_opt (try_unembed smtencoding_valid_intro norm) (fun smtencoding_valid_intro ->
                  BU.bind_opt (try_unembed smtencoding_valid_elim norm) (fun smtencoding_valid_elim ->
                  BU.bind_opt (try_unembed tcnorm norm) (fun tcnorm ->
                  BU.bind_opt (try_unembed no_plugins norm) (fun no_plugins ->
                  BU.bind_opt (try_unembed no_tactics norm) (fun no_tactics ->
                  BU.bind_opt (try_unembed z3cliopt norm) (fun z3cliopt ->
                  BU.bind_opt (try_unembed z3smtopt norm) (fun z3smtopt ->
                  BU.bind_opt (try_unembed z3refresh norm) (fun z3refresh ->
                  BU.bind_opt (try_unembed z3rlimit norm) (fun z3rlimit ->
                  BU.bind_opt (try_unembed z3rlimit_factor norm) (fun z3rlimit_factor ->
                  BU.bind_opt (try_unembed z3seed norm) (fun z3seed ->
                  BU.bind_opt (try_unembed z3version norm) (fun z3version ->
                  BU.bind_opt (try_unembed trivial_pre_for_unannotated_effectful_fns norm) (fun trivial_pre_for_unannotated_effectful_fns ->
                  BU.bind_opt (try_unembed reuse_hint_for norm) (fun reuse_hint_for ->
                  Some ({
                    initial_fuel = initial_fuel;
                    max_fuel = max_fuel;
                    initial_ifuel = initial_ifuel;
                    max_ifuel = max_ifuel;
                    detail_errors = detail_errors;
                    detail_hint_replay = detail_hint_replay;
                    no_smt = no_smt;
                    quake_lo = quake_lo;
                    quake_hi = quake_hi;
                    quake_keep = quake_keep;
                    retry = retry;
                    smtencoding_elim_box = smtencoding_elim_box;
                    smtencoding_nl_arith_repr = smtencoding_nl_arith_repr;
                    smtencoding_l_arith_repr = smtencoding_l_arith_repr;
                    smtencoding_valid_intro = smtencoding_valid_intro;
                    smtencoding_valid_elim = smtencoding_valid_elim;
                    tcnorm = tcnorm;
                    no_plugins = no_plugins;
                    no_tactics = no_tactics;
                    z3cliopt = z3cliopt;
                    z3smtopt = z3smtopt;
                    z3refresh = z3refresh;
                    z3rlimit = z3rlimit;
                    z3rlimit_factor = z3rlimit_factor;
                    z3seed = z3seed;
                    z3version = z3version;
                    trivial_pre_for_unannotated_effectful_fns = trivial_pre_for_unannotated_effectful_fns;
                    reuse_hint_for = reuse_hint_for;
                  })))))))))))))))))))))))))))))
        | _ ->
          None
    in
    mk_emb_full
        em
        un
        (fun () -> S.t_vconfig)
        (fun _ -> "vconfig")
        (fun () -> ET_app (PC.vconfig_lid |> Ident.string_of_lid, []))

let e_order =
  let open FStarC.Compiler.Order in
  let ord_Lt_lid = Ident.lid_of_path (["FStar"; "Order"; "Lt"]) Range.dummyRange in
  let ord_Eq_lid = Ident.lid_of_path (["FStar"; "Order"; "Eq"]) Range.dummyRange in
  let ord_Gt_lid = Ident.lid_of_path (["FStar"; "Order"; "Gt"]) Range.dummyRange in
  let ord_Lt = tdataconstr ord_Lt_lid in
  let ord_Eq = tdataconstr ord_Eq_lid in
  let ord_Gt = tdataconstr ord_Gt_lid in
  let ord_Lt_fv = lid_as_fv ord_Lt_lid (Some Data_ctor) in
  let ord_Eq_fv = lid_as_fv ord_Eq_lid (Some Data_ctor) in
  let ord_Gt_fv = lid_as_fv ord_Gt_lid (Some Data_ctor) in
  let embed_order (o:order) rng shadow cb : term =
      let r =
      match o with
      | Lt -> ord_Lt
      | Eq -> ord_Eq
      | Gt -> ord_Gt
      in { r with pos = rng }
  in
  let unembed_order (t:term) cb : option order =
      let t = U.unascribe t in
      let hd, args = U.head_and_args t in
      match (U.un_uinst hd).n, args with
      | Tm_fvar fv, [] when S.fv_eq_lid fv ord_Lt_lid -> Some Lt
      | Tm_fvar fv, [] when S.fv_eq_lid fv ord_Eq_lid -> Some Eq
      | Tm_fvar fv, [] when S.fv_eq_lid fv ord_Gt_lid -> Some Gt
      | _ ->
          None
  in
  mk_emb embed_order unembed_order (lid_as_fv PC.order_lid None)

let or_else (f: option 'a) (g:unit -> 'a) =
    match f with
    | Some x -> x
    | None -> g ()

let e_arrow (ea:embedding 'a) (eb:embedding 'b) : Tot (embedding ('a -> 'b)) =
    let typ () =
        S.mk (Tm_arrow {bs=[S.mk_binder (S.null_bv (type_of ea))];
                        comp=S.mk_Total (type_of eb)})
              Range.dummyRange
    in
    let emb_t_arr_a_b () = ET_fun(emb_typ_of 'a (), emb_typ_of 'b ()) in
    let printer (f:'a -> 'b) = "<fun>" in
    let em (f:'a -> 'b) rng shadow_f norm =
        // let f_wrapped (x:term) =
        //     let shadow_app = map_shadow shadow_f (fun f ->
        //         S.mk_Tm_app f [S.as_arg x] None rng)
        //     in
        //     or_else
        //     (BU.map_opt (unembed ea x true norm) (fun x ->
        //         embed eb (f x) rng shadow_app norm))
        //     (fun () ->
        //         match force_shadow shadow_app with
        //         | None -> raise Embedding_failure
        //         | Some app -> norm (BU.Inr app))
        // in
        lazy_embed
            printer
            emb_t_arr_a_b
            rng
            typ
            f //f_wrapped
            (fun () ->
                match force_shadow shadow_f with
                | None -> raise Embedding_failure //TODO: dodgy
                | Some repr_f ->
                  if !Options.debug_embedding then
                  BU.print2 "e_arrow forced back to term using shadow %s; repr=%s\n"
                                   (show repr_f)
                                   (BU.stack_dump());
                  let res = norm (Inr repr_f) in
                  if !Options.debug_embedding then
                  BU.print3 "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                                   (show repr_f)
                                   (show res)
                                   (BU.stack_dump());
                  res)
    in
    let un (f:term) norm : option ('a -> 'b) =
        lazy_unembed
            printer
            emb_t_arr_a_b
            f
            typ
            (fun f ->
                let f_wrapped (a:'a) : 'b =
                    if !Options.debug_embedding then
                    BU.print2 "Calling back into normalizer for %s\n%s\n"
                              (show f)
                              (BU.stack_dump());
                    let a_tm = embed a f.pos None norm in
                    let b_tm = norm (Inr (S.mk_Tm_app f [S.as_arg a_tm] f.pos)) in
                    match unembed b_tm norm with
                    | None -> raise Unembedding_failure
                    | Some b -> b
                in
                Some f_wrapped)
    in
    mk_emb_full
        em
        un
        typ
        printer
        emb_t_arr_a_b

let e_sealed (ea : embedding 'a) : Tot (embedding (Sealed.sealed 'a)) =
    let typ () = S.t_sealed_of (type_of ea) in
    let emb_ty_a () =
        ET_app(PC.sealed_lid |> Ident.string_of_lid, [emb_typ_of 'a ()])
    in
    let printer x = "(seal " ^ printer_of ea (Sealed.unseal x) ^ ")" in
    let em (a:Sealed.sealed 'a) (rng:range) shadow norm : term =
      let shadow_a =
        (* TODO: this application below is in TAC.. OK? *)
        map_shadow shadow (fun t ->
          let unseal = U.fvar_const PC.unseal_lid in
          S.mk_Tm_app (S.mk_Tm_uinst unseal [U_zero])
                      [S.iarg (type_of ea); S.as_arg t]
                      rng)
      in
      S.mk_Tm_app (S.mk_Tm_uinst (U.fvar_const PC.seal_lid) [U_zero])
                  [S.iarg (type_of ea); S.as_arg (embed (Sealed.unseal a) rng shadow_a norm)]
                  rng
    in
    let un (t:term) norm : option (Sealed.sealed 'a) =
      let hd, args = U.head_and_args_full t in
      match (U.un_uinst hd).n, args with
      | Tm_fvar fv, [_; (a, _)] when S.fv_eq_lid fv PC.seal_lid ->
           // Just relay it
           Class.Monad.fmap Sealed.seal <| try_unembed a norm
      | _ ->
           None
    in
    mk_emb_full
        em
        un
        typ
        printer
        emb_ty_a

(*
 * Embed a range as a FStar.Range.__range
 * The user usually manipulates a FStar.Range.range = sealed __range
 * For embedding an actual FStar.Range.range, we compose this (automatically
 * via typeclass resolution) with e_sealed.
 *)
let e___range =
    let em (r:range) (rng:range) _shadow _norm : term =
        S.mk (Tm_constant (C.Const_range r)) rng
    in
    let un (t:term) _norm : option range =
        match (SS.compress t).n with
        | Tm_constant (C.Const_range r) -> Some r
        | _ -> None
    in
    mk_emb_full
        em
        un
        (fun () -> S.t___range)
        Range.string_of_range
        (fun () -> ET_app (PC.range_lid |> Ident.string_of_lid, []))

(* This is an odd one. We embed ranges as sealed, but we don't want to use the Sealed.sealed
type internally, so we "hack" it like this. *)
let e_range : embedding Range.range =
  embed_as (e_sealed e___range) Sealed.unseal Sealed.seal None

let e_issue : embedding Err.issue = e_lazy Lazy_issue (S.fvar PC.issue_lid None)
let e_document : embedding Pprint.document = e_lazy Lazy_doc (S.fvar PC.document_lid None)

 /////////////////////////////////////////////////////////////////////
 //Registering top-level functions
 /////////////////////////////////////////////////////////////////////

let arrow_as_prim_step_1 (ea:embedding 'a) (eb:embedding 'b)
                         (f:'a -> 'b) (fv_lid:Ident.lid) norm
   : universes -> args -> option term =
    let rng = Ident.range_of_lid fv_lid in
    let f_wrapped _us args =
        //arity mismatches are handled by the caller
        let [(x, _)] = args in
        let shadow_app =
            Some (Thunk.mk (fun () -> S.mk_Tm_app (norm (Inl fv_lid)) args rng))
        in
        match
            (BU.map_opt (try_unembed x norm) (fun x ->
             embed (f x) rng shadow_app norm))
        with
        // NB: this always returns a Some
        | Some x -> Some x
        | None -> force_shadow shadow_app
    in
    f_wrapped

let arrow_as_prim_step_2 (ea:embedding 'a) (eb:embedding 'b) (ec:embedding 'c)
                         (f:'a -> 'b -> 'c) fv_lid norm
   : universes -> args -> option term =
    let rng = Ident.range_of_lid fv_lid in
    let f_wrapped _us args =
        //arity mismatches are handled by the caller
        let [(x, _); (y, _)] = args in
        let shadow_app =
            Some (Thunk.mk (fun () -> S.mk_Tm_app (norm (Inl fv_lid)) args rng))
        in
        match
            (BU.bind_opt (try_unembed x norm) (fun x ->
             BU.bind_opt (try_unembed y norm) (fun y ->
             Some (embed (f x y) rng shadow_app norm))))
        with
        // NB: this always returns a Some
        | Some x -> Some x
        | None -> force_shadow shadow_app
    in
    f_wrapped

let arrow_as_prim_step_3 (ea:embedding 'a) (eb:embedding 'b)
                         (ec:embedding 'c) (ed:embedding 'd)
                         (f:'a -> 'b -> 'c -> 'd) fv_lid norm
   : universes -> args -> option term =
    let rng = Ident.range_of_lid fv_lid in
    let f_wrapped _us args =
        //arity mismatches are handled by the caller
        let [(x, _); (y, _); (z, _)] = args in
        let shadow_app =
            Some (Thunk.mk (fun () -> S.mk_Tm_app (norm (Inl fv_lid)) args rng))
        in
        match
            (BU.bind_opt (try_unembed x norm) (fun x ->
             BU.bind_opt (try_unembed y norm) (fun y ->
             BU.bind_opt (try_unembed z norm) (fun z ->
             Some (embed (f x y z) rng shadow_app norm)))))
        with
        // NB: this always returns a Some
        | Some x -> Some x
        | None -> force_shadow shadow_app
    in
    f_wrapped

let debug_wrap (s:string) (f:unit -> 'a) =
    if !Options.debug_embedding
    then BU.print1 "++++starting %s\n" s;
    let res = f () in
    if !Options.debug_embedding
    then BU.print1 "------ending %s\n" s;
    res

instance e_abstract_term : embedding abstract_term =
  embed_as e_any (fun x -> Abstract x) (fun x -> match x with Abstract x -> x) None
