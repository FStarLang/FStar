﻿(*
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

module FStar.Syntax.Embeddings.Base

open FStar
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Compiler.Range
open FStar.Pervasives
open FStar.Syntax.Syntax

module BU    = FStar.Compiler.Util
module Err   = FStar.Errors
module Ident = FStar.Ident
module PC    = FStar.Parser.Const
module Print = FStar.Syntax.Print
module S     = FStar.Syntax.Syntax
module SS    = FStar.Syntax.Subst
module U     = FStar.Syntax.Util

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

type embedding (a:Type0) = {
  em : a -> embed_t;
  un : term -> unembed_t a;
  typ : typ;
  print: printer a;
  emb_typ: emb_typ
}
let emb_typ_of e = e.emb_typ

let unknown_printer typ _ =
    BU.format1 "unknown %s" (Print.term_to_string typ)

let term_as_fv t =
    match (SS.compress t).n with
    | Tm_fvar fv -> fv
    | _ -> failwith (BU.format1 "Embeddings not defined for type %s" (Print.term_to_string t))

let mk_emb em un fv =
    let typ = S.fv_to_tm fv in
    {
        em = em ;
        un = un ;
        typ = typ;
        print=unknown_printer typ;
        emb_typ=ET_app (S.lid_of_fv fv |> Ident.string_of_lid, [])
    }

let mk_emb_full em un typ printer emb_typ = {
    em = em ;
    un = un ;
    typ = typ;
    print = printer;
    emb_typ = emb_typ
}

//
// AR/NS: 04/22/2022:
//        In the case of metaprograms, we reduce divergent terms in
//        the normalizer, therefore, the final result that we get
//        may be wrapped in a Meta_monadic node (e.g. lift, app, etc.)
//        Before unembedding the result of such a computation,
//          we strip those meta nodes
//        In case the term inside is not a result, unembedding would
//          anyway fail
//        And we strip down only DIV
//        Can we get any other effect? Not today, since from the client
//          code, we enforce terms to be normalized to be PURE
//

let rec unmeta_div_results t =
  let open FStar.Ident in
  match (SS.compress t).n with
  | Tm_meta {tm=t'; meta=Meta_monadic_lift (src, dst, _)} ->
    if lid_equals src PC.effect_PURE_lid &&
       lid_equals dst PC.effect_DIV_lid
    then unmeta_div_results t'
    else t

  | Tm_meta {tm=t'; meta=Meta_monadic (m, _)} ->
    if lid_equals m PC.effect_DIV_lid
    then unmeta_div_results t'
    else t

  | Tm_meta {tm=t'} -> unmeta_div_results t'

  | Tm_ascribed {tm=t'} -> unmeta_div_results t'

  | _ -> t

let type_of      (e:embedding 'a) = e.typ
let printer_of   (e:embedding 'a) = e.print
let set_type ty  (e:embedding 'a) = { e with typ = ty }

let embed        (e:embedding 'a) = e.em
let try_unembed  (e:embedding 'a) t n =
  (* Unembed always receives a term without the meta_monadics above,
  strip it here. TODO: maybe also compress? *)
  let t = unmeta_div_results t in
  e.un t n

let unembed (e:embedding 'a) t n =
  let r = try_unembed e t n in
  if None? r then
    Err.log_issue t.pos (Err.Warning_NotEmbedded,
              BU.format3 "Warning, unembedding failed for type %s (%s); term = %s"
                          (Print.term_to_string (type_of e))
                          (Print.emb_typ_to_string (emb_typ_of e))
                          (Print.term_to_string t)
                          );
  r


let embed_as (ea:embedding 'a) (ab : 'a -> 'b) (ba : 'b -> 'a) (o:option typ) =
    mk_emb_full (fun (x:'b) -> embed ea (ba x))
                (fun (t:term) cb -> BU.map_opt (try_unembed ea t cb) ab)
                (match o with | Some t -> t | _ -> type_of ea)
                (fun (x:'b) -> BU.format1 "(embed_as>> %s)\n" (ea.print (ba x)))
                ea.emb_typ

(* A simple lazy embedding, without cancellations nor an expressive type. *)
let e_lazy #a (k:lazy_kind) (ty : typ) : embedding a =
  let ee (x:a) rng _topt _norm : term = U.mk_lazy x ty k (Some rng) in
  let uu (t:term) _norm : option a =
    let t0 = t in
    match (SS.compress t).n with
    | Tm_lazy {blob=b; lkind=lkind} when U.eq_lazy_kind lkind k -> Some (Dyn.undyn b)
    | Tm_lazy {blob=b; lkind=lkind} ->
      (* This is very likely a bug, warn! *)
      Err.log_issue t0.pos (Err.Warning_NotEmbedded,
                BU.format3 "Warning, lazy unembedding failed, tag mismatch.\n\t\
                            Expected %s, got %s\n\t\
                            t = %s."
                            (U.lazy_kind_to_string lkind) (U.lazy_kind_to_string k)
                            (Print.term_to_string t0));
      None
    | _ ->
      None
  in
  mk_emb ee uu (term_as_fv ty)

let lazy_embed (pa:printer 'a) (et:emb_typ) rng ta (x:'a) (f:unit -> term) =
    if !Options.debug_embedding
    then BU.print3 "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n"
                         (Print.term_to_string ta)
                         (Print.emb_typ_to_string et)
                         (pa x);
    if !Options.eager_embedding
    then f()
    else let thunk = Thunk.mk f in
         U.mk_lazy x S.tun (Lazy_embedding (et, thunk)) (Some rng)

let lazy_unembed (pa:printer 'a) (et:emb_typ) (x:term) (ta:term) (f:term -> option 'a) : option 'a =
    let x = SS.compress x in
    match x.n with
    | Tm_lazy {blob=b; lkind=Lazy_embedding (et', t)}  ->
      if et <> et'
      || !Options.eager_embedding
      then let res = f (Thunk.force t) in
           let _ = if !Options.debug_embedding
                   then BU.print3 "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                                (Print.emb_typ_to_string et)
                                (Print.emb_typ_to_string et')
                                (match res with None -> "None" | Some x -> "Some " ^ (pa x))
           in
           res
      else let a = Dyn.undyn b in
           let _ = if !Options.debug_embedding
                   then BU.print2 "Unembed cancelled for %s\n\tvalue is %s\n"
                                (Print.emb_typ_to_string et)
                                  (pa a)
           in
           Some a
    | _ ->
      let aopt = f x in
      let _ = if !Options.debug_embedding
              then BU.print3 "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                               (Print.emb_typ_to_string et)
                               (Print.term_to_string x)
                               (match aopt with None -> "None" | Some a -> "Some " ^ pa a) in
      aopt

let (let?) o f = BU.bind_opt o f

let mk_extracted_embedding (name: string) (u: string & list term -> option 'a) (e: 'a -> term) : embedding 'a =
  let uu (t:term) _norm : option 'a =
    let hd, args = U.head_and_args t in
    let? hd_lid =
      match (SS.compress (U.un_uinst hd)).n with
      | Tm_fvar fv -> Some fv.fv_name.v
      | _ -> None
    in
    u (Ident.string_of_lid hd_lid, List.map fst args)
  in
  let ee (x:'a) rng _topt _norm : term = e x in
  mk_emb ee uu (S.lid_as_fv (Ident.lid_of_str name) None)

let extracted_embed (e: embedding 'a) (x: 'a) : term =
  embed e x Range.dummyRange None id_norm_cb

let extracted_unembed (e: embedding 'a) (t: term) : option 'a =
  try_unembed e t id_norm_cb
