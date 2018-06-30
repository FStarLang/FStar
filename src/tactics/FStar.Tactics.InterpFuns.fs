#light "off"
module FStar.Tactics.InterpFuns

(* This module is awful, don't even look at it please. *)

open FStar
open FStar.All
open FStar.Syntax.Syntax
open FStar.Range

open FStar.Tactics.Types
open FStar.Tactics.Result
open FStar.Syntax.Embeddings
open FStar.Tactics.Basic
open FStar.Tactics.Native

module S     = FStar.Syntax.Syntax
module SS    = FStar.Syntax.Subst
module PC    = FStar.Parser.Const
module BU    = FStar.Util
module Print = FStar.Syntax.Print
module Cfg   = FStar.TypeChecker.Cfg
module E     = FStar.Tactics.Embedding
module RE    = FStar.Reflection.Embeddings
module NBETerm = FStar.TypeChecker.NBETerm

let extract_1 (ea:embedding<'a>)
              (args:args) : option<'a> =
    match args with
    | [(a, _)] ->
      BU.bind_opt (unembed ea a) (fun a ->
      Some a)
    | _ ->
      failwith "extract_1: wrong number of arguments"

let extract_2 (ea:embedding<'a>) (eb:embedding<'b>)
              (args:args) : option<('a * 'b)> =
    match args with
    | [(a, _); (b, _)] ->
      BU.bind_opt (unembed ea a) (fun a ->
      BU.bind_opt (unembed eb b) (fun b ->
      Some (a, b)))
    | _ ->
      failwith "extract_2: wrong number of arguments"

let extract_3 (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>)
              (args:args) : option<('a * 'b * 'c)> =
    match args with
    | [(a, _); (b, _); (c, _)] ->
      BU.bind_opt (unembed ea a) (fun a ->
      BU.bind_opt (unembed eb b) (fun b ->
      BU.bind_opt (unembed ec c) (fun c ->
      Some (a, b, c))))
    | _ ->
      failwith "extract_3: wrong number of arguments"

let extract_4 (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>) (ed:embedding<'d>)
              (args:args) : option<('a * 'b * 'c * 'd)> =
    match args with
    | [(a, _); (b, _); (c, _); (d, _)] ->
      BU.bind_opt (unembed ea a) (fun a ->
      BU.bind_opt (unembed eb b) (fun b ->
      BU.bind_opt (unembed ec c) (fun c ->
      BU.bind_opt (unembed ed d) (fun d ->
      Some (a, b, c, d)))))
    | _ ->
      failwith "extract_4: wrong number of arguments"

let extract_5 (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>) (ed:embedding<'d>)
              (ee:embedding<'e>)
              (args:args) : option<('a * 'b * 'c * 'd * 'e)> =
    match args with
    | [(a, _); (b, _); (c, _); (d, _); (e, _)] ->
      BU.bind_opt (unembed ea a) (fun a ->
      BU.bind_opt (unembed eb b) (fun b ->
      BU.bind_opt (unembed ec c) (fun c ->
      BU.bind_opt (unembed ed d) (fun d ->
      BU.bind_opt (unembed ee e) (fun e ->
      Some (a, b, c, d, e))))))
    | _ ->
      failwith "extract_5: wrong number of arguments"

let extract_6 (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>) (ed:embedding<'d>)
              (ee:embedding<'e>) (ef:embedding<'f>)
              (args:args) : option<('a * 'b * 'c * 'd * 'e * 'f)> =
    match args with
    | [(a, _); (b, _); (c, _); (d, _); (e, _); (f, _)] ->
      BU.bind_opt (unembed ea a) (fun a ->
      BU.bind_opt (unembed eb b) (fun b ->
      BU.bind_opt (unembed ec c) (fun c ->
      BU.bind_opt (unembed ed d) (fun d ->
      BU.bind_opt (unembed ee e) (fun e ->
      BU.bind_opt (unembed ef f) (fun f ->
      Some (a, b, c, d, e, f)))))))
    | _ ->
      failwith "extract_6: wrong number of arguments"

let extract_7 (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>) (ed:embedding<'d>)
              (ee:embedding<'e>) (ef:embedding<'f>) (eg:embedding<'g>)
              (args:args) : option<('a * 'b * 'c * 'd * 'e * 'f * 'g)> =
    match args with
    | [(a, _); (b, _); (c, _); (d, _); (e, _); (f, _); (g, _)] ->
      BU.bind_opt (unembed ea a) (fun a ->
      BU.bind_opt (unembed eb b) (fun b ->
      BU.bind_opt (unembed ec c) (fun c ->
      BU.bind_opt (unembed ed d) (fun d ->
      BU.bind_opt (unembed ee e) (fun e ->
      BU.bind_opt (unembed ef f) (fun f ->
      BU.bind_opt (unembed eg g) (fun g ->
      Some (a, b, c, d, e, f, g))))))))
    | _ ->
      failwith "extract_7: wrong number of arguments"

let mk_tactic_interpretation_1 (t:'a -> tac<'r>)
                               (ea:embedding<'a>) (er:embedding<'r>)
                               (psc:Cfg.psc) (args:args) : option<term> =
  BU.bind_opt (extract_2 ea E.e_proofstate args) (fun (a, ps) ->
  let ps = set_ps_psc psc ps in
  let r = run_safe (t a) ps in
  Some (embed (E.e_result er) (Cfg.psc_range psc) r))

let mk_tactic_interpretation_2 (t:'a -> 'b -> tac<'r>)
                               (ea:embedding<'a>) (eb:embedding<'b>) (er:embedding<'r>)
                               (psc:Cfg.psc) (args:args) : option<term> =
  BU.bind_opt (extract_3 ea eb E.e_proofstate args) (fun (a, b, ps) ->
  let ps = set_ps_psc psc ps in
  let r = run_safe (t a b) ps in
  Some (embed (E.e_result er) (Cfg.psc_range psc) r))

let mk_tactic_interpretation_3 (t:'a -> 'b -> 'c -> tac<'r>)
                               (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>) (er:embedding<'r>)
                               (psc:Cfg.psc) (args:args) : option<term> =
  BU.bind_opt (extract_4 ea eb ec E.e_proofstate args) (fun (a, b, c, ps) ->
  let ps = set_ps_psc psc ps in
  let r = run_safe (t a b c) ps in
  Some (embed (E.e_result er) (Cfg.psc_range psc) r))

let mk_tactic_interpretation_4 (t:'a -> 'b -> 'c -> 'd -> tac<'r>)
                               (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>) (ed:embedding<'d>)
                               (er:embedding<'r>)
                               (psc:Cfg.psc) (args:args) : option<term> =
  BU.bind_opt (extract_5 ea eb ec ed E.e_proofstate args) (fun (a, b, c, d, ps) ->
  let ps = set_ps_psc psc ps in
  let r = run_safe (t a b c d) ps in
  Some (embed (E.e_result er) (Cfg.psc_range psc) r))

let mk_tactic_interpretation_5 (t:'a -> 'b -> 'c -> 'd -> 'e -> tac<'r>)
                               (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>) (ed:embedding<'d>)
                               (ee:embedding<'e>) (er:embedding<'r>)
                               (psc:Cfg.psc) (args:args) : option<term> =
  BU.bind_opt (extract_6 ea eb ec ed ee E.e_proofstate args) (fun (a, b, c, d, e, ps) ->
  let ps = set_ps_psc psc ps in
  let r = run_safe (t a b c d e) ps in
  Some (embed (E.e_result er) (Cfg.psc_range psc) r))

let mk_tactic_interpretation_6 (t:'a -> 'b -> 'c -> 'd -> 'e -> 'f -> tac<'r>)
                               (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>) (ed:embedding<'d>)
                               (ee:embedding<'e>) (ef:embedding<'f>) (er:embedding<'r>)
                               (psc:Cfg.psc) (args:args) : option<term> =
  BU.bind_opt (extract_7 ea eb ec ed ee ef E.e_proofstate args) (fun (a, b, c, d, e, f, ps) ->
  let ps = set_ps_psc psc ps in
  let r = run_safe (t a b c d e f) ps in
  Some (embed (E.e_result er) (Cfg.psc_range psc) r))

let step_from_native_step (s: native_primitive_step): Cfg.primitive_step =
  { Cfg.name                         = s.name
  ; Cfg.arity                        = s.arity
  ; Cfg.univ_arity                   = 0 // Zoe : We might need to change that
  ; Cfg.auto_reflect                 = Some (s.arity - 1)
  ; Cfg.strong_reduction_ok          = s.strong_reduction_ok
  ; Cfg.requires_binder_substitution = false // GM: Don't think we care about pretty-printing on native
  ; Cfg.interpretation               = s.tactic
  ; Cfg.interpretation_nbe           = NBETerm.dummy_interp s.name
  }

let mk nm arity nunivs interpretation =
  let nm = E.fstar_tactics_lid' ["Builtins"; nm] in
  { Cfg.name                         = nm
  ; Cfg.arity                        = arity
  ; Cfg.univ_arity                   = nunivs
  ; Cfg.auto_reflect                 = Some (arity - 1)
  ; Cfg.strong_reduction_ok          = true
  ; Cfg.requires_binder_substitution = true
  ; Cfg.interpretation               = interpretation
  ; Cfg.interpretation_nbe           = NBETerm.dummy_interp nm
  }

let native_tactics = list_all ()
let native_tactics_steps = List.map step_from_native_step native_tactics

let mktac1 (nunivs:int) (name : string) (f : 'a -> tac<'r>)
           (ea : embedding<'a>)
           (er : embedding<'r>) : Cfg.primitive_step =
    mk name 2 nunivs (mk_tactic_interpretation_1 f ea er)

let mktac2 (nunivs:int) (name : string) (f : 'a -> 'b -> tac<'r>)
           (ea : embedding<'a>) (eb : embedding<'b>)
           (er : embedding<'r>) : Cfg.primitive_step =
    mk name 3 nunivs (mk_tactic_interpretation_2 f ea eb er)

let mktac3 (nunivs:int) (name : string) (f : 'a -> 'b -> 'c -> tac<'r>)
           (ea : embedding<'a>) (eb : embedding<'b>) (ec : embedding<'c>)
           (er : embedding<'r>) : Cfg.primitive_step =
    mk name 4 nunivs (mk_tactic_interpretation_3 f ea eb ec er)

let mktac4 (nunivs:int) (name : string) (f : 'a -> 'b -> 'c -> 'd -> tac<'r>)
           (ea : embedding<'a>) (eb : embedding<'b>) (ec : embedding<'c>)
           (ed : embedding<'d>)
           (er : embedding<'r>) : Cfg.primitive_step =
    mk name 5 nunivs (mk_tactic_interpretation_4 f ea eb ec ed er)

let mktac5 (nunivs:int) (name : string) (f : 'a -> 'b -> 'c -> 'd -> 'e -> tac<'r>)
           (ea : embedding<'a>) (eb : embedding<'b>) (ec : embedding<'c>)
           (ed : embedding<'d>) (ee : embedding<'e>)
           (er : embedding<'r>) : Cfg.primitive_step =
    mk name 6 nunivs (mk_tactic_interpretation_5 f ea eb ec ed ee er)
