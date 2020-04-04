#light "off"
module FStar.Tactics.InterpFuns

(* This module is awful, don't even look at it please. *)

open FStar
open FStar.All

open FStar.Syntax.Embeddings
open FStar.Tactics.Monad

module Cfg   = FStar.TypeChecker.Cfg
module NBET  = FStar.TypeChecker.NBETerm

(* These functions are suboptimal, since they need to take embeddings for both
 * the interpreter AND the NBE evaluator. Attempting to coallesce them
 * is not easy, since we have some parametric e_any embeddings of differing types
 * (Syntax.embedding<term> vs NBET.embedding<NBET.t>). So we pass both of them.
 * We also need to pass in two versions of the underlying primitive, since they
 * will be instantiated differently (again term vs NBET.t). Such is life
 * without higher-order polymorphism. *)

val mktac1
    (nunivs:int)
    (name : string)
    (f : 'a -> tac<'r>)
    (ea : embedding<'a>)
    (er : embedding<'r>)
    (nf : 'na -> tac<'nr>)
    (nea : NBET.embedding<'na>)
    (ner : NBET.embedding<'nr>)
    : Cfg.primitive_step

val mktac2
    (nunivs:int)
    (name : string)
    (f : 'a -> 'b -> tac<'r>)
    (ea : embedding<'a>)
    (eb : embedding<'b>)
    (er : embedding<'r>)
    (nf : 'na -> 'nb -> tac<'nr>)
    (nea : NBET.embedding<'na>)
    (neb : NBET.embedding<'nb>)
    (ner : NBET.embedding<'nr>)
    : Cfg.primitive_step

val mktac3
    (nunivs:int)
    (name : string)
    (f : 'a -> 'b -> 'c -> tac<'r>)
    (ea : embedding<'a>)
    (eb : embedding<'b>)
    (ec : embedding<'c>)
    (er : embedding<'r>)
    (nf : 'na -> 'nb -> 'nc -> tac<'nr>)
    (nea : NBET.embedding<'na>)
    (neb : NBET.embedding<'nb>)
    (nec : NBET.embedding<'nc>)
    (ner : NBET.embedding<'nr>)
    : Cfg.primitive_step

val mktac4
    (nunivs:int)
    (name : string)
    (f : 'a -> 'b -> 'c -> 'd -> tac<'r>)
    (ea : embedding<'a>)
    (eb : embedding<'b>)
    (ec : embedding<'c>)
    (ed : embedding<'d>)
    (er : embedding<'r>)
    (nf : 'na -> 'nb -> 'nc -> 'nd -> tac<'nr>)
    (nea : NBET.embedding<'na>)
    (neb : NBET.embedding<'nb>)
    (nec : NBET.embedding<'nc>)
    (ned : NBET.embedding<'nd>)
    (ner : NBET.embedding<'nr>)
    : Cfg.primitive_step

val mktac5
    (nunivs:int)
    (name : string)
    (f : 'a -> 'b -> 'c -> 'd -> 'e -> tac<'r>)
    (ea : embedding<'a>)
    (eb : embedding<'b>)
    (ec : embedding<'c>)
    (ed : embedding<'d>)
    (ee : embedding<'e>)
    (er : embedding<'r>)
    (nf : 'na -> 'nb -> 'nc -> 'nd -> 'ne -> tac<'nr>)
    (nea : NBET.embedding<'na>)
    (neb : NBET.embedding<'nb>)
    (nec : NBET.embedding<'nc>)
    (ned : NBET.embedding<'nd>)
    (nee : NBET.embedding<'ne>)
    (ner : NBET.embedding<'nr>)
    : Cfg.primitive_step

val mktot1
    (nunivs:int)
    (name : string)
    (f : 'a -> 'r)
    (ea : embedding<'a>)
    (er : embedding<'r>)
    (nf : 'na -> 'nr)
    (nea : NBET.embedding<'na>)
    (ner : NBET.embedding<'nr>)
    : Cfg.primitive_step

val mktot1_psc
    (nunivs:int)
    (name : string)
    (f : Cfg.psc -> 'a -> 'r)
    (ea : embedding<'a>)
    (er : embedding<'r>)
    (nf : Cfg.psc -> 'na -> 'nr)
    (nea : NBET.embedding<'na>)
    (ner : NBET.embedding<'nr>)
    : Cfg.primitive_step

val mktot2
    (nunivs:int)
    (name : string)
    (f : 'a -> 'b -> 'r)
    (ea : embedding<'a>)
    (eb:embedding<'b>)
    (er : embedding<'r>)
    (nf : 'na -> 'nb -> 'nr)
    (nea : NBET.embedding<'na>)
    (neb:NBET.embedding<'nb>)
    (ner : NBET.embedding<'nr>)
    : Cfg.primitive_step
