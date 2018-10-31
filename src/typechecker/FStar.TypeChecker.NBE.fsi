#light "off"
module FStar.TypeChecker.NBE
open FStar.All
open FStar.Exn
open FStar
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Errors
open FStar.TypeChecker.Normalize
open FStar.TypeChecker.NBETerm
module Cfg = FStar.TypeChecker.Cfg

val iapp : Cfg.cfg -> t -> args -> t

val normalize_for_unit_test : steps:list<Env.step>
               -> env : Env.env
               -> e:term
               -> term

val normalize   : list<Cfg.primitive_step>
                -> list<Env.step>
                -> Env.env
                -> term
                -> term
