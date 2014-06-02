module Microsoft.FStar.Backends.OCaml.ASTTrans

open Microsoft.FStar
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Backends.OCaml.Syntax

type error

exception OCamlFailure of Range.range * error

val string_of_error : error -> string

type mlenv = MLEnv of unit

val mlmod_of_mod : mlenv -> list<sigelt> -> mlmodule
val mlsig_of_sig : mlenv -> list<sigelt> -> mlsig

val mlmod_of_fstar  : modul -> mlpath * mlsig * mlmodule
val mlmod_of_fstars : list<modul> -> mllib
