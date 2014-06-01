module Microsoft.FStar.Backends.OCaml.ASTTrans

open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Backends.OCaml.Syntax

type mlenv = MLEnv of unit

val mlmod_of_mod : mlenv -> list<sigelt> -> mlmodule
val mlsig_of_sig : mlenv -> list<sigelt> -> mlsig
