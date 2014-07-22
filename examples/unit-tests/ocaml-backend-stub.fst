module FSharp.Format
type doc 
assume val pretty: int -> doc -> string

module Microsoft.FStar.Backends.OCaml.Syntax
type mllib

module Microsoft.FStar.Backends.OCaml.ASTTrans
open Microsoft.FStar
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Backends.OCaml.Syntax
type error
assume val string_of_error : error -> string
exception OCamlFailure of Range.range * error
assume val mlmod_of_fstars : list<modul> -> mllib

module Microsoft.FStar.Backends.OCaml.Code
open Microsoft.FStar.Backends.OCaml.Syntax

assume val doc_of_mllib: mllib -> FSharp.Format.doc
