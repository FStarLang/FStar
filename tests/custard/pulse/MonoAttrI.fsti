(* Section 92.  The [.fsti] half of section 91's control.  Kuiper's [Inst.spec]
   is a signature in an interface with the definition in the implementation,
   which is the one structural difference between it and [MonoAttr], so the
   question is whether the interface/implementation merge drops a binder
   attribute on its way to the extractor.  It does not: the two
   specializations come out exactly as they do without the interface. *)
module MonoAttrI
#lang-pulse
open Pulse
module SZ = FStar.SizeT

val f ([@@@FStar.Attributes.monomorphize] n: SZ.t)
  : stt SZ.t emp (fun _ -> emp)

val main : unit -> stt FStar.Int32.t emp (fun _ -> emp)
