(*
   Copyright 2026 Microsoft Research

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
module FStarC.Target

open FStarC.Effect

(* Compilation targets, see doc/ref/targets.md.

   A file [A.B-s2.qemu-c.fst] belongs to module [A.B] and has the tag
   [s2.qemu-c]: a set of atoms separated by '-'.  An atom is a dotted path of
   names matching [a-z][a-z0-9_]*; [s2.qemu] implies [s2].

   Tags are represented by their canonical string: atoms implied by another
   atom of the tag are dropped, and the rest are sorted.  [None] is the empty
   tag of common files. *)
type tag = option string

(* Canonical form of a '-'-separated list of atoms; [None] if it is not
   valid. *)
val parse_tag : string -> ML (option tag)

(* Split a file stem into the module name and its canonical tag.  A stem
   whose suffix is not a valid tag is returned unchanged. *)
val split_target : string -> ML (string & tag)

(* The canonical tag with the atoms of both. *)
val join : tag -> tag -> ML tag

(* [implies ctx t]: every atom of [t] is implied by an atom of [ctx], i.e. a
   file tagged [t] applies in context [ctx]. *)
val implies : tag -> tag -> ML bool

(* [compatible t1 t2]: no atom of [t1] diverges from an atom of [t2] below a
   common root (as [s2.qemu] and [s2.silicon] do), so some context may imply
   both. *)
val compatible : tag -> tag -> ML bool

(* All tags implied by a context, most specific (most atoms) first. *)
val applicable_tags : tag -> ML (list tag)

val show_tag : tag -> string
