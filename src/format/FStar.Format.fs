(*
   Copyright 2008-2018 Microsoft Research

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
﻿(* -------------------------------------------------------------------- *)
#light "off"

module FStar.Format
open FStar.ST
open FStar.All
open FStar

(* -------------------------------------------------------------------- *)
type doc = | Doc of string



(* -------------------------------------------------------------------- *)
let empty    = Doc ""
let hardline = Doc "\n"

(* -------------------------------------------------------------------- *)
let text (s : string) = Doc s
let num (i : int) = Doc (string_of_int i)

(* -------------------------------------------------------------------- *)
let break_ (i : int   ) = Doc ""

let break0 = break_ 0
let break1 = text " "

(* -------------------------------------------------------------------- *)
let enclose (Doc l) (Doc r) (Doc x) =
    Doc (l^x^r)

let brackets (Doc d ) = enclose (text "[") (text "]") (Doc d)
let cbrackets (Doc d) = enclose (text "{") (text "}") (Doc d)
let parens   (Doc d ) = enclose (text "(") (text ")") (Doc d)

(* -------------------------------------------------------------------- *)
let cat (Doc d1) (Doc d2) = Doc (d1 ^ d2)

(* -------------------------------------------------------------------- *)
let reduce (docs : list<doc>) =
  List.fold_left cat empty docs

(* -------------------------------------------------------------------- *)
let group (Doc d) = Doc (d)

(* -------------------------------------------------------------------- *)
let groups (docs : list<doc>) =
  group (reduce docs)

(* -------------------------------------------------------------------- *)
let combine (Doc sep) (docs : list<doc>) =
  let select (Doc d) = if d = "" then None else Some d in
  let docs = List.choose select docs in
  Doc (String.concat sep docs)

(* -------------------------------------------------------------------- *)
let cat1 (d1 : doc) (d2 : doc) =
    reduce [d1; break1; d2]

(* -------------------------------------------------------------------- *)
let reduce1 (docs : list<doc>) =
    combine break1 docs

(* -------------------------------------------------------------------- *)
let nest (i : int) (Doc d) =
    Doc (d)

(* -------------------------------------------------------------------- *)
let align (docs : list<doc>) =
    let (Doc doc) = combine hardline docs in
    Doc (doc)

(* -------------------------------------------------------------------- *)
let hbox (d : doc) = d (* FIXME *)

(* -------------------------------------------------------------------- *)
let pretty (sz : int) (Doc doc) = doc
