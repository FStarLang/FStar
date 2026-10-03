(*
   Copyright 2025 Microsoft Research

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

module Pulse.Lib.Comment
#lang-pulse

open Pulse.Main
open Pulse.Lib.Core

/// This is the Pulse counterpart of F*'s LowStar.Comment.

/// `comment_gen before body after` extracts to KaRaMeL AST
/// `EComment (before, body', after)` (where `body` extracts
/// to `body'`), and so ultimately extracts to the
/// corresponding C implementation of `body` enclosed with
/// two comments `/* before */` and `/* after */`.
/// `before` and `after` *must be* string literals.
/// However, `comment_gen` is not enough to produce
/// standalone comments, because if `body` is a pure unit
/// expression, then F\*, not KaRaMeL, will erase it at
/// extraction.

val comment_gen (#t: Type) (before: string) (body: t) (after: string) : Pure t
  (requires True)
  (ensures fun res -> res == body)

/// `comment s` extracts to KaRaMeL AST
/// `EStandaloneComment s`, and so ultimately extracts to
/// the standalone C comment `/* s */`.  `s` *must be*
/// a string literal.

fn comment (s: string)
  requires emp
  ensures emp
