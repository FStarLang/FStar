(*
   Copyright 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Brian G. Milnes 
*)

(*
  This module provides polymorphic mappers for OCaml Wrapping for F*.
  See the mli for the abbreviations.
 *)

let wrapIaOz       fn a         = Z.of_int (fn a)
let wrapIaOb       fn a         = fn a
let wrapIzOa       fn i         = fn (Z.to_int i)

(* let localtime    : float -> tm   = wrapIaOwb gmtime to_tm *)
let wrapIaOwb      fn w s       =  w (fn s)

let wrapIazOz      fn a i       = Z.of_int (fn a (Z.to_int i))
let wrapIazbOz     fn a i b     = Z.of_int (fn a (Z.to_int i) b)
let wrapIwaOb      fn w a       = fn (w a)
let wrapIwaOpbwc   fn w1 w2 a   = 
  match fn (w1 a) with
  | (b, c) -> (b,w2 c)
let wrapIazwbOz    fn w a i b   = Z.of_int (fn a (Z.to_int i) (w b))
let wrapIaOpzwb    fn w a       =
  match (fn a) with
  | (i, c) -> (Z.of_int i, w c)
let wrapIzOz       fn i         = Z.of_int (fn (Z.to_int i))
let wrapIazOb      fn a i       = fn a (Z.to_int i)
let wrapIazzOb     fn a i1 i2   = fn a (Z.to_int i1) (Z.to_int i2)
let wrapIabzOc     fn a b i     = fn a b (Z.to_int i)
let wrapIzzOa      fn i1 i2     = fn (Z.to_int i1) (Z.to_int i2)
let wrapIabzzOz    fn a b i1 i2 = (Z.of_int (fn a b (Z.to_int i1) (Z.to_int i2)))
let wrapIazzOpzb   fn a i1 i2   = 
  match (fn a (Z.to_int i1) (Z.to_int i2)) with
  | (i, b) -> (Z.of_int i, b)
let wrapILwazOpzwb fn w1 w2 lc i =
  match (fn (List.map w1 lc) (Z.to_int i)) with
  | (i,b) -> (Z.of_int i, w2 b)
let wrapIabcdeOz   fn a b c d e   = Z.of_int (fn a b c d e)
let wrapIabcdefOz  fn a b c d e f = Z.of_int (fn a b c d e f)
let wrapIaOLwb     fn w a         = List.map w (fn a)
let wrapIaLbOLwc   fn w1 w2 a dl  = List.map w2 (fn a (List.map w1 dl))
let wrapILwaOb     fn w cl        = fn (List.map w cl)
let wrapIaOwA      fn w a         = Array.map w (fn a)
let wrapIAaOb      fn w c         = fn (Array.map w c)
let wrapIazOwb     fn w i         = w (fn (Z.to_int i))
let wrapIwawbwcOd  fn w1 w2 w3 a b c = fn (w1 a) (w2 b) (w3 c) 
let wrapIwaOwb     fn w1 w2 c     = w2 (fn (w1 c))
let wrapIaOpbwc    fn w  a        = 
  match (fn a) with
  | (b,c) -> (b, w c)
let wrapIawbOc     fn w a d        = fn a (w d) 
let wrapIabOwc     fn w a b        = w (fn a b)
let wrapIwabOwc    fn w1 w2 d b    = w2 (fn (w1 d) b)
let wrapIabLwcOLwd fn w1 w2 a b el = List.map w2 (fn a b (List.map w1 el))
let wrapIwabOc     fn w d b        = (fn (w d) b)
let wrapIaOwNSb    fn w a          =
  match (fn a) with
  | None -> None
  | Some e -> Some (w e)

let wrapIabOwNSc    fn w a b       =
  match (fn a b) with
  | None -> None
  | Some e -> Some (w e)

let wrapIabwNScOd  fn w a b co     =
  let co' =
    match co with
    | None   -> None
    | Some z -> Some (w z)
   in
   fn a b co'
    
let wrapIabwcwdeOwf fn w1 w2 w3 a b c1 d1 f =
  w3 (fn a b (w1 c1) (w2 d1) f)

let wrapIabwcwdewfOwg fn w1 w2 w3 w4 a b c1 d1 e f1 =
  w4 (fn a b (w1 c1) (w2 d1) e (w3 f1))

let wrapIabwcwdeOwNSwfwg fn w1 w2 w3 w4 a b c1 d1 e =
  match (fn a b (w1 c1) (w2 d1) e) with
  | (f1,g1) -> ((w3 f1),(w4 g1))

let wrapIabwcOd fn w a b c1 = fn a b (w c1)
