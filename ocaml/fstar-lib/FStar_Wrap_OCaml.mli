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

  Abbreviations 

  wrap 
  f - the function to wrap
  I - the input side.
  O - the output side.
  a,b,c - polymorphic input or output.
  z     - a Z.t argument or output.
  w     - a function on the input side to to get a type, 
           likely an inductive type, with a wrapper named to_X
  w     - a function on the output side to to get a type, 
           likely an inductive type, with a wrapper named of_X
  p     - a pair followed by two output function designations.
  Lw(a,b,c) - a list of something to transform, 
  Aw(a,b,c) - an array of something to transform
  NS - for option
 *)


val wrapIaOz        : ('a -> int)               -> 'a  -> Z.t
val wrapIzOa        : (int -> 'a)               -> Z.t -> 'a
val wrapIzOz        : (int -> int)              -> Z.t -> Z.t
val wrapIaOb        : ('a -> 'b)                -> 'a -> 'b 
val wrapIazOb       : ('a -> int -> 'b)         -> 'a -> Z.t -> 'b
val wrapIazzOb      : ('a -> int -> int -> 'b)  -> 'a -> Z.t -> Z.t -> 'b
val wrapIabzOc       : ('a -> 'b -> int -> 'c)   -> 'a -> 'b  -> Z.t -> 'c
val wrapIzzOa       : (int -> int -> 'a)        -> Z.t -> Z.t -> 'a
val wrapIaOwb       : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c
val wrapIwaOb       : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
val wrapIaOpzwb     : ('a -> (int * 'c)) -> ('c -> 'b) -> 'a -> (Z.t * 'b)
val wrapIwaOpbwc    : ('a -> 'b * 'c) -> ('d -> 'a) -> ('c -> 'e) -> 'd -> ('b * 'e)
val wrapIazwbOz     : ('a -> int -> 'c -> int) -> ('b -> 'c) -> 'a -> Z.t -> 'b -> Z.t
val wrapIazOz       : ('a -> int -> int) -> 'a -> Z.t  -> Z.t
val wrapIabzzOz     : ('a -> 'b -> int -> int -> int) ->
                           'a -> 'b -> Z.t -> Z.t -> Z.t
val wrapIazbOz      : ('a -> int -> 'b -> int) -> 'a -> Z.t -> 'b -> Z.t

val wrapIazzOpzb    : ('a -> int -> int -> (int * 'b)) -> 'a -> Z.t -> Z.t -> (Z.t * 'b) 
val wrapILwazOpzwb  : ('a list -> int -> int * 'b) -> ('c -> 'a) -> ('b -> 'd) -> 
                       'c list -> Z.t -> (Z.t * 'd)
val wrapIaOLwb      : ('a -> 'b list) -> ('b -> 'c) -> 'a -> 'c list
val wrapIaLbOLwc : ('a -> 'b list -> 'c list) ->
                   ('d -> 'b) -> 
                   ('c -> 'e)
                    -> 'a -> 'd list -> 'e list
val wrapIabcdeOz   : ('a -> 'b -> 'c -> 'd -> 'e -> int) ->
                      'a -> 'b -> 'c -> 'd -> 'e -> Z.t
val wrapIabcdefOz   : ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> int) ->
                       'a -> 'b -> 'c -> 'd -> 'e -> 'f -> Z.t
val wrapILwaOb      : ('a list -> 'b) -> ('c -> 'a) -> 'c list -> 'b
val wrapIaOwA       : ('a -> 'b array) -> ('b -> 'c) -> 'a -> 'c array
val wrapIAaOb       : ('a array -> 'b) -> ('c -> 'a) -> 'c array -> 'b
val wrapIazOwb      : (int -> 'b)      -> ('b -> 'c) -> Z.t -> 'c
val wrapIwawbwcOd   : ('a -> 'b -> 'c -> 'd) -> ('e -> 'a) -> ('f -> 'b) -> ('g -> 'c) ->
                       'e -> 'f -> 'g -> 'd
val wrapIwaOwb      : ('a -> 'b) -> ('c -> 'a) -> ('b -> 'd) -> 'c -> 'd
val wrapIaOpbwc     : ('a -> ('b * 'c)) -> ('c -> 'd) -> 'a -> ('b * 'd)
val wrapIawbOc      : ('a -> 'b -> 'c) -> ('d -> 'b) -> 'a -> 'd -> 'c 
val wrapIabOwc      : ('a -> 'b -> 'c) -> ('c -> 'd) -> 'a -> 'b -> 'd
val wrapIwabOwc     : ('a -> 'b -> 'c) -> ('d -> 'a) -> ('c -> 'e) -> 'd -> 'b -> 'e
val wrapIabLwcOLwd  : ('a -> 'b -> 'c list -> 'd list) -> ('e -> 'c) -> ('d -> 'f) -> 
                       'a -> 'b -> 'e list -> 'f list
val wrapIwabOc      : ('a -> 'b -> 'c) -> ('d -> 'a) -> 'd -> 'b -> 'c
val wrapIaOwNSb     : ('a -> 'c option) -> ('c -> 'b ) -> 'a -> 'b option
val wrapIabOwNSc    : ('a -> 'b -> 'c option) -> ('c -> 'd ) -> 'a -> 'b -> 'd option
val wrapIabwNScOd   : ('a -> 'b -> 'e option -> 'd) -> ('c -> 'e) -> 
                       'a -> 'b -> 'c option -> 'd
val wrapIabwcwdeOwf : ('a -> 'b -> 'c -> 'd -> 'f -> 'g) ->
                      ('c1 -> 'c) -> ('d1 -> 'd) -> ('g -> 'g1) ->
                      'a -> 'b -> 'c1 -> 'd1 -> 'f -> 'g1

val wrapIabwcwdewfOwg: ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g1) ->
                       ('c1 -> 'c) -> ('d1 -> 'd) -> ('f1 -> 'f) -> ('g1 -> 'g) -> 
                       'a -> 'b -> 'c1 -> 'd1 -> 'e -> 'f1 -> 'g
(*
let recvfrom : file_descr -> bytes -> Z.t -> Z.t -> msg_flag list -> Z.t * sockaddr = 
     wrapIabwcwdeOwNSwfwg recvfrom Z.to_int Z.to_int Z.of_int of_sockaddr
 *)

val wrapIabwcwdeOwNSwfwg : ('a -> 'b -> 'c -> 'd -> 'e -> ('f1 * 'g1)) ->
                           ('c1 -> 'c) -> ('d1 -> 'd) -> ('f1 -> 'f) -> ('g1 -> 'g) ->
                           'a -> 'b -> 'c1 -> 'd1 -> 'e -> ('f * 'g) 

val wrapIabwcOd          : ('a -> 'b -> 'c -> 'd) -> ('c1 -> 'c) ->
                           'a -> 'b -> 'c1 -> 'd
