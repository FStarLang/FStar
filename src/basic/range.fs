(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
// Adapted from sources of F#
//----------------------------------------------------------------------------
//
// Copyright (c) 2002-2012 Microsoft Corporation.
//
// This source code is subject to terms and conditions of the Apache License, Version 2.0. A
// copy of the license can be found in the License.html file at the root of this distribution.
// By using this source code in any fashion, you are agreeing to be bound
// by the terms of the Apache License, Version 2.0.
//
// You must not remove this notice, or any other, from this software.
//----------------------------------------------------------------------------
// See LICENSE-fsharp.txt at the root of this distribution for terms and conditions
#light "off"
// (c) Microsoft Corporation. All rights reserved
module FStar.Range

open System.Collections.Generic
open FSharp.Compatibility.OCaml
open Printf

let b0 n =  (n          &&& 0xFF)
let b1 n =  ((n >>> 8)  &&& 0xFF)
let b2 n =  ((n >>> 16) &&& 0xFF)
let b3 n =  ((n >>> 24) &&& 0xFF)


let rec pown32 n = if n = 0 then 0  else (pown32 (n-1) ||| (1  <<<  (n-1)))
let rec pown64 n = if n = 0 then 0L else (pown64 (n-1) ||| (1L <<< (n-1)))
let mask32 m n = (pown32 n) <<< m
let mask64 m n = (pown64 n) <<< m


let string_ord (a:string) (b:string) = compare a b
let int_ord (a:int) (b:int) = compare a b
let int32_ord (a:int32) (b:int32) = compare a b

let pair_ord (compare1,compare2) (a1,a2) (aa1,aa2) =
  let res1 = compare1 a1 aa1 in
    if res1 <> 0 then res1 else compare2 a2 aa2

let proj_ord f a1 a2 = compare (f a1)  (f a2)

type file_idx = MkFileIdx of int32
type pos = MkPos of int32
let int32_of_pos (MkPos x) = x

type range = {
    def_range:int64;
    use_range:int64
}

let dummyRange = {
    def_range=0L;
    use_range=0L
}
let set_use_range r2 r = if r.use_range <> 0L then {r2 with use_range=r.use_range} else r2
let range_of_def_range i = {def_range=i; use_range=i}
let col_nbits  = 9
let line_nbits  = 16

let pos_nbits = line_nbits + col_nbits
let _ = assert (pos_nbits <= 32)
let pos_col_mask  = mask32 0         col_nbits
let line_col_mask = mask32 col_nbits line_nbits

let mk_pos l c =
    let l = max 0 l in
    let c = max 0 c in
    MkPos
    (( c &&& pos_col_mask)
    ||| ((l <<< col_nbits) &&& line_col_mask))
let line_of_pos (MkPos p) =  (p lsr col_nbits)
let col_of_pos (MkPos p) =  (p &&& pos_col_mask)
let zeroPos = mk_pos 1 0

let bits_of_pos (MkPos x) :int32 = x
let pos_of_bits (x:int32) : pos = MkPos x
let end_of_line (MkPos x) = MkPos ((x &&& line_col_mask) ||| pos_col_mask)

let file_idx_nbits = 14
let start_line_nbits = line_nbits
let start_col_nbits = col_nbits
let end_line_nbits = line_nbits
let end_col_nbits = col_nbits
let _ = assert (file_idx_nbits + start_line_nbits + start_col_nbits + end_line_nbits + end_col_nbits = 64)

let file_idx_mask   = mask64 0 file_idx_nbits
let start_line_mask = mask64 (file_idx_nbits) start_line_nbits
let start_col_mask  = mask64 (file_idx_nbits + start_line_nbits) start_col_nbits
let end_line_mask   = mask64 (file_idx_nbits + start_line_nbits + start_col_nbits) end_line_nbits
let end_col_mask    = mask64 (file_idx_nbits + start_line_nbits + start_col_nbits + end_line_nbits) end_col_nbits

let mk_file_idx_range (MkFileIdx fidx) (b:pos) (e:pos) =
        int64(fidx)
    ||| (int64(line_of_pos b) <<< file_idx_nbits)
    ||| (int64(col_of_pos b)  <<< (file_idx_nbits + start_line_nbits))
    ||| (int64(line_of_pos e) <<< (file_idx_nbits + start_line_nbits + start_col_nbits))
    ||| (int64(col_of_pos e)  <<< (file_idx_nbits + start_line_nbits + start_col_nbits + end_line_nbits))
    |> range_of_def_range

let file_idx_of_range {def_range=r}   = MkFileIdx <| int32(r &&& file_idx_mask)
let start_line_of_range {def_range=r} = int32((r &&& start_line_mask) >>> file_idx_nbits)
let start_col_of_range {def_range=r}  = int32((r &&& start_col_mask)  >>> (file_idx_nbits + start_line_nbits))
let end_line_of_range {def_range=r}   = int32((r &&& end_line_mask)   >>> (file_idx_nbits + start_line_nbits + start_col_nbits))
let end_col_of_range {def_range=r}    = int32((r &&& end_col_mask)    >>> (file_idx_nbits + start_line_nbits + start_col_nbits + end_line_nbits))


// This is just a standard unique-index table
type FileIndexTable() =
    class
        let indexToFileTable = new ResizeArray<_>(11)
        let fileToIndexTable = new Dictionary<string,int>(11)
        member t.FileToIndex f =
            let mutable res = 0 in
            let ok = fileToIndexTable.TryGetValue(f,&res) in
            if ok then res
            else
                lock fileToIndexTable (fun () ->
                    let mutable res = 0 in
                    let ok = fileToIndexTable.TryGetValue(f,&res) in
                    if ok then res
                    else
                        let n = indexToFileTable.Count in
                        indexToFileTable.Add(f);
                        fileToIndexTable.[f] <- n;
                        n)
        member t.SetFileName (MkFileIdx n) f =
            indexToFileTable.[n] <- f

        member t.IndexToFile n =
            (if n < 0 then failwithf "file_of_file_idx: negative argument: n = %d\n" n);
            (if n >= indexToFileTable.Count then failwithf "file_of_file_idx: invalid argument: n = %d\n" n);
            indexToFileTable.[n]
    end

let maxFileIndex = pown32 file_idx_nbits

// WARNING: Global Mutable State, holding a mapping between integers and filenames
let fileIndexTable = new FileIndexTable()
// Note if we exceed the maximum number of files we'll start to report incorrect file names
let file_idx_of_file f = MkFileIdx <| fileIndexTable.FileToIndex(f) % maxFileIndex
let file_of_file_idx (MkFileIdx n) = fileIndexTable.IndexToFile(n)
let set_file_of_range r f = fileIndexTable.SetFileName (file_idx_of_range r) f

let mk_range f (b:pos) (e:pos) = mk_file_idx_range (file_idx_of_file f) b e
let file_of_range r = file_of_file_idx (file_idx_of_range r)

(* end representation, start derived ops *)

let start_of_range r = mk_pos (start_line_of_range r) (start_col_of_range r)
let end_of_range r = mk_pos (end_line_of_range r) (end_col_of_range r)
let dest_file_idx_range r = file_idx_of_range r,start_of_range r,end_of_range r
let dest_range r = file_of_range r,start_of_range r,end_of_range r
let dest_pos p = line_of_pos p,col_of_pos p
let end_range r = mk_range (file_of_range r) (end_of_range r) (end_of_range r)
let extend_to_end_of_line r = mk_range (file_of_range r)
                                       (start_of_range r)
                                       (end_of_line (end_of_range r))

let pos_ord   p1 p2 = pair_ord (int_ord   ,int_ord) (dest_pos p1) (dest_pos p2)
(* range_ord: not a total order, but enough to sort on ranges *)
let range_ord r1 r2 = pair_ord (string_ord,pos_ord) (file_of_range r1,start_of_range r1) (file_of_range r2,start_of_range r2)

let output_pos (os:out_channel) m = fprintf os "(%d,%d)" (line_of_pos m) (col_of_pos m)
let output_range (os:out_channel) m = fprintf os "%s%a-%a" (file_of_range m) output_pos (start_of_range m) output_pos (end_of_range m)
let boutput_pos os m = bprintf os "(%d,%d)" (line_of_pos m) (col_of_pos m)
let boutput_range os m = bprintf os "%s%a-%a" (file_of_range m) boutput_pos (start_of_range m) boutput_pos (end_of_range m)

let start_range_of_range m =    let f,s,e = dest_file_idx_range m in mk_file_idx_range f s s
let end_range_of_range m =   let f,s,e = dest_file_idx_range m in mk_file_idx_range f e e
let pos_gt p1 p2 =
   (line_of_pos p1 > line_of_pos p2 ||
      (line_of_pos p1 = line_of_pos p2 &&
       col_of_pos p1 > col_of_pos p2))

let pos_eq p1 p2 = (line_of_pos p1 = line_of_pos p2 &&  col_of_pos p1 = col_of_pos p2)
let pos_geq p1 p2 = pos_eq p1 p2 || pos_gt p1 p2

let union_ranges m1 m2 =
    if file_idx_of_range m1 <> file_idx_of_range m2 then m2 else
    let b =
      if pos_geq (start_of_range m1) (start_of_range m2) then (start_of_range m2)
      else (start_of_range m1) in
    let e =
      if pos_geq (end_of_range m1) (end_of_range m2) then (end_of_range m1)
      else (end_of_range m2) in
    mk_file_idx_range (file_idx_of_range m1) b e

let range_contains_range m1 m2 =
    (file_of_range m1) = (file_of_range m2) &&
    pos_geq (start_of_range m2) (start_of_range m1) &&
    pos_geq (end_of_range m1) (end_of_range m2)

let range_contains_pos m1 p =
    pos_geq p (start_of_range m1) &&
    pos_geq (end_of_range m1) p

let range_before_pos m1 p =
    pos_geq p (end_of_range m1)

let range_before_range m1 m2 =
  pos_geq (start_of_range m2) (end_of_range m1)

let rangeN filename line =  mk_range filename (mk_pos line 0) (mk_pos line 80)
let pos0 = mk_pos 1 0
let range0 =  rangeN "unknown" 1
let rangeStartup = rangeN "startup" 1

(* // Store a file_idx in the pos_fname field, so we don't have to look up the  *)
(* // file_idx hash table to map back from pos_fname to a file_idx during lexing  *)
let encode_file_idx (MkFileIdx idx) =
   Bytes.utf8_bytes_as_string (Bytes.of_intarray [|  (idx &&& 0x7F);
                                                     ((idx lsr 7) &&& 0x7F)  |])

let encode_file file = file |> file_idx_of_file |> encode_file_idx

let _ = assert (file_idx_nbits <= 14) (* this encoding is size limited *)
let decode_file_idx (s:string) =
    MkFileIdx
        (if String.length s = 0 then 0 else
         let idx =   (int32 s.[0])
                  ||| ((int32 s.[1]) <<< 7) in
         idx)

(* For Diagnostics *)
let string_of_pos   pos = let line,col = line_of_pos pos,col_of_pos pos in sprintf "%d,%d" line col
let string_of_def_range r   = sprintf "%s(%s-%s)" (file_of_range r) (string_of_pos (start_of_range r)) (string_of_pos (end_of_range r))
let string_of_use_range r   = string_of_def_range {r with def_range=r.use_range}
let string_of_range r       = string_of_def_range r
let file_of_use_range r     = file_of_range {r with def_range=r.use_range}
let start_of_use_range r    = start_of_range {r with def_range=r.use_range}
let end_of_use_range r      = end_of_range {r with def_range=r.use_range}

let compare r1 r2 =
    let fcomp = String.compare (file_of_range r1) (file_of_range r2) in
    if fcomp = 0
    then let start1 = start_of_range r1 in
         let start2 = start_of_range r2 in
         let lcomp = line_of_pos start1 - line_of_pos start2 in
         if lcomp = 0
         then col_of_pos start1 - col_of_pos start2
         else lcomp
    else fcomp

let compare_use_range r1 r2 =
    compare ({r1 with def_range=r1.use_range})
            ({r2 with def_range=r2.use_range})
