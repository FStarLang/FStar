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
#light

/// Byte arrays
module FStar.Bytes

open System.IO
open FSharp.Compatibility.OCaml

let b0 n =  (n &&& 0xFF)
let b1 n =  ((n >>> 8) &&& 0xFF)
let b2 n =  ((n >>> 16) &&& 0xFF)
let b3 n =  ((n >>> 24) &&& 0xFF)

let dWw1 n = int32 ((n >>> 32) &&& 0xFFFFFFFFL)
let dWw0 n = int32 (n          &&& 0xFFFFFFFFL)

type array<'a> = 'a[]
type bytes = array<byte>

let length (b:byte[]) = Array.length b
let get (b:byte[]) n = int32 (Array.get b n)
let make (f : _ -> int) n = Array.init n (fun i -> byte (f i))
let zero_create n : byte[] = Array.create n (byte 0)

let really_input (is:TextReader) n =
    let buff = Array.create n 0uy in
     really_input is buff 0 n;
     buff

let maybe_input (is:TextReader) n =
    let buff = Array.create n 0uy in
    let x = input is buff 0 n in
    Array.sub buff 0 x

let output (os:TextWriter) b =
  Pervasives.output os b 0 (Array.length b)

let sub ( b:byte[]) s l = Array.sub b s l
let set bb n (b:int32) = Array.set bb n (byte b)
let blit (a:byte[]) b c d e = Array.blit a b c d e
let string_as_unicode_bytes (s:string) = System.Text.Encoding.Unicode.GetBytes s
let utf8_bytes_as_string (b:bytes) = System.Text.Encoding.UTF8.GetString b
let unicode_bytes_as_string (b:bytes) = System.Text.Encoding.Unicode.GetString b
let compare (b1:bytes) (b2:bytes) = compare b1 b2

let to_intarray (b:bytes) =  Array.init (length b) (get b)
let of_intarray (arr:int[]) = make (fun i -> arr.[i]) (Array.length arr)

let string_as_utf8_bytes (s:string) = System.Text.Encoding.UTF8.GetBytes s

let append (b1: bytes) (b2:bytes) = Array.append b1 b2

let string_as_utf8_bytes_null_terminated (s:string) =
    append (string_as_utf8_bytes s) (of_intarray [| 0x0 |])

let string_as_unicode_bytes_null_terminated (s:string) =
    append (string_as_unicode_bytes s) (of_intarray [| 0x0 |])


module Bytestream =
    type t = { bytes: bytes; mutable pos: int; max: int }

    let of_bytes b n len =
        if n < 0 || (n+len) > length b then failwith "Bytestream.of_bytes";
        { bytes = b; pos = n; max = n+len }

    let read_byte b  =
        if b.pos >= b.max then failwith "Bytestream.of_bytes.read_byte: end of stream";
        let res = get b.bytes b.pos in
        b.pos <- b.pos + 1;
        res

    let read_bytes b n  =
        if b.pos + n > b.max then failwith "Bytestream.read_bytes: end of stream";
        let res = sub b.bytes b.pos n in
        b.pos <- b.pos + n;
        res

    let position b = b.pos
    let clone_and_seek b pos = { bytes=b.bytes; pos=pos; max=b.max }
    let skip b n = b.pos <- b.pos + n

    let read_unicode_bytes_as_string (b:t) n =
        let res = System.Text.Encoding.Unicode.GetString(b.bytes,b.pos,n) in
        b.pos <- b.pos + n; res

    let read_utf8_bytes_as_string (b:t) n =
        let res = System.Text.Encoding.UTF8.GetString(b.bytes,b.pos,n) in
        b.pos <- b.pos + n; res

type bytebuf =
     { mutable bbArray: bytes;
       mutable bbCurrent: int }

module Bytebuf =
    let create sz =
        { bbArray=zero_create sz;
          bbCurrent = 0; }

    let ensure_bytebuf buf new_size =
        let old_buf_size = buf.bbArray.Length in
        if new_size > old_buf_size then begin
          let old = buf.bbArray in
          buf.bbArray <- zero_create (max new_size (old_buf_size * 2));
          blit old 0 buf.bbArray 0 buf.bbCurrent;
        end

    let close buf = sub buf.bbArray 0 buf.bbCurrent

    let emit_int_as_byte buf i =
        let new_size = buf.bbCurrent + 1 in
        ensure_bytebuf buf new_size;
        set buf.bbArray buf.bbCurrent i;
        buf.bbCurrent <- new_size

    let emit_byte buf (b:byte) = emit_int_as_byte buf (int b)
    let emit_bool_as_byte buf (b:bool) = emit_int_as_byte buf (if b then 1 else 0)

    let emit_bytes buf i =
        let n = length i in
        let new_size = buf.bbCurrent + n in
        ensure_bytebuf buf new_size;
        blit i 0 buf.bbArray buf.bbCurrent n;
        buf.bbCurrent <- new_size

    let emit_i32_as_u16 buf n =
        let new_size = buf.bbCurrent + 2 in
        ensure_bytebuf buf new_size;
        set buf.bbArray buf.bbCurrent (b0 n);
        set buf.bbArray (buf.bbCurrent + 1) (b1 n);
        buf.bbCurrent <- new_size

    let emit_u16 buf (x:uint16) = emit_i32_as_u16 buf (int32 x)

    let fixup_i32 bb pos n =
        set bb.bbArray pos (b0 n);
        set bb.bbArray (pos + 1) (b1 n);
        set bb.bbArray (pos + 2) (b2 n);
        set bb.bbArray (pos + 3) (b3 n);

    let emit_i32 buf n =
        let new_size = buf.bbCurrent + 4 in
        ensure_bytebuf buf new_size;
        fixup_i32 buf buf.bbCurrent n;
        buf.bbCurrent <- new_size

    let emit_i64 buf x =
      emit_i32 buf (dWw0 x);
      emit_i32 buf (dWw1 x)

    let emit_intarray_as_bytes buf arr =
        let n = Array.length arr in
        let new_size = buf.bbCurrent + n in
        ensure_bytebuf buf new_size;
        let bbarr = buf.bbArray in
        let bbbase = buf.bbCurrent in
        for i= 0 to n - 1 do set bbarr (bbbase + i) arr.[i] done;
        buf.bbCurrent <- new_size

    let length bb = bb.bbCurrent
    let position bb = bb.bbCurrent

let create i = Bytebuf.create i
let close t = Bytebuf.close t
let emit_int_as_byte t i = Bytebuf.emit_int_as_byte t i
let emit_bytes t b = Bytebuf.emit_bytes t b

let f_encode f (b:bytes) : string =
    Microsoft.FSharp.Core.String.concat "" (Array.map f b)
