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

module Microsoft.FStar.Parser.Lexhelp

open Microsoft.FSharp.Compatibility
open Microsoft.FSharp.Compatibility.OCaml.Pervasives
open Microsoft.FSharp.Text.Lexing
open Microsoft.FStar
open Microsoft.FStar.Range
open Microsoft.FStar.Parser
open Microsoft.FStar.Parser.AST
open Microsoft.FStar.Parser.Parse 

let intern_string = 
  let strings = new System.Collections.Generic.Dictionary<string,string>(100) in 
  fun s ->
    let mutable res = "" in
    let ok = strings.TryGetValue(s,&res)  in
    if ok then res 
    else (strings.[s] <- s; s)
      
type lexargs =  
    { getSourceDirectory: (unit -> string); }
      
let resetLexbufPos filename (lexbuf: Microsoft.FSharp.Text.Lexing.LexBuffer<char>) = 
  lexbuf.EndPos <- {lexbuf.EndPos with 
    pos_fname= encode_file filename; 
    pos_cnum=0;
    pos_lnum=1 }

let mkLexargs (srcdir,filename) =
  { getSourceDirectory=srcdir; }

let default_string_finish = (fun endm b s -> STRING (s))

let call_string_finish fin buf endm b = fin endm b (Bytes.Bytebuf.close buf)

let add_string buf x = Bytes.Bytebuf.emit_bytes buf (Bytes.string_as_unicode_bytes x)

let add_int_char buf c = 
  Bytes.Bytebuf.emit_int_as_byte buf (c % 256);
  Bytes.Bytebuf.emit_int_as_byte buf (c / 256)

let add_unichar buf c = add_int_char buf (int c)
let add_byte_char buf (c:char) = add_int_char buf (int32 c % 256)

(* When lexing bytearrays we don't expect to see any unicode stuff. *)
(* Likewise when lexing string constants we shouldn't see any trigraphs > 127 *)
(* So to turn the bytes collected in the string buffer back into a bytearray *)
(* we just take every second byte we stored.  Note all bytes > 127 should have been *)
(* stored using add_int_char *)
let stringbuf_as_bytes buf = 
    let bytes = Bytes.Bytebuf.close buf in 
    Bytes.make (fun i -> Bytes.get bytes (i*2)) (Bytes.length bytes / 2)

(* Sanity check that high bytes are zeros. Further check each low byte <= 127 *)
let stringbuf_is_bytes buf = 
    let bytes = Bytes.Bytebuf.close buf in
    let mutable ok = true in
    for i = 0 to Bytes.length bytes/2-1 do
      if Bytes.get bytes (i*2+1) <> 0 then ok <- false
    done;
    ok

let newline (lexbuf:Microsoft.FSharp.Text.Lexing.LexBuffer<_>) = 
    lexbuf.EndPos <- lexbuf.EndPos.NextLine

let trigraph c1 c2 c3 =
    let digit (c:char) = int c - int '0' in 
    char (digit c1 * 100 + digit c2 * 10 + digit c3)

let digit d = 
    if d >= '0' && d <= '9' then int32 d - int32 '0'   
    else failwith "digit" 

let hexdigit d = 
    if d >= '0' && d <= '9' then digit d 
    else if d >= 'a' && d <= 'f' then int32 d - int32 'a' + 10
    else if d >= 'A' && d <= 'F' then int32 d - int32 'A' + 10
    else failwith "hexdigit" 

let unicodegraph_short s =
    if String.length s <> 4 then failwith "unicodegraph";
    uint16 (hexdigit s.[0] * 4096 + hexdigit s.[1] * 256 + hexdigit s.[2] * 16 + hexdigit s.[3])

let hexgraph_short s =
    if String.length s <> 2 then failwith "hexgraph";
    uint16 (hexdigit s.[0] * 16 + hexdigit s.[1])

let unicodegraph_long s =
    if String.length s <> 8 then failwith "unicodegraph_long";
    let high = hexdigit s.[0] * 4096 + hexdigit s.[1] * 256 + hexdigit s.[2] * 16 + hexdigit s.[3] in 
    let low = hexdigit s.[4] * 4096 + hexdigit s.[5] * 256 + hexdigit s.[6] * 16 + hexdigit s.[7] in 
    if high = 0 then None, uint16 low 
    else 
      (* A surrogate pair - see http://www.unicode.org/unicode/uni2book/ch03.pdf, section 3.7 *)
      Some (uint16 (0xD800 + ((high * 0x10000 + low - 0x10000) / 0x400))),
      uint16 (0xDF30 + ((high * 0x10000 + low - 0x10000) % 0x400))

let escape c = 
    match c with
    | '\\' -> '\\'
    | '\'' -> '\''
    | 'n' -> '\n'
    | 't' -> '\t'
    | 'b' -> '\b'
    | 'r' -> '\r'
    | c -> c

(*------------------------------------------------------------------------
!* Keyword table
 *-----------------------------------------------------------------------*)
    
type compatibilityMode =
    | ALWAYS  (* keyword *)
    | FSHARP  (* keyword, but an identifier under --ml-compatibility mode *)

let keywords = 
  [ FSHARP, "abstract", ABSTRACT;
    ALWAYS, "and"        ,AND;
    ALWAYS, "as"         ,AS;
    ALWAYS, "assert"     ,ASSERT;
    ALWAYS, "asr"        ,INFIX_STAR_STAR_OP "asr";
    ALWAYS, "assume"     ,ASSUME;
    ALWAYS, "base"       ,BASE;
    ALWAYS, "begin"      ,BEGIN;
    ALWAYS, "class"      ,CLASS;
    FSHARP, "default"    ,DEFAULT;
    ALWAYS, "define"     ,DEFINE;
    FSHARP, "delegate"   ,DELEGATE;
    ALWAYS, "do"         ,DO;
    ALWAYS, "done"       ,DONE;
    FSHARP, "downcast"   ,DOWNCAST;
    ALWAYS, "downto"     ,DOWNTO;
    FSHARP, "elif"       ,ELIF;
    ALWAYS, "else"       ,ELSE;
    ALWAYS, "end"        ,END;
    ALWAYS, "exception"  ,EXCEPTION;
    ALWAYS, "exists"     ,EXISTS;
    FSHARP, "extern"     ,EXTERN;
    ALWAYS, "false"      ,FALSE;
    ALWAYS, "finally"    ,FINALLY;
    ALWAYS, "for"        ,FOR;
    ALWAYS, "forall"     ,FORALL;
    ALWAYS, "fun"        ,FUN;
    ALWAYS, "function"   ,FUNCTION;
    ALWAYS, "if"         ,IF;
    ALWAYS, "in"         ,IN;
    ALWAYS, "inherit"    ,INHERIT;
    FSHARP, "inline"     ,INLINE;
    FSHARP, "interface"  ,INTERFACE;
    FSHARP, "internal"   ,INTERNAL;
    ALWAYS, "land"       ,INFIX_STAR_DIV_MOD_OP "land";
    ALWAYS, "lazy"       ,LAZY;
    ALWAYS, "let"        ,LET(false);
    ALWAYS, "lor"        ,INFIX_STAR_DIV_MOD_OP "lor";
    ALWAYS, "logic"      ,LOGIC;
    ALWAYS, "lsl"        ,INFIX_STAR_STAR_OP "lsl";
    ALWAYS, "lsr"        ,INFIX_STAR_STAR_OP "lsr";
    ALWAYS, "lxor"       ,INFIX_STAR_DIV_MOD_OP "lxor";
    ALWAYS, "match"      ,MATCH;
    FSHARP, "member"     ,MEMBER;
    ALWAYS, "method"     ,METHOD;
    ALWAYS, "mod"        ,INFIX_STAR_DIV_MOD_OP "mod";
    ALWAYS, "module"     ,MODULE;
  (*   FSHARP, "namespace"  ,NAMESPACE; *)
    ALWAYS, "new"        ,NEW;
    FSHARP, "null"       ,NULL;
    ALWAYS, "of"         ,OF;
    ALWAYS, "open"       ,OPEN;
    ALWAYS, "or"         ,OR;
    FSHARP, "override"   ,OVERRIDE;
    ALWAYS, "private"    ,PRIVATE;  
    ALWAYS, "prop"       ,PROP;  
    FSHARP, "public"     ,PUBLIC;
    ALWAYS, "query"      ,QUERY;
    ALWAYS, "rec"        ,REC;
    FSHARP, "reference"  ,REFERENCE;
    FSHARP, "return"     ,YIELD(false);
    ALWAYS, "sig"        ,SIG;
    FSHARP, "static"     ,STATIC;
    ALWAYS, "struct"     ,STRUCT;
    ALWAYS, "then"       ,THEN;
    ALWAYS, "to"         ,TO;
    ALWAYS, "true"       ,TRUE;
    ALWAYS, "try"        ,TRY;
    ALWAYS, "type"       ,TYPE;
    FSHARP, "upcast"     ,UPCAST;
    FSHARP, "use"        ,LET(true);
    ALWAYS, "val"        ,VAL;
    ALWAYS, "virtual"    ,VIRTUAL;
    FSHARP, "void"       ,VOID;
    ALWAYS, "when"       ,WHEN;
    ALWAYS, "while"      ,WHILE;
    ALWAYS, "with"       ,WITH;
    FSHARP, "yield"      ,YIELD(true);
    ALWAYS, "_"          ,UNDERSCORE;
    FSHARP, "__token_constraint",CONSTRAINT;
  ]
(*------- reserved keywords which are ml-compatibility ids *) 
  @ List.map (fun s -> (FSHARP,s,RESERVED)) 
    [ "atomic"; "break"; 
      "checked"; "component"; "const"; "constraint"; "constructor"; "continue"; 
      "eager"; 
      "fixed"; "functor"; "global"; 
      "include";  (* "instance"; *)
      "mixin"; 
      (* "object";  *)
      "parallel"; "params";  "process"; "protected"; "pure"; (* "pattern"; *)
      "sealed"; "trait";  "tailcall";
      "volatile"; ]

let stringKeywords = List.map (fun (_, w, _) -> w) keywords

(*------------------------------------------------------------------------
!* Keywords
 *-----------------------------------------------------------------------*)

let unreserve_words = 
    List.choose (function (mode,keyword,_) -> if mode = FSHARP then Some keyword else None) keywords

let kwd_table = 
    let tab = Hashtbl.create 1000 in
    List.iter (fun (mode,keyword,token) -> Hashtbl.add tab keyword token) keywords;
    tab
let kwd s = Hashtbl.find kwd_table s

(* REVIEW: get rid of this element of global state *)
let permitFsharpKeywords = ref true

exception ReservedKeyword of string * range
exception IndentationProblem of string * range

let kwd_or_id args (lexbuf:Microsoft.FSharp.Text.Lexing.LexBuffer<char> (*UnicodeLexing.Lexbuf*)) s =
  if not !permitFsharpKeywords && List.mem s unreserve_words then
    IDENT (intern_string(s))
  else if Hashtbl.mem kwd_table s then 
    let v = kwd s in 
    if v = RESERVED then
      begin
        let m = GetLexerRange lexbuf in 
        warning(ReservedKeyword("The keyword '"^s^"' is reserved for future use by F#.",m));
          (* This will give a proper syntax error at the right location for true F# files. *)
        IDENT (intern_string(s))
      end
    else v
  else 
    match s with 
    | "__SOURCE_DIRECTORY__" -> 
       STRING (Bytes.string_as_unicode_bytes (args.getSourceDirectory()))
    | "__SOURCE_FILE__" -> 
       STRING (Bytes.string_as_unicode_bytes (file_of_file_idx (decode_file_idx lexbuf.StartPos.FileName)))
    | "__LINE__" -> 
       STRING (Bytes.string_as_unicode_bytes (string lexbuf.StartPos.Line))
    | _ -> 
       IDENT (intern_string(s))

