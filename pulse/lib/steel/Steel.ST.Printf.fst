(*
   Copyright 2008-2022 Microsoft Research

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
module Steel.ST.Printf

/// This module provides Steel.ST imperative printing functions for several
/// primitive Low* types, including
///  -- booleans (%b)
///  -- characters (%c)
///  -- strings (%s)
///  -- machine integers
///          (UInt8.t as %uy, UInt16.t as %us, UInt32.t as %ul, and UInt64.t as %uL;
///            Int8.t  as %y,  Int16.t as %i,   Int32.t as %l , and  Int64.t as %L)
///  -- and arrays of these base types formatted
///         as %xN, where N is the format specifier for the array element type
///         e.g., %xuy for buffers of UInt8.t

/// The main function of this module is `printf`
/// There are a few main differences relative to C printf
///   -- The format specifiers are different (see above)
///
///   -- For technical reasons explained below, an extra dummy
///      argument `done` has to be provided at the end for the
///      computation to have any effect.
///
///      E.g., one must write
///           `printf "%b %c" true 'c' done`
///      rather than just
///           `printf "%b %c" true 'c'`
///
///   -- When printing arrays, two arguments must be passed; the
///      length of the array fragment to be formatted and the array
///      itself
///
///   -- When extracted, rather than producing a C `printf` (which
///      does not, e.g., support printing of dynamically sized
///      arrays), our `printf` is specialized to a sequence of calls
///      to primitive printers for each supported type
///
/// Before diving into the technical details of how this module works,
/// you might want to see a sample usage at the very end of this file.

open FStar.Char
open FStar.String
open Steel.ST.Util
module L = FStar.List.Tot
module A = Steel.ST.Array
module U32 = FStar.UInt32

#set-options "--ide_id_info_off"

/// `lmbuffer a l` is
///    - an array of `a`
///    - governed by preorders `r` and `s`
///    - with length `l`
inline_for_extraction
let lmbuffer a l =
    b: A.array a {
      A.length b == U32.v l
    }

/// `StTrivial`: A effect abbreviation for a stateful computation
///  with no precondition, and which does not read or change the state
effect StTrivial (a:Type) =
  STT a emp (fun _ -> emp)

/// `StBuf a b`: A effect abbreviation for a stateful computation
///  that may read `b` but does not change the state
/// 
///  NOTE: I need to provide those primitives operating on
///  Steel.ST.Array.ptr instead of Steel.ST.Array.array, otherwise
///  Karamel will complain about arity mismatch
inline_for_extraction
let stBuf (t:Type) : Type =
  (l: U32.t) ->
  (p: Ghost.erased (lmbuffer t l & perm)) ->
  (x: Ghost.erased (Seq.seq t)) ->
  (b: A.ptr t) ->
  ST unit
    (A.pts_to (fst p) (snd p) x)
    (fun _ -> A.pts_to (fst p) (snd p) x)
    (A.ptr_of (fst p) == b)
    (fun _ -> True)

/// Primitive printers for all the types supported by this module
assume val print_string: string -> StTrivial unit
assume val print_char  : char -> StTrivial unit
assume val print_u8  : UInt8.t -> StTrivial unit
assume val print_u16 : UInt16.t -> StTrivial unit
assume val print_u32 : UInt32.t -> StTrivial unit
assume val print_u64 : UInt64.t -> StTrivial unit
assume val print_i8  : Int8.t -> StTrivial unit
assume val print_i16 : Int16.t -> StTrivial unit
assume val print_i32 : Int32.t -> StTrivial unit
assume val print_i64 : Int64.t -> StTrivial unit
assume val print_bool : bool -> StTrivial unit
assume val print_lmbuffer_bool : stBuf bool
assume val print_lmbuffer_char : stBuf char
assume val print_lmbuffer_string : stBuf string
assume val print_lmbuffer_u8 : stBuf UInt8.t
assume val print_lmbuffer_u16 : stBuf UInt16.t
assume val print_lmbuffer_u32 : stBuf UInt32.t
assume val print_lmbuffer_u64 : stBuf UInt64.t
assume val print_lmbuffer_i8 : stBuf Int8.t
assume val print_lmbuffer_i16 : stBuf Int16.t
assume val print_lmbuffer_i32 : stBuf Int32.t
assume val print_lmbuffer_i64 : stBuf Int64.t


/// An attribute to control reduction
noextract irreducible
let __printf_reduce__ = unit

/// Base types supported so far
noextract
type base_typ =
  | Bool
  | Char
  | String
  | U8
  | U16
  | U32
  | U64
  | I8
  | I16
  | I32
  | I64

/// Argument types are base types and arrays thereof
/// Or polymorphic arguments specified by "%a"
noextract
type arg =
  | Base of base_typ
  | Array of base_typ
  | Any

/// Interpreting a `base_typ` as a type
[@@__printf_reduce__]
noextract
let base_typ_as_type (b:base_typ) : Type0 =
  match b with
  | Bool   -> bool
  | Char   -> char
  | String -> string
  | U8     -> FStar.UInt8.t
  | U16    -> FStar.UInt16.t
  | U32    -> FStar.UInt32.t
  | U64    -> FStar.UInt64.t
  | I8     -> FStar.Int8.t
  | I16    -> FStar.Int16.t
  | I32    -> FStar.Int32.t
  | I64    -> FStar.Int64.t

/// `fragment`: A format string is parsed into a list of fragments of
///  string literals and other arguments that need to be spliced in
///  (interpolated)
noextract
type fragment =
  | Frag of string
  | Interpolate of arg

noextract
let fragments = list fragment

/// `parse_format s`:
///     Parses a list of characters in a format string into a list of fragments
///     Or None, in case the format string is invalid
[@@__printf_reduce__]
noextract inline_for_extraction
let rec parse_format
      (s:list char)
 : Tot (option fragments)
       (decreases (L.length s))
 = let add_dir (d:arg) (ods : option fragments)
     = match ods with
       | None -> None
       | Some ds -> Some (Interpolate d::ds)
   in
   let head_buffer (ods:option fragments)
     = match ods with
       | Some (Interpolate (Base t) :: rest) -> Some (Interpolate (Array t) :: rest)
       | _ -> None
   in
   let cons_frag (c:char) (ods:option fragments)
     = match ods with
       | Some (Frag s::rest) -> Some (Frag (string_of_list (c :: list_of_string s)) :: rest)
       | Some rest -> Some (Frag (string_of_list [c]) :: rest)
       | _ -> None
   in
   match s with
   | [] -> Some []
   | ['%'] -> None

   // %a... polymorphic arguments and preceded by their printers
   | '%' :: 'a' :: s' ->
     add_dir Any (parse_format s')

   // %x... arrays of base types
   | '%' :: 'x' :: s' ->
     head_buffer (parse_format ('%' :: s'))

   // %u ... Unsigned integers
   | '%' :: 'u' :: s' -> begin
     match s' with
     | 'y' :: s'' -> add_dir (Base U8) (parse_format s'')
     | 's' :: s'' -> add_dir (Base U16) (parse_format s'')
     | 'l' :: s'' -> add_dir (Base U32) (parse_format s'')
     | 'L' :: s'' -> add_dir (Base U64) (parse_format s'')
     | _ -> None
     end

   | '%' :: c :: s' -> begin
     match c with
     | '%' -> cons_frag '%' (parse_format s')
     | 'b' -> add_dir (Base Bool)   (parse_format s')
     | 'c' -> add_dir (Base Char)   (parse_format s')
     | 's' -> add_dir (Base String) (parse_format s')
     | 'y' -> add_dir (Base I8)     (parse_format s')
     | 'i' -> add_dir (Base I16)    (parse_format s')
     | 'l' -> add_dir (Base I32)    (parse_format s')
     | 'L' -> add_dir (Base I64)    (parse_format s')
     | _   -> None
     end

   | c :: s' ->
     cons_frag c (parse_format s')


/// `parse_format_string`: a wrapper around `parse_format`
[@@__printf_reduce__]
noextract inline_for_extraction
let parse_format_string
    (s:string)
  : option fragments
  = parse_format (list_of_string s)

/// `lift a` lifts the type `a` to a higher universe
noextract
type lift (a:Type u#a) : Type u#(max a b) =
  | Lift : a -> lift a

/// `done` is a `unit` in universe 1
noextract
let done : lift unit = Lift u#0 u#1 ()

/// `arg_t`: interpreting an argument as a type
///   (in universe 1) since it is polymorphic in the argument type of Any (%a) printers.
/// GM: Somehow, this needs to be a `let rec` (even if it not really recursive)
///     or print_frags fails to verify. I don't know why; the generated
///     VC and its encoding seem identical (modulo hash consing in the
///     latter).
[@@__printf_reduce__]
noextract
let rec arg_t (a:arg) : Type u#1 =
  match a with
  | Base t -> lift (base_typ_as_type t)
  | Array t -> lift ((l:UInt32.t & lmbuffer (base_typ_as_type t) l) & perm & Ghost.erased (Seq.seq (base_typ_as_type t)))
  | Any -> (a:Type0 & (a -> StTrivial unit) & a)

/// `frag_t`: a fragment is either a string literal or a argument to be interpolated
noextract
let frag_t = either string (a:arg & arg_t a)

/// `live_frags h l` is a separation logic predicate asserting ownership of all the arrays in `l`
[@@__printf_reduce__; Steel.Effect.Common.__reduce__]
noextract
let live_frag0 (f: frag_t) : vprop =
  match f with
  | Inl _ -> emp
  | Inr a ->
    (match a with
     | (| Base _, _ |) -> emp
     | (| Any, _ |) -> emp
     | (| Array _, Lift ((| _, b |), p, v) |) -> A.pts_to b p v)

[@@__printf_reduce__]
noextract
let live_frag (f: frag_t) : vprop =
  live_frag0 f

[@@__printf_reduce__]
noextract
let rec live_frags (l:list frag_t) : vprop =
  match l with
  | [] -> emp
  | a :: q -> live_frag a `star` live_frags q

/// `interpret_frags` interprets a list of fragments as a Steel.ST function type
///    Note `l` is the fragments in L-to-R order (i.e., parsing order)
///    `acc` accumulates the fragment values in reverse order
[@@__printf_reduce__]
noextract
let rec interpret_frags (l:fragments) (acc: list frag_t) : Type u#1 =
  match l with
  | [] ->
    // Always a dummy argument at the end
    // Ensures that all cases of this match
    // have the same universe, i.e., u#1
     lift u#0 u#1 unit
    -> STT unit (live_frags acc) (fun _ -> live_frags acc)

  | Interpolate (Base t) :: args ->
    // Base types are simple: we just take one more argument
    x:base_typ_as_type t ->
    interpret_frags args (Inr (| Base t, Lift x |) :: acc)

  | Interpolate (Array t) :: args ->
    // Arrays are implicitly polymorphic in their preorders `r` and `s`
    // which is what forces us to be in universe 1
    // Note, the length `l` is explicit
    l:UInt32.t ->
    #p:perm ->
    #v:Ghost.erased (Seq.seq (base_typ_as_type t)) ->
    b:lmbuffer (base_typ_as_type t) l ->
    interpret_frags args (Inr (| Array t, Lift ((| l, b |), p, v) |)  :: acc)

  | Interpolate Any :: args ->
    #a:Type0 ->
    p:(a -> StTrivial unit) ->
    x:a ->
    interpret_frags args (Inr (| Any, (| a, p, x |) |) :: acc)

  | Frag s :: args ->
    // Literal fragments do not incur an additional argument
    // We just accumulate them and recur
    interpret_frags args (Inl s :: acc)


/// `normal` A normalization marker with very specific steps enabled
noextract unfold
let normal (#a:Type) (x:a) : a =
  FStar.Pervasives.norm
    [iota;
     zeta;
     delta_attr [`%__printf_reduce__; `%BigOps.__reduce__];
     delta_only [`%Base?; `%Array?; `%Some?; `%Some?.v; `%list_of_string];
     primops;
     simplify]
     x

/// `coerce`: A utility to trigger extensional equality of types
noextract
let coerce (x:'a{'a == 'b}) : 'b = x

/// `fragment_printer`: The type of a printer of fragments
noextract
let fragment_printer =
  (acc:list frag_t)
  -> STT unit (live_frags acc) (fun _ -> live_frags acc)

/// `print_frags`: Having accumulated all the pieces of a format
/// string and the arguments to the printed (i.e., the `list frag_t`),
/// this function does the actual work of printing them all using the
/// primitive printers

noextract inline_for_extraction
let print_lmbuffer_gen
  (#t: Type)
  (#fr: frag_t)
  (f: stBuf t)
  (l: U32.t)
  (#tb: Type)
  (b: tb)
  (p: perm)
  (#tv: Type)
  (v: tv)
: ST unit (live_frag fr) (fun _ -> live_frag fr)
    (tb == lmbuffer t l /\
      tv == Ghost.erased (Seq.seq t) /\
      live_frag fr == A.pts_to #t (coerce #_ #(lmbuffer t l) b) p (coerce #_ #(Ghost.erased (Seq.seq t)) v))
    (fun _ -> True)
= [@inline_let] let b' : lmbuffer t l = coerce b in
  let v' : Ghost.erased (Seq.seq t) = coerce v in
  let p' : Ghost.erased (lmbuffer t l & perm) = Ghost.hide (b', p) in
  rewrite (live_frag fr) (A.pts_to #t (fst p') (snd p') v');
  f l _ _ (A.ptr_of b');
  rewrite (A.pts_to _ _ _) (live_frag fr)

noextract inline_for_extraction
let print_frag (hd: frag_t) : STT unit (live_frag hd) (fun _ -> live_frag hd)
=
      (match hd with
       | Inl s -> print_string s
       | Inr (| Base t, Lift value |) ->
         (match t with
           | Bool -> print_bool value
           | Char -> print_char value
           | String -> print_string value
           | U8 ->   print_u8 value
           | U16 ->  print_u16 value
           | U32 ->  print_u32 value
           | U64 ->  print_u64 value
           | I8 ->   print_i8 value
           | I16 ->  print_i16 value
           | I32 ->  print_i32 value
           | I64 ->  print_i64 value)
       | Inr (| Array t, Lift ((| l, value |), p, v ) |) ->
         (match t with
           | Bool -> print_lmbuffer_gen print_lmbuffer_bool l value p v
           | Char -> print_lmbuffer_gen print_lmbuffer_char l value p v
           | String -> print_lmbuffer_gen print_lmbuffer_string l value p v
           | U8 -> print_lmbuffer_gen print_lmbuffer_u8 l value p v
           | U16 -> print_lmbuffer_gen print_lmbuffer_u16 l value p v
           | U32 -> print_lmbuffer_gen print_lmbuffer_u32 l value p v
           | U64 -> print_lmbuffer_gen print_lmbuffer_u64 l value p v
           | I8 -> print_lmbuffer_gen print_lmbuffer_i8 l value p v
           | I16 -> print_lmbuffer_gen print_lmbuffer_i16 l value p v
           | I32 -> print_lmbuffer_gen print_lmbuffer_i32 l value p v
           | I64 -> print_lmbuffer_gen print_lmbuffer_i64 l value p v
           )
       | Inr (| Any, (| _, printer, value |) |) ->
         printer value)

noextract inline_for_extraction
let rec print_frags (acc:list frag_t)
  : STT unit
      (live_frags acc)
      (fun _ -> live_frags acc)
  = match acc with
    | [] -> noop ()
    | hd::tl ->
      rewrite (live_frags acc) (live_frag hd `star` live_frags tl);
      print_frags tl;
      print_frag hd;
      rewrite (live_frag hd `star` live_frags tl) (live_frags acc)

[@@__printf_reduce__]
let no_inst #a (#b:a -> Type) (f: (#x:a -> b x)) : unit -> #x:a -> b x = fun () -> f
[@@__printf_reduce__]
let elim_unit_arrow #t (f:unit -> t) : t = f ()

/// `aux frags acc`: This is the main workhorse which interprets a
/// parsed format string (`frags`) as a variadic, stateful function
[@@__printf_reduce__]
noextract inline_for_extraction
let rec aux (frags:fragments) (acc:list frag_t) (fp: fragment_printer) : interpret_frags frags acc =
  match frags with
  | [] ->
    let f (l:lift u#0 u#1 unit)
      : STT unit (live_frags acc) (fun _ -> live_frags acc)
      = fp acc
    in
    (f <: interpret_frags [] acc)

  | Frag s :: rest ->
    coerce (aux rest (Inl s :: acc) fp)

  | Interpolate (Base t) :: args ->
    let f (x:base_typ_as_type t)
      : interpret_frags args (Inr (| Base t, Lift x |) :: acc)
      = aux args (Inr (| Base t, Lift x |) :: acc) fp
    in
    f

  | Interpolate (Array t) :: rest ->
    let f :
       l:UInt32.t
     -> #p:perm
     -> #v:Ghost.erased (Seq.seq (base_typ_as_type t))
     -> b:lmbuffer (base_typ_as_type t) l
     -> interpret_frags rest (Inr (| Array t, Lift ((| l, b |), p, v) |) :: acc)
     = fun l #p #v b -> aux rest (Inr (| Array t, Lift ((| l, b |), p, v) |) :: acc) fp
    in
    f <: interpret_frags (Interpolate (Array t) :: rest) acc

  | Interpolate Any :: rest ->
    let f :
        unit
      -> #a:Type
      -> p:(a -> StTrivial unit)
      -> x:a
      -> interpret_frags rest (Inr (| Any, (| a, p, x |) |) :: acc)
      = fun () #a p x -> aux rest (Inr (| Any, (| a, p, x |) |) :: acc) fp
    in
    elim_unit_arrow (no_inst (f ()) <: (unit -> interpret_frags (Interpolate Any :: rest) acc))

/// `format_string` : A valid format string is one that can be successfully parsed
[@@__printf_reduce__]
noextract
let format_string = s:string{normal #bool (Some? (parse_format_string s))}

/// `interpret_format_string` parses a string into fragments and then
/// interprets it as a type
[@@__printf_reduce__]
noextract
let interpret_format_string (s:format_string) : Type =
  interpret_frags (Some?.v (parse_format_string s)) []

/// `printf'`: Almost there ... this has a variadic type
///  and calls the actual printers for all its arguments.
///
///  Note, the `normalize_term` in its body is crucial. It's what
///  allows the term to be specialized at extraction time.
noextract inline_for_extraction
let printf' (s:format_string) : interpret_format_string s =
  normalize_term
  (match parse_format_string s with
    | Some frags -> aux frags [] print_frags)

/// `intro_normal_f`: a technical gadget to introduce
/// implicit normalization in the domain and co-domain of a function type
noextract inline_for_extraction
let intro_normal_f (#a:Type) (b: (a -> Type)) (f:(x:a -> b x))
  : (x:(normal a) -> normal (b x))
  = f

/// `printf`: The main function has type
///    `s:normal format_string -> normal (interpret_format_string s)`
/// Note:
///   This is the type F* infers for it and it is best to leave it that way
///   rather then writing it down and asking F* to re-check what it inferred.
///
///   Annotating it results in a needless additional proof obligation to
///   equate types after they are partially reduced, which is pointless.
noextract inline_for_extraction
val printf : s:normal format_string -> normal (interpret_format_string s)
let printf = intro_normal_f #format_string interpret_format_string printf'


/// `skip`: We also provide `skip`, a function that has the same type as printf
///  but normalizes to `()`, i.e., it prints nothing. This is useful for conditional
///  printing in debug code, for instance.
noextract inline_for_extraction
let skip' (s:format_string) : interpret_format_string s =
  normalize_term
  (match parse_format_string s with
    | Some frags -> aux frags [] (fun _ -> noop ()))

noextract inline_for_extraction
val skip : s:normal format_string -> normal (interpret_format_string s)
let skip = intro_normal_f #format_string interpret_format_string skip'


/// `test`: A small test function
/// Running `fstar --codegen OCaml Steel.ST.Printf.fst --extract Steel.ST.Printf`
/// produces the following for the body of this function
///    ```
///            print_string "Hello ";
///            print_bool true;
///            print_string " Steel.ST ";
///            print_u64 m;
///            print_string " Printf ";
///            print_lmbuffer_bool l x () ();
///            print_string " ";
///            print_string "bye"
///   ```
let test_printf (m:UInt64.t) (l:UInt32.t) (x:A.array bool {A.length x == U32.v l}) (v: Ghost.erased (Seq.seq bool))
  : STT unit (A.pts_to x full_perm v) (fun _ -> A.pts_to x full_perm v)
  = printf "Hello %b Steel.ST %uL Printf %xb %s"
              true  //%b boolean
              m     //%uL u64
              l x   //%xb (buffer bool)
              "bye"
              done //dummy universe coercion

let test2_printf (x:(int * int)) (print_pair:(int * int) -> StTrivial unit)
  : STT unit emp (fun _ -> emp)
  = printf "Hello pair %a" print_pair x done

let test3_printf (m:UInt64.t) (l:UInt32.t) (x:A.array bool {A.length x == U32.v l}) (v: Ghost.erased (Seq.seq bool))
  : STT unit (A.pts_to x full_perm v) (fun _ -> A.pts_to x full_perm v)
  = skip "Hello %b Steel.ST %uL Printf %xb %s"
              true  //%b boolean
              m     //%uL u64
              l x   //%xb (buffer bool)
              "bye"
              done //dummy universe coercion
