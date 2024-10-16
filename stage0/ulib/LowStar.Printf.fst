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
module LowStar.Printf

/// This module provides imperative printing functions for several
/// primitive Low* types, including
///  -- booleans (%b)
///  -- characters (%c)
///  -- strings (%s)
///  -- machine integers
///          (UInt8.t as %uy, UInt16.t as %us, UInt32.t as %ul, and UInt64.t as %uL;
///            Int8.t  as %y,  Int16.t as %i,   Int32.t as %l , and  Int64.t as %L)
///  -- and arrays (aka buffers) of these base types formatted
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
open FStar.HyperStack.ST
module L = FStar.List.Tot
module LB = LowStar.Monotonic.Buffer

/// `lmbuffer a r s l` is
///    - a monotonic buffer of `a`
///    - governed by preorders `r` and `s`
///    - with length `l`
let lmbuffer a r s l =
    b:LB.mbuffer a r s{
      LB.len b == l
    }

/// `StTrivial`: A effect abbreviation for a stateful computation
///  with no precondition, and which does not change the state
effect StTrivial (a:Type) =
  Stack a
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> h0==h1)

/// `StBuf a b`: A effect abbreviation for a stateful computation
///  that may read `b` does not change the state
effect StBuf (a:Type) #t #r #s #l (b:lmbuffer t r s l) =
  Stack a
    (requires fun h -> LB.live h b)
    (ensures (fun h0 _ h1 -> h0 == h1))

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
assume val print_lmbuffer_bool (l:_) (#r:_) (#s:_) (b:lmbuffer bool r s l) : StBuf unit b
assume val print_lmbuffer_char (l:_) (#r:_) (#s:_) (b:lmbuffer char r s l) : StBuf unit b
assume val print_lmbuffer_string (l:_) (#r:_) (#s:_) (b:lmbuffer string r s l) : StBuf unit b
assume val print_lmbuffer_u8 (l:_) (#r:_) (#s:_) (b:lmbuffer UInt8.t r s l) : StBuf unit b
assume val print_lmbuffer_u16 (l:_) (#r:_) (#s:_) (b:lmbuffer UInt16.t r s l) : StBuf unit b
assume val print_lmbuffer_u32 (l:_) (#r:_) (#s:_) (b:lmbuffer UInt32.t r s l) : StBuf unit b
assume val print_lmbuffer_u64 (l:_) (#r:_) (#s:_) (b:lmbuffer UInt64.t r s l) : StBuf unit b
assume val print_lmbuffer_i8 (l:_) (#r:_) (#s:_) (b:lmbuffer Int8.t r s l) : StBuf unit b
assume val print_lmbuffer_i16 (l:_) (#r:_) (#s:_) (b:lmbuffer Int16.t r s l) : StBuf unit b
assume val print_lmbuffer_i32 (l:_) (#r:_) (#s:_) (b:lmbuffer Int32.t r s l) : StBuf unit b
assume val print_lmbuffer_i64 (l:_) (#r:_) (#s:_) (b:lmbuffer Int64.t r s l) : StBuf unit b


/// An attribute to control reduction
noextract irreducible
let __reduce__ = unit

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
[@@__reduce__]
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
[@@__reduce__]
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
[@@__reduce__]
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
///   (in universe 1) since it is polymorphic in the preorders of a buffer
/// GM: Somehow, this needs to be a `let rec` (even if it not really recursive)
///     or print_frags fails to verify. I don't know why; the generated
///     VC and its encoding seem identical (modulo hash consing in the
///     latter).
[@@__reduce__]
noextract
let rec arg_t (a:arg) : Type u#1 =
  match a with
  | Base t -> lift (base_typ_as_type t)
  | Array t -> (l:UInt32.t & r:_ & s:_ & lmbuffer (base_typ_as_type t) r s l)
  | Any -> (a:Type0 & (a -> StTrivial unit) & a)

/// `frag_t`: a fragment is either a string literal or a argument to be interpolated
noextract
let frag_t = either string (a:arg & arg_t a)

/// `live_frags h l` is a liveness predicate on all the buffers in `l`
[@@__reduce__]
noextract
let rec live_frags (h:_) (l:list frag_t) : prop =
  match l with
  | [] -> True
  | Inl _ :: rest -> live_frags h rest
  | Inr a :: rest ->
    (match a with
     | (| Base _, _ |) -> live_frags h rest
     | (| Any, _ |) -> live_frags h rest
     | (| Array _, (| _, _, _, b |) |) -> LB.live h b /\ live_frags h rest)


/// `interpret_frags` interprets a list of fragments as a Low* function type
///    Note `l` is the fragments in L-to-R order (i.e., parsing order)
///    `acc` accumulates the fragment values in reverse order
[@@__reduce__]
noextract
let rec interpret_frags (l:fragments) (acc:list frag_t) : Type u#1 =
  match l with
  | [] ->
    // Always a dummy argument at the end
    // Ensures that all cases of this match
    // have the same universe, i.e., u#1
     lift u#0 u#1 unit
    -> Stack unit
      (requires fun h0 -> live_frags h0 acc)
      (ensures fun h0 _ h1 -> h0 == h1)

  | Interpolate (Base t) :: args ->
    // Base types are simple: we just take one more argument
    x:base_typ_as_type t ->
    interpret_frags args (Inr (| Base t, Lift x |) :: acc)

  | Interpolate (Array t) :: args ->
    // Arrays are implicitly polymorphic in their preorders `r` and `s`
    // which is what forces us to be in universe 1
    // Note, the length `l` is explicit
    l:UInt32.t ->
    #r:LB.srel (base_typ_as_type t) ->
    #s:LB.srel (base_typ_as_type t) ->
    b:lmbuffer (base_typ_as_type t) r s l ->
    interpret_frags args (Inr (| Array t, (| l, r, s, b |) |)  :: acc)

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
     delta_attr [`%__reduce__; `%BigOps.__reduce__];
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
  -> Stack unit
    (requires fun h0 -> live_frags h0 acc)
    (ensures fun h0 _ h1 -> h0 == h1)

/// `print_frags`: Having accumulated all the pieces of a format
/// string and the arguments to the printed (i.e., the `list frag_t`),
/// this function does the actual work of printing them all using the
/// primitive printers
noextract inline_for_extraction
let rec print_frags (acc:list frag_t)
  : Stack unit
    (requires fun h0 -> live_frags h0 acc)
    (ensures fun h0 _ h1 -> h0 == h1)
  = match acc with
    | [] -> ()
    | hd::tl ->
      print_frags tl;
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
       | Inr (| Array t, (| l, r, s, value |) |) ->
         (match t with
           | Bool ->  print_lmbuffer_bool l value
           | Char -> print_lmbuffer_char l value
           | String -> print_lmbuffer_string l value
           | U8 ->   print_lmbuffer_u8 l value
           | U16 ->  print_lmbuffer_u16 l value
           | U32 ->  print_lmbuffer_u32 l value
           | U64 ->  print_lmbuffer_u64 l value
           | I8 ->   print_lmbuffer_i8 l value
           | I16 ->  print_lmbuffer_i16 l value
           | I32 ->  print_lmbuffer_i32 l value
           | I64 ->  print_lmbuffer_i64 l value)
       | Inr (| Any, (| _, printer, value |) |) ->
         printer value)

[@@__reduce__]
let no_inst #a (#b:a -> Type) (f: (#x:a -> b x)) : unit -> #x:a -> b x = fun () -> f
[@@__reduce__]
let elim_unit_arrow #t (f:unit -> t) : t = f ()

// let test2 (f: (#a:Type -> a -> a)) : id_t 0 = test f ()
// let coerce #a (#b: (a -> Type)) ($f: (#x:a -> b x)) (t:Type{norm t == (#x:a -> b x)})
/// `aux frags acc`: This is the main workhorse which interprets a
/// parsed format string (`frags`) as a variadic, stateful function
[@@__reduce__]
noextract inline_for_extraction
let rec aux (frags:fragments) (acc:list frag_t) (fp: fragment_printer) : interpret_frags frags acc =
  match frags with
  | [] ->
    let f (l:lift u#0 u#1 unit)
      : Stack unit
        (requires fun h0 -> live_frags h0 acc)
        (ensures fun h0 _ h1 -> h0 == h1)
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
     -> #r:LB.srel (base_typ_as_type t)
     -> #s:LB.srel (base_typ_as_type t)
     -> b:lmbuffer (base_typ_as_type t) r s l
     -> interpret_frags rest (Inr (| Array t, (| l, r, s, b |) |) :: acc)
     = fun l #r #s b -> aux rest (Inr (| Array t, (| l, r, s, b |) |) :: acc) fp
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
[@@__reduce__]
noextract
let format_string = s:string{normal #bool (Some? (parse_format_string s))}

/// `interpret_format_string` parses a string into fragments and then
/// interprets it as a type
[@@__reduce__]
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
    | Some frags -> aux frags [] (fun _ -> ()))

noextract inline_for_extraction
val skip : s:normal format_string -> normal (interpret_format_string s)
let skip = intro_normal_f #format_string interpret_format_string skip'


/// `test`: A small test function
/// Running `fstar --codegen OCaml LowStar.Printf.fst --extract LowStar.Printf`
/// produces the following for the body of this function
///    ```
///            print_string "Hello ";
///            print_bool true;
///            print_string " Low* ";
///            print_u64 m;
///            print_string " Printf ";
///            print_lmbuffer_bool l () () x;
///            print_string " ";
///            print_string "bye"
///   ```
let test (m:UInt64.t) (l:UInt32.t) (#r:_) (#s:_) (x:LB.mbuffer bool r s{LB.len x = l})
  : Stack unit
    (requires (fun h0 -> LB.live h0 x))
    (ensures (fun h0 _ h1 -> h0 == h1))
  = printf "Hello %b Low* %uL Printf %xb %s"
              true  //%b boolean
              m     //%uL u64
              l x   //%xb (buffer bool)
              "bye"
              done //dummy universe coercion

let test2 (x:(int & int)) (print_pair:(int & int) -> StTrivial unit)
  : Stack unit
    (requires (fun h0 -> True))
    (ensures (fun h0 _ h1 -> h0 == h1))
  = printf "Hello pair %a" print_pair x done

let test3 (m:UInt64.t) (l:UInt32.t) (#r:_) (#s:_) (x:LB.mbuffer bool r s{LB.len x = l})
  : Stack unit
    (requires (fun h0 -> LB.live h0 x))
    (ensures (fun h0 _ h1 -> h0 == h1))
  = skip "Hello %b Low* %uL Printf %xb %s"
              true  //%b boolean
              m     //%uL u64
              l x   //%xb (buffer bool)
              "bye"
              done //dummy universe coercion
