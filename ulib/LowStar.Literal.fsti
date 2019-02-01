module LowStar.Literal

module B = LowStar.Buffer
module MB = LowStar.Monotonic.Buffer
module IB = LowStar.ImmutableBuffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.Mul

/// This module enables clients to make use of string literals in Low* using two
/// different approaches: either as shorthand syntax for immutable, always-live
/// uint8 buffers, or as actual strings that can be used elsewhere, e.g.
/// LowStar.Printf.

/// .. note::
///
///    This module supersedes ``C.String``.

/// As a reminder, the F* compiler enforces that string literals are UTF-8
/// encoded, and list_of_string returns the corresponding sequence of Unicode
/// scalar values (see https://erratique.ch/software/uucp/doc/Uucp.html#uminimal) for an excellent
/// crash course on Unicode.

/// When compiling with KreMLin, string literals are printed as series of bytes,
/// where non-printable characters are hex-encoded. For instance, if after reading
/// the C standard, the user writes ``let x = "🤮"``, then KreMLin will generate
/// ``const char *x = "\xf0\x9f\xa4\xae"``.

/// String literals as buffers
/// --------------------------

/// Therefore, in order to talk about the interpretation of a string literal as
/// a series of bytes, we need to define the serialization of Unicode scalar values
/// (as returned by ``String.list_of_string``) into bytes. This is a commendable and
/// noble goal, but instead, we choose to restrict ourselves to the ASCII subset of
/// UTF-8, where the byte encoding of a scalar value is the identity.
let is_ascii_char (c: Char.char) = UInt32.lt (Char.u32_of_char c) 0x80ul

let ascii_char = c:Char.char{is_ascii_char c}

let is_ascii_string (s: string) =
  List.Tot.for_all is_ascii_char (String.list_of_string s)

let ascii_string = s:string{is_ascii_string s}

let ascii_chars_of_ascii_string (s: ascii_string): list ascii_char =
  // TODO: missing facilities for reasoning about List.Tot.for_all
  List.Tot.map (fun (x: Char.char) -> admit (); (x <: ascii_char)) (String.list_of_string s)

let u8_of_ascii_char (c: ascii_char): x:UInt8.t{ UInt8.v x = Char.int_of_char c } =
  let x32 = Char.u32_of_char c in
  assert_norm (pow2 24 * pow2 8 = pow2 32);
  Math.Lemmas.modulo_modulo_lemma (UInt32.v x32) (pow2 24) (pow2 8);
  Int.Cast.Full.uint32_to_uint8 x32

/// This means that if a string literal only contains ASCII, then we can easily
/// reflect its contents in terms of uint8's, without having to talk about the utf8
/// encoding.
/// TODO: lemma: S.index (uint8s_of_string s) i = String.index s i
///   (cannot be proven right now because we don't know much about String.index)
///   (is this even what we want? should we do everything in terms of list_of_string?)
let u8s_of_ascii_string (s: ascii_string):
  ss:Seq.seq UInt8.t { Seq.length ss = List.Tot.length (String.list_of_string s) }
=
  let cs = List.Tot.map u8_of_ascii_char (ascii_chars_of_ascii_string s) in
  Seq.Base.init (List.Tot.length cs) (List.Tot.index cs)

/// Consequently, this function becomes in C a simple cast from ``const char *`` to
/// ``char *``, since immutable buffers don't (yet) have the ``const`` attribute in
/// KreMLin. (This is unsavory, and should be fixed later.) This way, a string
/// literal can be seen as an immutable buffer and passed around as such.
/// This function checks at extraction-time that its argument is a literal.
val buffer_of_literal: (s: ascii_string) ->
  ST.Stack (b: IB.ibuffer UInt8.t)
    (requires (fun _ -> // TODO: find a way to meta-program the "is literal" check
      String.length s > 0)) // needed for the implementation
    (ensures (fun h0 b h1 ->
      MB.frameOf b == HS.root /\ // is this really useful?
      MB.recallable b /\
      MB.alloc_post_mem_common b h0 h1 (u8s_of_ascii_string s)))

/// .. note::
///
///    This literal will be zero-terminated, but since we do not require that the
///    string literal be zero-free, the trailing zero will be ignored and unused. This
///    means that we won't be able to use the C standard library functions for string
///    manipulation and will instead have to pass lengths at run-time.

/// Rather than having to write ``assert_norm`` by hand, this convenient wrapper
/// relies on the normalizer to discharge all the relevant proof obligations, and
/// synthesizes the length of the resulting buffer. The pair has no cost: KreMLin
/// guarantees that it will be eliminated.
unfold
let buf_len_of_literal (s: string):
  ST.Stack (IB.ibuffer UInt8.t & UInt32.t)
    (requires (fun _ ->
      normalize (String.length s > 0) /\
      normalize (is_ascii_string s) /\
      normalize (List.Tot.length (String.list_of_string s) < pow2 32)))
    (ensures (fun h0 r h1 ->
      let b, l = r in
      MB.frameOf b == HS.root /\
      MB.recallable b /\
      MB.alloc_post_mem_common b h0 h1 (u8s_of_ascii_string s) /\
      UInt32.v l = IB.length b))
=
  [@inline_let]
  let l = normalize_term (UInt32.uint_to_t (List.Tot.length (String.list_of_string s))) in
  buffer_of_literal s, l

/// String literals as values
/// -------------------------
///
/// The other way to leverage string literals in Low* is to see them as values
/// (they are always live, because they live in the data segment). This enables
/// a variety of use-cases, mostly for printing functions. For these, we
/// currently do not enable any sort of advanced reasoning, except that they must
/// not contain zeroes (since printing routines rely on the trailing zero). Note
/// that we don't reflect the fact that these are zero-terminated like ``C.String``
/// attempted to do.

val const_string: Type0

let zero_free s =
  List.Tot.for_all (fun c -> Char.int_of_char c <> 0) (String.list_of_string s)

val const_string_of_literal: s:string { normalize (zero_free s) } -> const_string
