module LowParseWriters.Test
open LowParseWriters.Parsers

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST
module LPI = LowParse.Low.Int
module HS = FStar.HyperStack

module U32 = FStar.UInt32

(* Unit tests *)

let test_read
  (inv: memory_invariant)
  ()
: HST.Stack (result bool)
  (requires (fun h ->
    B.modifies B.loc_none inv.h0 h /\
    HS.get_tip inv.h0 `HS.includes` HS.get_tip h
  ))
  (ensures (fun h _ h' ->
    True
  ))
=
  reify_read _ _ _ _ _ (fun _ -> test_read3 inv (fun () -> false) <: Read bool True (fun _ -> True) inv)

let test_read_if_1
  (inv: memory_invariant)
  ()
: HST.Stack (result bool)
  (requires (fun h ->
    B.modifies B.loc_none inv.h0 h /\
    HS.get_tip inv.h0 `HS.includes` HS.get_tip h
  ))
  (ensures (fun h _ h' ->
    True
  ))
=
  reify_read _ _ _ _ _ (fun _ -> test_read_if inv (fun () -> false) <: Read bool True (fun _ -> True) inv)

inline_for_extraction
noextract
let test_read_from_ptr'
  (inv: memory_invariant)
  (b: ptr parse_u32 inv)
  ()
: Read FStar.UInt32.t True (fun _ -> True) inv
= deref LPI.read_u32 b

let test_read_from_ptr
  (inv: memory_invariant)
  (b: ptr parse_u32 inv)
  ()
: HST.Stack (result U32.t)
  (requires (fun h ->
    B.modifies B.loc_none inv.h0 h /\
    HS.get_tip inv.h0 `HS.includes` HS.get_tip h
  ))
  (ensures (fun h _ h' ->
    True
  ))
=
  reify_read U32.t True (fun _ -> True) (fun _ -> False) inv (test_read_from_ptr' inv b)

inline_for_extraction
noextract
let test_read_if_nontrivial'
  (inv: memory_invariant)
  (b: ptr parse_u32 inv)
  ()
: Read FStar.UInt32.t True (fun _ -> True) inv
= let x = deref LPI.read_u32 b in
  if x = 18ul
  then 42ul
  else 1729ul

let test_read_if_nontrivial
  (inv: memory_invariant)
  (b: ptr parse_u32 inv)
  ()
: HST.Stack (result U32.t)
  (requires (fun h ->
    B.modifies B.loc_none inv.h0 h /\
    HS.get_tip inv.h0 `HS.includes` HS.get_tip h
  ))
  (ensures (fun h _ h' ->
    True
  ))
=
  reify_read U32.t True (fun _ -> True) (fun _ -> False) inv (test_read_if_nontrivial' inv b)

inline_for_extraction
noextract
let test_read_if_really_nontrivial'
  (inv: memory_invariant)
  (b: ptr parse_u32 inv)
  (c: ptr parse_u32 inv)
  ()
: Read FStar.UInt32.t True (fun _ -> True) inv
= let x = deref LPI.read_u32 b in
  if x = 18ul
  then deref LPI.read_u32 c
  else 1729ul

let test_read_if_really_nontrivial
  (inv: memory_invariant)
  (b: ptr parse_u32 inv)
  (c: ptr parse_u32 inv)
  ()
: HST.Stack (result U32.t)
  (requires (fun h ->
    B.modifies B.loc_none inv.h0 h /\
    HS.get_tip inv.h0 `HS.includes` HS.get_tip h
  ))
  (ensures (fun h _ h' ->
    True
  ))
=
  reify_read U32.t True (fun _ -> True) (fun _ -> False) inv (test_read_if_really_nontrivial' inv b c)

inline_for_extraction
noextract
let write_two_ints_1
  (l: memory_invariant)
  (x y: U32.t)
  ()
: Write unit parse_empty (parse_u32 `parse_pair` parse_u32) (fun _ -> True) (fun _ _ (x', y') -> x' == x /\ y' == y) l
= start parse_u32 LPI.write_u32 x;
  append parse_u32 LPI.write_u32 y

let extract_write_two_ints_1
  (l: memory_invariant)
  (x y: U32.t)
=
  extract _ (write_two_ints_1 l x y)

inline_for_extraction
noextract
let write_two_ints_2
  (l: memory_invariant)
  (x y: U32.t)
  ()
: Write unit parse_empty (parse_u32 `parse_pair` parse_u32) (fun _ -> True) (fun _ _ _ -> True) l
= start parse_u32 LPI.write_u32 x;
  append parse_u32 LPI.write_u32 y

let extract_write_two_ints_2
  (l: memory_invariant)
  (x y: U32.t)
=
  extract _ (write_two_ints_2 l x y)

inline_for_extraction
noextract
let write_two_ints_ifthenelse_2_aux
  (l: memory_invariant)
  (x y: U32.t)
  ()
: Write unit parse_empty (parse_u32 `parse_pair` parse_u32) (fun _ -> True) (fun _ _ _ -> True) l
= start parse_u32 LPI.write_u32 x;
  if x `U32.lt` y
  then
    append parse_u32 LPI.write_u32 x
  else
    append parse_u32 LPI.write_u32 y

let extract_write_two_ints_ifthenelse_2_aux
  (l: memory_invariant)
  (x y: U32.t)
=
  extract _ (write_two_ints_ifthenelse_2_aux l x y)

(* Tests from the paper *)

open LowParseWriters.NoHoare.Compat

noeq
type example = { left: U32.t; right: U32.t }

let synth_example (left, right) = { left = left; right = right }
let synth_example_recip (e: example) = (e.left, e.right)

inline_for_extraction
noextract
let parse_example : parser =
  parse_synth
    (parse_u32 `parse_pair` parse_u32)
    synth_example
    synth_example_recip

let valid_rewrite_example : squash (valid_rewrite_prop
  (parse_u32 `parse_pair` parse_u32)
  parse_example
) =
  tvalid_rewrite_of_evalid_rewrite
    (valid_rewrite_parse_synth (parse_u32 `parse_pair` parse_u32) synth_example synth_example_recip ())

inline_for_extraction
noextract
let write_u32
  #inv
  (x: U32.t)
: TWrite unit parse_empty parse_u32 inv
=
  start parse_u32 LPI.write_u32 x

inline_for_extraction
noextract
let write_example
  inv
  (left right: U32.t)
: TWrite unit parse_empty parse_example inv
=
  write_u32 left;
  frame (fun _ -> write_u32 right)

let extract_write_example
  #inv left right
= extract _ (fun _ -> write_example inv left right)

inline_for_extraction
noextract
let write_two_ints
  inv
  (x y: U32.t)
  (max: U32.t { U32.v max > 0 })
: TWrite unit parse_empty (parse_vllist parse_u32 0ul max) inv
= write_vllist_nil parse_u32 max;
  frame (fun _ -> write_u32 x);
  extend_vllist_snoc _ _ _;
  frame (fun _ -> write_u32 y);
  extend_vllist_snoc _ _ _

let extract_write_two_ints
  #inv left right
= extract _ (fun _ -> write_two_ints inv left right 255ul)
