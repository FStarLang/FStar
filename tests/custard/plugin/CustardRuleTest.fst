module CustardRuleTest

(* Section 34: the program CustardRulePlugin's rule fires on.

   Everything about [kdesc] is compile-time input to code generation.  It is
   not representable in C -- [DArr] stores a [Type0] that the type of its next
   field mentions, which is what section 30.3 calls an existential package --
   and it is not meant to be: the plugin reads it during extraction and emits
   a number.

   Without the plugin loaded this program does not extract, and that is the
   point: the rule is doing the work, not a coincidence. *)

module U32 = FStar.UInt32

noeq
type sized (t:Type0) = {
  sz:   U32.t;
  dflt: t;
}

noeq
type desc =
  | DArr : ty:Type0 -> s:sized ty -> len:nat -> desc

noeq
type kdesc = {
  kname:  string;
  shmems: list desc;
}

(* [inline_for_extraction] is what makes the descriptor reduce at the call
   site.  A rule sees its arguments after the extractor has unfolded what it
   may; without this the argument would arrive as a reference to [kd] and the
   plugin's [die] would fire. *)
inline_for_extraction noextract
let kd : kdesc = {
  kname  = "kernel";
  shmems = [ DArr U32.t ({ sz = 40ul; dflt = 0ul }) 10;
             DArr bool  ({ sz = 2ul;  dflt = false }) 2 ];
}

assume val launch (k:kdesc) (nblk:U32.t) : FStar.All.ML U32.t

let main () : FStar.All.ML U32.t =
  let r = launch kd 3ul in
  (* 40 + 2 + 3 = 45 *)
  if r = 45ul then 0ul else 1ul
