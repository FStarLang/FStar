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

(* Section 36.3.  [kbody] is Kuiper's [kernel_desc.f]: the code the launcher
   is to run, written at the launch site and therefore *open* in the launch
   site's locals.  It is the input [hoist] gets. *)
noeq
type kdesc = {
  kname:  string;
  shmems: list desc;
  kbody:  U32.t -> U32.t;
}

(* [inline_for_extraction] is what makes the descriptor reduce at the call
   site.  A rule sees its arguments after the extractor has unfolded what it
   may; without this the argument would arrive as a reference to [kd] and the
   plugin's [die] would fire. *)
inline_for_extraction noextract
let kd (c: U32.t) : kdesc = {
  kname  = "kernel";
  shmems = [ DArr U32.t ({ sz = 40ul; dflt = 0ul }) 10;
             DArr bool  ({ sz = 2ul;  dflt = false }) 2 ];
  (* Captures [c], which is a local of whoever calls [launch]. *)
  kbody  = (fun tid -> U32.add_mod tid c);
}

assume val launch (k:kdesc) (nblk:U32.t) : FStar.All.ML U32.t

(* Section 36.2.  The runtime entry point the rule synthesizes a call to.
   Nothing here calls it -- that is the whole point, and before section 36 it
   was silently deleted and the output did not compile.  The plugin keeps it
   alive with [register_root], so no artificial use is needed. *)
[@@FStar.Attributes.custard_extern "kpr_kcall"]
assume val kcall (f : U32.t -> U32.t -> U32.t) (nblk:U32.t) (cap:U32.t)
  : FStar.All.ML U32.t

let main () : FStar.All.ML U32.t =
  let c = 7ul in
  let r = launch (kd c) 3ul in
  (* [kpr_kcall] is realized in CustardRuleMain.c and returns
     nblk + total_shmem + f 1ul c = 3 + 42 + (1 + 7) = 53. *)
  if r = 53ul then 0ul else 1ul
