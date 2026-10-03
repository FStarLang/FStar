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
module U64 = FStar.UInt64

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

(* Section 64.  A polymorphic external reached only through a rule.

   [emit] has a rule; [sink] has none and no F* caller, so it is a root the
   plugin pins.  The rule rewrites [emit x] into [sink<ty of x> x], which is
   the shape a launcher rule has whenever the runtime entry point it calls is
   generic in the payload -- and it used to be exactly the shape that did not
   work, because the extractor never sees a call to [sink] and so never
   learns an instantiation for it.

   No [@@custard_extern]: the two instantiations must get *different* C
   names, which is the property being tested, and a fixed target string has
   nowhere to put the type.  (With one they would collide, which is error
   384's job and is tested separately.) *)
assume val sink (#a:Type0) (x:a) : FStar.All.ML unit

assume val emit (#a:Type0) (x:a) : FStar.All.ML unit

(* Section 64.  The same shape again, for the rule that gets it *wrong*: the
   plugin's [bare] rule builds the call to [bare_sink] without putting the
   argument's type on the [EQual].  Declared here rather than beside its use
   in CustardRuleBare.fst because a plugin's [register_root] is resolved in
   every program the plugin is loaded into, and a root naming a module this
   one does not use is error 385.

   Nothing here calls [bare_emit], so in this program [bare_sink] is a
   polymorphic root with no instantiation and no reference, which is dropped
   without complaint -- that being the common case for a plugin whose roots
   outnumber what any single program needs. *)
assume val bare_sink (#a:Type0) (x:a) : FStar.All.ML unit
assume val bare_emit (#a:Type0) (x:a) : FStar.All.ML unit

(* Monomorphic, so an ordinary external, and called from F*: it is here to
   read back what the two [sink]s did, so that the test checks the calls
   arrived rather than merely that the program linked. *)
[@@FStar.Attributes.custard_extern "kpr_sink_total"]
assume val sink_total (u:unit) : FStar.All.ML U32.t

let main () : FStar.All.ML U32.t =
  let c = 7ul in
  let r = launch (kd c) 3ul in
  (* [kpr_kcall] is realized in CustardRuleMain.c and returns
     nblk + total_shmem + f 1ul c = 3 + 42 + (1 + 7) = 53. *)
  (* Two instantiations of one polymorphic external, u32 and u64.  The
     realization adds 3 and 4 respectively, so a single shared symbol -- or
     one instantiation quietly standing in for both -- does not give 7. *)
  emit 3ul;
  emit 4UL;
  if r = 53ul && sink_total () = 7ul then 0ul else 1ul
