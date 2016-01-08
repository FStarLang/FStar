(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst
  --*)
module Bug237b

(* Can only reproduce one of the problems with k_foralle.
   The others only appear in tinyfstar-new.fst for now. *)

type knd =
  | KType : knd
  | KKArr : knd -> knd

val ktsubst_beta : knd -> Tot knd
let ktsubst_beta k = k

val tconsts : unit -> Tot knd
let tconsts () = KKArr KType

type kinding : k:knd -> Type =
| KConst : kinding (tconsts())
| KTApp : #k':knd -> hk1:kinding (KKArr k') -> kinding (ktsubst_beta k')

val k_foralle : u:unit -> Tot (kinding KType)
let k_foralle () =  KTApp (* KType *) KConst
(* Problem: without the annotation and the explicit k' in KTApp
   this causes "Unresolved implicit argument" *)
