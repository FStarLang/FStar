module GlobalRenameNoPrefix
module U32 = FStar.UInt32

[@@FStar.Attributes.rename_let "different_f"]
let f (x:U32.t) : U32.t = U32.add_mod x 2ul

let main () : FStar.All.ML FStar.Int32.t =
  if U32.eq (U32.add_mod (f 1ul) (ColA.f 1ul)) 5ul then 0l else 1l
