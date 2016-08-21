module MtE.Plain

open Platform.Bytes


type plain = AES.plain

val ind_cpa : bool
let ind_cpa = false

assume val repr: p:plain{ind_cpa == false} -> Tot (AES.plain)


assume val mk_plain: r:bytes{ind_cpa == false} -> Tot (plain)

