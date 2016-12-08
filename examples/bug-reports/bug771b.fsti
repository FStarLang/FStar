module Bug771b

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

val len: pos
val clen: l:FStar.UInt32.t{FStar.UInt32.v l = len}

val template: idx:nat{idx < len} -> Tot pos
val ctemplate: idx:nat{idx < len} -> Tot (x:FStar.UInt32.t{template idx = FStar.UInt32.v x}) // works
