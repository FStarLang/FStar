// This module tests reaching definitions of module `Definition` via
// module `Consumer`.
module IndirectConsumer

open Consumer {fn_renamed}
open Consumer {AnotherNicerName}

include Consumer {fn_renamed as fn_renamed_again}

let _ = AnotherNicerName
let _ = Consumer.BType2

let _ = assert_norm (fn_renamed 12 30 == 42)


