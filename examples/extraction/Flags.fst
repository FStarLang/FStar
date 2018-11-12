module Flags

type id = nat

abstract val ideal: id -> Tot bool
let ideal x = false
