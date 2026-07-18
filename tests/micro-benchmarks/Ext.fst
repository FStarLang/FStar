module Ext

open FStar.Tactics.V2

let check (k:string) (s:string) : Tac unit =
  let r = ext_getv k in
  if r <> s then
    fail ("Expected '" ^ s ^ "' but got '" ^ r ^ "'")

#reset-options "--ext foo=bar"

let _0 = assert True by (check "foo" "bar")

#reset-options ""

let _1 = assert True by (check "foo" "")

let _2 = assert True by (check "foo" "")

#push-options "--ext foo=bar"

let _3 = assert True by (check "foo" "bar"; dump "")

#pop-options

let _4 = assert True by (check "foo" "")

#push-options "--ext foo=bar2"
let _5 = assert True by (check "foo" "bar2")
  #push-options "--ext goo=bar3,foo=bar3"
  let _6 = assert True by (check "goo" "bar3")
  let _7 = assert True by (check "foo" "bar3")
  #pop-options
let _8 = assert True by (check "foo" "bar2")
#pop-options

let _9 = assert True by (check "foo" "")

#set-options "--ext foo=bar4"

let _10 = assert True by (check "foo" "bar4")
