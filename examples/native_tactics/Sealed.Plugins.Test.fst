module Sealed.Plugins.Test
open FStar.Sealed
open FStar.Tactics
open Sealed.Plugins

let test0 = assert True by (let res = use_seal (seal 17) in
                         if res <> 18 then fail "Unexpected")

let test1 = assert True by (let res = use_seal (get_seal 16) in
                         if res <> 18 then fail "Unexpected")

let test2 = assert True by (let res = get_seal_tac 17 in
                         if unseal res <> 18 then fail "Unexpected")
