module MiniParseExample3
open MiniParse.Tac.Spec
open MiniParse.Tac.Impl
open FStar.Tactics

let ps = _ by (gen_package Goal (`palette))

#set-options "--print_implicits --print_universes"

let p = _ by (gen_parser_impl Goal)

let s = _ by (gen_serializer_impl Goal)
