module MiniParseExample3
open MiniParse.Tac.Spec
open MiniParse.Tac.Impl
open FStar.Tactics

let ps' : package palette = _ by (gen_package Goal (`palette))

let ps = ps'

#set-options "--print_implicits --print_universes"

let p' : parser_impl (package_parser ps') = _ by (gen_parser_impl Goal)

let p = p'
