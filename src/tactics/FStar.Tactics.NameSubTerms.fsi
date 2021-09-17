#light "off"
module FStar.Tactics.NameSubTerms

open FStar.Syntax.Syntax
open FStar.Tactics.Types
open FStar.Tactics.Monad

module Z = FStar.BigInt

type subterm_identifier = term -> tac<option<int>>

type identifier_map = list<(int * binder * term)>

val name_sub_terms: subterm_identifier ->
                    (identifier_map -> (unit -> tac<unit>) -> tac<unit>) ->
                    tac<unit>
