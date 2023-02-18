module FStar.Syntax.Visit

open FStar.Syntax.Syntax

val visit_term : (term -> term) -> term -> term

val visit_term_univs : (term -> term) -> (universe -> universe) -> (term -> term)

val visit_sigelt : (term -> term) -> (universe -> universe) -> (sigelt -> sigelt)
