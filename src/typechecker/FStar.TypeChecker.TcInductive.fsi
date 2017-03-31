#light "off"
module FStar.TypeChecker.TcInductive
open FStar.All
open FStar
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.Util
open FStar.Ident
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Syntax.Util
open FStar.Const
open FStar.TypeChecker.Rel
open FStar.TypeChecker.Common

val check_inductive_well_typedness: env_t -> list<sigelt> -> list<qualifier> -> list<lident> -> option<fsdoc> -> (sigelt * list<sigelt> * list<sigelt>)
val check_positivity: sigelt -> env -> bool
val optimized_haseq_scheme: sigelt -> list<sigelt> -> list<sigelt> -> env_t -> (env_t -> lident -> formula -> list<qualifier> -> Range.range -> option<fsdoc> -> sigelt) -> list<sigelt>
val unoptimized_haseq_scheme: sigelt -> list<sigelt> -> list<sigelt> -> env_t -> (env_t -> lident -> formula -> list<qualifier> -> Range.range -> option<fsdoc> -> sigelt) -> list<sigelt>
