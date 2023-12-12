module FStar.TypeChecker.Primops.Base

(* This module defines the type of primitive steps and some helpers. *)

open FStar
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.Syntax.Syntax
open FStar.Class.Monad

module EMB = FStar.Syntax.Embeddings
module NBE = FStar.TypeChecker.NBETerm

let null_psc = { psc_range = Range.dummyRange ; psc_subst = fun () -> [] }
let psc_range psc = psc.psc_range
let psc_subst psc = psc.psc_subst ()

let embed_simple {| EMB.embedding 'a |} (r:Range.range) (x:'a) : term =
    EMB.embed x r None EMB.id_norm_cb

let try_unembed_simple {| EMB.embedding 'a |} (x:term) : option 'a =
    EMB.try_unembed x EMB.id_norm_cb

let solve (#a:Type) {| ev : a |} : Tot a = ev

let as_primitive_step_nbecbs is_strong (l, arity, u_arity, f, f_nbe) : primitive_step = {
    name=l;
    arity=arity;
    univ_arity=u_arity;
    auto_reflect=None;
    strong_reduction_ok=is_strong;
    requires_binder_substitution=false;
    renorm_after=false;
    interpretation=(fun psc cb univs args -> f psc cb univs args);
    interpretation_nbe=(fun cb univs args -> f_nbe cb univs args)
}

let mk_interp1 #a #r
  {| EMB.embedding a |}
  {| EMB.embedding r |}
  (f : a -> r)
  : interp_t =
    fun psc cb us args ->
      match args with
      | [(a, _)] ->
        let! a = try_unembed_simple a in
        return (embed_simple psc.psc_range (f a))
      | _ -> None

let mk_nbe_interp1 #a #r
  {| NBE.embedding a |}
  {| NBE.embedding r |}
  (f : a -> r)
  : nbe_interp_t =
    fun cbs us args ->
      match args with
      | [(a, _)] ->
        let! r = f <$> NBE.unembed solve cbs a in
        return (NBE.embed solve cbs r)
      | _ ->
        None

let mk_interp2 #a #b #r
  {| EMB.embedding a |}
  {| EMB.embedding b |}
  {| EMB.embedding r |}
  (f : a -> b -> r)
  : interp_t =
    fun psc cb us args ->
      match args with
      | [(a, _); (b, _)] ->
        let! r = f <$> try_unembed_simple a <*> try_unembed_simple b in
        return (embed_simple psc.psc_range r)
      | _ -> None

let mk_nbe_interp2 #a #b #r
  {| NBE.embedding a |}
  {| NBE.embedding b |}
  {| NBE.embedding r |}
  (f : a -> b -> r)
  : nbe_interp_t =
    fun cbs us args ->
      match args with
      | [(a, _); (b, _)] ->
        let! r = f <$> NBE.unembed solve cbs a <*> NBE.unembed solve cbs b in
        return (NBE.embed solve cbs r)
      | _ ->
        None

let mk_interp3 #a #b #c #r
  {| EMB.embedding a |}
  {| EMB.embedding b |}
  {| EMB.embedding c |}
  {| EMB.embedding r |}
  (f : a -> b -> c -> r)
  : interp_t =
    fun psc cb us args ->
      match args with
      | [(a, _); (b, _); (c, _)] ->
        let! r = f <$> try_unembed_simple a <*> try_unembed_simple b <*> try_unembed_simple c in
        return (embed_simple psc.psc_range r)
      | _ -> None

let mk_nbe_interp3 #a #b #c #r
  {| NBE.embedding a |}
  {| NBE.embedding b |}
  {| NBE.embedding c |}
  {| NBE.embedding r |}
  (f : a -> b -> c -> r)
  : nbe_interp_t =
    fun cbs us args ->
      match args with
      | [(a, _); (b, _); (c, _)] ->
        let! r = f <$> NBE.unembed solve cbs a <*> NBE.unembed solve cbs b <*> NBE.unembed solve cbs c in
        return (NBE.embed solve cbs r)
      | _ ->
        None

let mk_interp4 #a #b #c #d #r
  {| EMB.embedding a |}
  {| EMB.embedding b |}
  {| EMB.embedding c |}
  {| EMB.embedding d |}
  {| EMB.embedding r |}
  (f : a -> b -> c -> d -> r)
  : interp_t =
    fun psc cb us args ->
      match args with
      | [(a, _); (b, _); (c, _); (d, _)] ->
        let! r = f <$> try_unembed_simple a <*> try_unembed_simple b <*> try_unembed_simple c <*> try_unembed_simple d in
        return (embed_simple psc.psc_range r)
      | _ -> None

let mk_nbe_interp4 #a #b #c #d #r
  {| NBE.embedding a |}
  {| NBE.embedding b |}
  {| NBE.embedding c |}
  {| NBE.embedding d |}
  {| NBE.embedding r |}
  (f : a -> b -> c -> d -> r)
  : nbe_interp_t =
    fun cbs us args ->
      match args with
      | [(a, _); (b, _); (c, _); (d, _)] ->
        let! r = f <$> NBE.unembed solve cbs a <*> NBE.unembed solve cbs b <*> NBE.unembed solve cbs c <*> NBE.unembed solve cbs d in
        return (NBE.embed solve cbs r)
      | _ ->
        None

let mk_interp5 #a #b #c #d #e #r
  {| EMB.embedding a |}
  {| EMB.embedding b |}
  {| EMB.embedding c |}
  {| EMB.embedding d |}
  {| EMB.embedding e |}
  {| EMB.embedding r |}
  (f : a -> b -> c -> d -> e -> r)
  : interp_t =
    fun psc cb us args ->
      match args with
      | [(a, _); (b, _); (c, _); (d, _); (e, _)] ->
        let! r = f <$> try_unembed_simple a <*> try_unembed_simple b <*> try_unembed_simple c <*> try_unembed_simple d <*> try_unembed_simple e in
        return (embed_simple psc.psc_range r)
      | _ -> None

let mk_nbe_interp5 #a #b #c #d #e #r
  {| NBE.embedding a |}
  {| NBE.embedding b |}
  {| NBE.embedding c |}
  {| NBE.embedding d |}
  {| NBE.embedding e |}
  {| NBE.embedding r |}
  (f : a -> b -> c -> d -> e -> r)
  : nbe_interp_t =
    fun cbs us args ->
      match args with
      | [(a, _); (b, _); (c, _); (d, _); (e, _)] ->
        let! r = f <$> NBE.unembed solve cbs a <*> NBE.unembed solve cbs b <*> NBE.unembed solve cbs c <*> NBE.unembed solve cbs d <*> NBE.unembed solve cbs e in
        return (NBE.embed solve cbs r)
      | _ ->
        None

let mk1 #a #r
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding a |}
  {| EMB.embedding r |} {| NBE.embedding r |}
  (f : a -> r)
  : primitive_step =
  let interp : interp_t = mk_interp1 f in
  let nbe_interp : nbe_interp_t = mk_nbe_interp1 f in
  as_primitive_step_nbecbs true (name, 1, u_arity, interp, nbe_interp)

let mk2 #a #b #r
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding a |}
  {| EMB.embedding b |} {| NBE.embedding b |}
  {| EMB.embedding r |} {| NBE.embedding r |}
  (f : a -> b -> r)
  : primitive_step =
  let interp : interp_t = mk_interp2 f in
  let nbe_interp : nbe_interp_t = mk_nbe_interp2 f in
  as_primitive_step_nbecbs true (name, 2, u_arity, interp, nbe_interp)

let mk3 #a #b #c #r
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding a |}
  {| EMB.embedding b |} {| NBE.embedding b |}
  {| EMB.embedding c |} {| NBE.embedding c |}
  {| EMB.embedding r |} {| NBE.embedding r |}
  (f : a -> b -> c -> r)
  : primitive_step =
  let interp : interp_t = mk_interp3 f in
  let nbe_interp : nbe_interp_t = mk_nbe_interp3 f in
  as_primitive_step_nbecbs true (name, 3, u_arity, interp, nbe_interp)

let mk4 #a #b #c #d #r
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding a |}
  {| EMB.embedding b |} {| NBE.embedding b |}
  {| EMB.embedding c |} {| NBE.embedding c |}
  {| EMB.embedding d |} {| NBE.embedding d |}
  {| EMB.embedding r |} {| NBE.embedding r |}
  (f : a -> b -> c -> d -> r)
  : primitive_step =
  let interp : interp_t = mk_interp4 f in
  let nbe_interp : nbe_interp_t = mk_nbe_interp4 f in
  as_primitive_step_nbecbs true (name, 4, u_arity, interp, nbe_interp)

let mk5 #a #b #c #d #e #r
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding a |}
  {| EMB.embedding b |} {| NBE.embedding b |}
  {| EMB.embedding c |} {| NBE.embedding c |}
  {| EMB.embedding d |} {| NBE.embedding d |}
  {| EMB.embedding e |} {| NBE.embedding e |}
  {| EMB.embedding r |} {| NBE.embedding r |}
  (f : a -> b -> c -> d -> e -> r)
  : primitive_step =
  let interp : interp_t = mk_interp5 f in
  let nbe_interp : nbe_interp_t = mk_nbe_interp5 f in
  as_primitive_step_nbecbs true (name, 5, u_arity, interp, nbe_interp)

let mk2' #a #b #r #na #nb #nr
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding na |}
  {| EMB.embedding b |} {| NBE.embedding nb |}
  {| EMB.embedding r |} {| NBE.embedding nr |}
  (f : a -> b -> option r)
  (nbe_f : na -> nb -> option nr)
  : primitive_step =
  let interp : interp_t =
    fun psc cb us args ->
      match args with
      | [(a, _); (b, _)] ->
        let! r = f <$> try_unembed_simple a <*> try_unembed_simple b in
        let! r = r in
        return (embed_simple psc.psc_range r)
      | _ -> None
  in
  let nbe_interp : nbe_interp_t =
    fun cbs us args ->
      match args with
      | [(a, _); (b, _)] ->
        let! r = nbe_f <$> NBE.unembed solve cbs a <*> NBE.unembed solve cbs b in
        let! r = r in
        return (NBE.embed solve cbs r)
      | _ ->
        None
  in
  as_primitive_step_nbecbs true (name, 2, u_arity, interp, nbe_interp)

let mk3' #a #b #c #r #na #nb #nc #nr
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding na |}
  {| EMB.embedding b |} {| NBE.embedding nb |}
  {| EMB.embedding c |} {| NBE.embedding nc |}
  {| EMB.embedding r |} {| NBE.embedding nr |}
  (f : a -> b -> c -> option r)
  (nbe_f : na -> nb -> nc -> option nr)
  : primitive_step =
  let interp : interp_t =
    fun psc cb us args ->
      match args with
      | [(a, _); (b, _); (c, _)] ->
        let! r = f <$> try_unembed_simple a <*> try_unembed_simple b <*> try_unembed_simple c in
        let! r = r in
        return (embed_simple psc.psc_range r)
      | _ -> None
  in
  let nbe_interp : nbe_interp_t =
    fun cbs us args ->
      match args with
      | [(a, _); (b, _); (c, _)] ->
        let! r = nbe_f <$> NBE.unembed solve cbs a <*> NBE.unembed solve cbs b <*> NBE.unembed solve cbs c in
        let! r = r in
        return (NBE.embed solve cbs r)
      | _ ->
        None
  in
  as_primitive_step_nbecbs true (name, 3, u_arity, interp, nbe_interp)
