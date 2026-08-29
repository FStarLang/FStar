(*
   Copyright 2008-2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.Custard.Extract

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Errors.Msg
open FStarC.Class.Show
open FStarC.Class.Setlike
open FStarC.Syntax.Syntax
open FStarC.Syntax.Print
open FStarC.Const
open FStarC.Custard.Mono

open FStarC.Custard.Syntax

module BU     = FStarC.Format
module Dep    = FStarC.Parser.Dep
module E      = FStarC.Errors
module Effects = FStarC.Custard.Effects
module Free   = FStarC.Syntax.Free
module FlatSet = FStarC.FlatSet
module Ident  = FStarC.Ident
module Loader = FStarC.Custard.Loader
module Prof   = FStarC.Custard.Prof
module Real   = FStarC.Real
module Mono   = FStarC.Custard.Mono
module Builtins = FStarC.Custard.Builtins
module GenSym = FStarC.GenSym
module N      = FStarC.TypeChecker.Normalize
module Options = FStarC.Options
module PC     = FStarC.Parser.Const
module ExtractAs = FStarC.Parser.Const.ExtractAs
module S      = FStarC.Syntax.Syntax
module SMap   = FStarC.SMap
module Unit   = FStarC.Custard.Unit
module Visit  = FStarC.Syntax.Visit
module SS     = FStarC.Syntax.Subst
module TcEnv  = FStarC.TypeChecker.Env
module U      = FStarC.Syntax.Util
module UF     = FStarC.Syntax.Unionfind
module TcUtil = FStarC.TypeChecker.Util
module Range = FStarC.Range
module R      = FStarC.Reflection.V2.Builtins
module RD     = FStarC.Reflection.V2.Data
module RC     = FStarC.Reflection.V2.Constants
module RE     = FStarC.Reflection.V2.Embeddings
module EMB    = FStarC.Syntax.Embeddings


(* -------------------------------------------------------------------- *)
(* Specialization keys                                                  *)
(* -------------------------------------------------------------------- *)

(* Section 3.7: two call sites share a specialization when their [Mono]
   arguments have the same canonical form.  This step list is deliberately much
   smaller than the one used on a definition's body: the key only has to make
   equal things syntactically equal.

   [Primops] is what makes [loop_unrolling (n-1)] fold to a literal, without
   which every recursive call would produce a fresh key.  Delta-unfolding is
   what turns a named type-class instance into a concrete dictionary value, so
   that [ReduceProjections] can collapse method projections in the body. *)
(* [FStar.Custard.dyn] is a call-site opt-out of specialization (section
   3.2c): it marks an argument that is to be passed at run time rather than
   specialized on.  For that to work the marker has to survive the reduction
   that computes a specialization key -- an ordinary identity function would
   simply be unfolded away, leaving the bare variable it was wrapping and the
   rejection that variable triggers.  So [dyn] carries an attribute that
   Custard refuses to unfold, in every reduction it performs.  The marker is
   erased later, by the builtin rule for [dyn] in [Custard.Builtins]. *)
let no_specialize_lid : Ident.lident = PC.p2l ["FStar"; "Custard"; "no_specialize"]

let norm_steps_base : list TcEnv.step = [
  TcEnv.DontUnfoldAttr [no_specialize_lid];
  TcEnv.Weak;
  TcEnv.AllowUnboundUniverses;
  TcEnv.EraseUniverses;
  TcEnv.Beta;
  TcEnv.Iota;
  TcEnv.Unascribe;
  TcEnv.Unmeta;
  TcEnv.UnfoldUntil delta_constant;
]

let key_norm_steps : list TcEnv.step = TcEnv.Primops :: norm_steps_base

(* [Weak] is what makes this reduction terminate, and it is not optional.

   A key is reduced to a normal form, and strong normalization of a recursive
   function does not terminate.  Reducing *under* a lambda means reducing
   inside the branches of a [match] that cannot fire, because its scrutinee is
   a bound variable; each branch contains recursive calls, which unfold into
   more unreducible matches, without bound.  [FStarC.Class.Binders.hasNames_term]
   is the case that found this: the key term is the single fvar
   [hasNames_term], the instance [{ freeNames = Free.names }], and normalizing
   it strongly unfolded [free_names_and_uvars] hundreds of times and was still
   going after 500 million steps and fifty minutes.  Nothing about that
   dictionary is unusual -- any instance whose method is recursive does it, and
   the compiler is full of them.

   [Weak] stops at a lambda, so a method body is a key as written.  The cost is
   that two arguments differing only *inside* a lambda no longer share a
   specialization even when reduction would identify them.  That duplicates
   code; it does not miscompile.  It is the same trade-off, for the same
   reason, that [subst_norm_steps] makes below, and the reduction that would
   avoid it is the one that does not terminate. *)

(* The same reduction, stopped as soon as the value's head constructor is
   visible.  This -- not [key_norm_steps] -- is what gets substituted into the
   body; see section 3.3.

   The two have to differ.  [key_norm_steps] is a specialization's *identity*,
   so it must reduce everything: two arguments that mean the same thing have
   to produce the same key, or the same code is emitted twice.  But that same
   reduction, applied to the term the body will contain, evaluates the whole
   program at extraction time.  On a bundled parser combinator it inlines the
   entire grammar into its root -- [Primops] folds the offset arithmetic
   [4 + 8], which forces the sub-parsers to reduce to concrete [Some (n, _)]
   values, which lets [Iota] collapse every [match] -- and all the sharing is
   gone.  Weak head normal form stops at the record constructor, leaving the
   fields' bodies as written, so a sub-combinator stays a *call* and gets a
   specialization (and a name) of its own. *)
(* [SafePrimops] rather than [Primops], for the reason spelled out at
   {!custard_norm_steps}: this is the reduct that gets *substituted into the
   body*, so it is code.  The key keeps [Primops], because a key is only ever
   printed. *)
let subst_norm_steps : list TcEnv.step =
  TcEnv.SafePrimops :: TcEnv.Weak :: TcEnv.HNF :: norm_steps_base

(* -------------------------------------------------------------------- *)
(* The key printer (section 12.3)                                       *)
(* -------------------------------------------------------------------- *)

(* A specialization key is an *identity*: two call sites share a
   specialization exactly when their keys are equal as strings.  So the
   function that turns a term into a key has one job, and it is not
   readability -- it is to be injective up to the equivalence we intend, and
   to depend on nothing but the term.

   [show] is neither.  It resugars unless [--ugly] (Print.fst:166), and it
   prints an [fv] by its last identifier alone unless [--print_real_names]
   (Syntax.fst:629), so [A.inst] and [B.inst] are one key and the whole
   interning table changes shape with a printing option.  Delta-unfolding in
   [key_norm_steps] hides this most of the time -- two dictionaries usually
   reduce to record literals that differ -- but it stops hiding it the moment
   a [Mono] argument keeps an [fv] that does not unfold: an [assume val], a
   [[@@custard_extern]], an abstract type constructor.  The failure is a
   silent miscompilation, two call sites sharing code built for one of them.

   Hence this printer.  It is deliberately dumb and total:

     - every [fv] and effect name is fully qualified;
     - universes are erased, matching [EraseUniverses] in [key_norm_steps];
     - bound variables print as their de Bruijn index and binders print only
       their sort, so the key is alpha-canonical for free -- terms are
       locally nameless and we never open one, which is also why [ppname] and
       [bv.index], both of which are run-local gensym noise, never appear;
     - ranges and attributes, which are not semantic, are dropped.

   It is also what section 12.2 stores in a unit interface, so it has to mean
   the same thing in the next process as in this one. *)

let key_of_const (c:sconst) : ML string =
  match c with
  | Const_effect        -> "Effect"
  | Const_unit          -> "()"
  | Const_bool b        -> if b then "true" else "false"
  | Const_real r        -> Real.to_string r ^ "R"
  | Const_char c        -> "'" ^ show (FStarC.Util.int_of_char c) ^ "'"
  | Const_string (s, _) -> "\"" ^ s ^ "\""
  (* The *base* an integer was written in is not part of its meaning --
     [FStarC.Const.eq_const] ignores it -- so it must not reach a key, or
     [f 16] and [f 0x10] would specialize twice and produce two identical
     definitions under two names.  [show] on the value is the canonical
     spelling.

     The width and signedness, by contrast, *are* part of the constant: [0uy]
     and [0ul] are different values of different types, and both print as
     "0". *)
  | Const_int (v, _)    -> show v
  | Const_machine_int (v, _, sg, w) ->
    show v ^
    (match sg with Unsigned -> "u" | Signed -> "s") ^
    (match w with Int8 -> "8" | Int16 -> "16" | Int32 -> "32"
                | Int64 -> "64" | Sizet -> "sz")
  (* A range is a position, so it cannot appear in a key: two identical calls
     on different lines would specialize twice, and the key would change
     whenever anything above it moved. *)
  | Const_range _       -> "<range>"
  | Const_range_of      -> "range_of"
  | Const_set_range_of  -> "set_range_of"
  | Const_reify lopt    ->
    "reify" ^ (match lopt with None -> "" | Some l -> "<" ^ Ident.string_of_lid l ^ ">")
  | Const_reflect l     -> "reflect<" ^ Ident.string_of_lid l ^ ">"

(* Round 31 measured this as the third of three per-term-size costs, and the
   only one in Custard's own code: a key is built once per [request] and a key
   for a deep grammar derivation is megabytes long, so left-nested [^] copies
   the prefix again at every node -- quadratic in the rendered size, in
   [memcpy].

   So the renderer appends into an accumulator instead of returning strings.
   The pieces are pushed in reverse and concatenated once, which makes the
   whole rendering linear.  Nothing about *what* is rendered has changed, and
   it must not: §12.3's keys are compared as strings, and a key that rendered
   differently would silently split or merge specializations. *)
private let rec key_into (acc:ref (list string)) (t:S.term) : ML unit =
  let emit (s:string) : ML unit = acc := s :: !acc in
  match (SS.compress t).n with
  | Tm_bvar bv          -> emit ("@" ^ show bv.index)
  (* A [Tm_name] is bound outside the term, so its identity is the gensym
     index and there is nothing canonical to print.  A key containing one is
     not portable across runs; see section 12.3. *)
  | Tm_name bv          -> emit ("%" ^ Ident.string_of_id bv.ppname ^ "#" ^ show bv.index)
  | Tm_fvar fv          -> emit (Ident.string_of_lid (S.lid_of_fv fv))
  | Tm_uinst (t, _)     -> key_into acc t
  | Tm_constant c       -> emit (key_of_const c)
  | Tm_type _           -> emit "Type"
  | Tm_abs {b; body}    ->
    emit "(fun "; key_of_binder acc b; emit " -> "; key_into acc body; emit ")"
  | Tm_arrow {b; comp}  ->
    emit "("; key_of_binder acc b; emit " -> "; key_of_comp acc comp; emit ")"
  | Tm_refine {b; phi}  ->
    emit "({"; key_into acc b.sort; emit "|"; key_into acc phi; emit "})"
  | Tm_app {hd; arg}    ->
    emit "("; key_into acc hd; emit " "; key_of_arg acc arg; emit ")"
  | Tm_match {scrutinee; brs} ->
    emit "(match "; key_into acc scrutinee; emit " with";
    brs |> List.iter (key_of_branch acc); emit ")"
  (* [Unascribe] and [Unmeta] are in [key_norm_steps], so these are only
     reached on a term the normalizer declined to touch; either way neither
     node changes what the term means. *)
  | Tm_ascribed {tm}    -> key_into acc tm
  | Tm_meta {tm}        -> key_into acc tm
  | Tm_let {lbs = (r, lbs); body} ->
    emit ("(let" ^ (if r then " rec" else ""));
    lbs |> List.iteri (fun i lb ->
      if i > 0 then emit " and ";
      key_of_lb acc lb);
    emit " in "; key_into acc body; emit ")"
  | Tm_uvar (u, _)      -> emit ("?" ^ show (UF.uvar_id u.ctx_uvar_head))
  | Tm_quoted (t, _)    -> emit "(quote "; key_into acc t; emit ")"
  | Tm_lazy _ ->
    (* One step only: [unlazy] on something that does not unfold gives back
       what it was handed, and we must not loop. *)
    (match (SS.compress (U.unlazy t)).n with
     | Tm_lazy _ -> emit "<lazy>"
     | _ -> key_into acc (U.unlazy t))
  | Tm_unknown          -> emit "_"
  | Tm_delayed _        -> emit "<delayed>"  (* unreachable: compressed above *)

(* The qualifier is dropped: whether an argument was written [#a] or [a] does
   not change the value, and the two must not key differently.  Attributes are
   dropped for the same reason. *)
and key_of_binder (acc:ref (list string)) (b:S.binder) : ML unit =
  key_into acc b.binder_bv.sort

and key_of_arg (acc:ref (list string)) (a:S.arg) : ML unit = key_into acc (fst a)

and key_of_comp (acc:ref (list string)) (c:S.comp) : ML unit =
  match c.n with
  | Total t  -> key_into acc t
  | GTotal t -> acc := "GTot " :: !acc; key_into acc t
  | Comp ct  ->
    acc := (Ident.string_of_lid ct.effect_name ^ " ") :: !acc;
    key_into acc ct.result_typ;
    acc := " " :: !acc; key_into acc ct.comp_pre;
    acc := " " :: !acc; key_into acc ct.comp_post

and key_of_branch (acc:ref (list string)) (br:S.branch) : ML unit =
  let (p, w, e) = br in
  acc := " | " :: !acc;
  key_of_pat acc p;
  (match w with None -> () | Some w -> (acc := " when " :: !acc; key_into acc w));
  acc := " -> " :: !acc;
  key_into acc e

and key_of_pat (acc:ref (list string)) (p:S.pat) : ML unit =
  match p.v with
  | Pat_constant c   -> acc := key_of_const c :: !acc
  (* Pattern variables are positional, so their names carry no information. *)
  | Pat_var _        -> acc := "_" :: !acc
  | Pat_dot_term _   -> acc := "." :: !acc
  | Pat_cons (fv, _, ps) ->
    acc := ("(" ^ Ident.string_of_lid (S.lid_of_fv fv)) :: !acc;
    ps |> List.iter (fun (p, _) -> (acc := " " :: !acc; key_of_pat acc p));
    acc := ")" :: !acc

and key_of_lb (acc:ref (list string)) (lb:S.letbinding) : ML unit =
  acc := (match lb.lbname with
          | Inl _ -> "@"                 (* recursive group binders are positional *)
          | Inr fv -> Ident.string_of_lid (S.lid_of_fv fv)) :: !acc;
  acc := " : " :: !acc; key_into acc lb.lbtyp;
  acc := " = " :: !acc; key_into acc lb.lbdef

let key_of_term (t:S.term) : ML string =
  let acc : ref (list string) = mk_ref [] in
  key_into acc t;
  String.concat "" (List.rev !acc)

let string_of_key (k:spec_key) : ML string =
  Prof.timed "key" (fun () ->
  let acc : ref (list string) = mk_ref [] in
  acc := Ident.string_of_lid k.sk_lid :: !acc;
  if k.sk_holes <> 0 then acc := ("/" ^ show k.sk_holes) :: !acc;
  k.sk_args |> List.iter (fun (i, t) ->
    acc := ("#" ^ show i ^ "=") :: !acc;
    key_into acc t);
  String.concat "" (List.rev !acc))

(* -------------------------------------------------------------------- *)
(* State                                                                *)
(* -------------------------------------------------------------------- *)

type state = {
  deps:    Dep.deps;
  env:     ref TcEnv.env;
  (* Specialization key -> the IR name it was assigned.  Filled in *before*
     the definition is translated, so that a recursive occurrence finds it and
     stops. *)
  names:   SMap.t name;
  emitted: SMap.t decl;
  (* Emission order, reversed: a definition is appended once its body has been
     translated, so uses come after definitions. *)
  order:   ref (list string);
  (* lid -> its binder classification (section 3.1), computed once. *)
  classes: SMap.t (list bclass);
  (* Which of a declaration's binders are erased, unit-shaped or type
     parameters: a property of its F* type, asked at every *call site* of it
     and answered by normalizing every binder's sort.  Keyed by a tag and the
     lid; see {!binder_flags} and section 12.14. *)
  bflags:  SMap.t (list bool);
  (* lid -> how many specializations of it we have created so far. *)
  counts:  SMap.t int;
  (* The mangled names handed out already, so that two specializations whose
     hints coincide still get distinct names. *)
  suffixes: SMap.t bool;
  fuel:    ref int;
  (* The chain of requests that led to what we are currently working on,
     innermost first.  Only used to make diagnostics debuggable (section
     3.6). *)
  chain:   ref (list string);
  (* Local [let rec]s are lambda-lifted to declarations of their own; this maps
     a recursive binder (by its IR variable name) to the lifted declaration's
     name, its type arguments, the captured variables its call sites have to
     supply, and its full arrow type.  See [lift_letrec]. *)
  lifted:  SMap.t (name & list cty & list binder & cty & list S.bv);
  (* The declaration currently being extracted, which is what a lifted local
     function is named after. *)
  cur:     ref name;
  (* The definition of every pure local [let] the extractor is currently
     inside, keyed by its bound variable's index.  Section 3.2b consults it so
     that a [Mono] argument named by a local variable is judged by the value
     the variable stands for.  Binder indices are unique after opening, so a
     stale entry can never be found by a different variable and nothing is
     ever removed. *)
  letdefs: SMap.t S.term;
  (* Names bound to an *effectful* right-hand side, which [letdefs]
     deliberately does not record.  Kept only so that section 3.2's rejection
     can tell a runtime parameter apart from a computation's result: the two
     need entirely different advice. *)
  effletdefs: SMap.t unit;
  (* The binders of the definition currently being extracted.  Section 3.2's
     advice is to write [@@monomorphize] on the offending name "in the
     enclosing definition", which is only possible if the name *is* one of
     those binders.  Section 30.4: in the CDDL bundles it is a record field
     instead, and the reader who follows the advice writes an attribute that
     nothing reads.  Indices are unique after opening, so entries accumulate
     harmlessly and are never removed. *)
  defbinders: SMap.t unit;
  (* The type a local [let] was given, keyed by its bound variable's index.
     In a [--lax] run the typechecker leaves the sort of a binder it invented
     itself (the [uu__] of an ANF-style [let]) unknown, so the *occurrence* of
     such a variable extracts to [any] even though the right-hand side has a
     perfectly good type.  That loses information the backends need -- whether
     a value is a [ref] rather than a one-element run, for one -- so an
     occurrence whose own sort says nothing falls back to this. *)
  lettys: SMap.t cty;
  (* Every type abbreviation emitted so far, keyed by its target name.  An
     abbreviation is a name for a type, not a type of its own, so a use of it
     in *function position* has to be seen through: [exported_id_set] is an
     arrow, and an application of a value of that type has the arrow's result
     type, not [any].  Section 5.5. *)
  abbrevs: SMap.t (list string & cty);
  (* What the already-compiled units this run links against export, indexed by
     specialization key (section 12.4).  This is the whole of separate
     compilation on the extraction side: a request whose key is already in here
     is answered by a reference rather than by a translation. *)
  links:   Unit.links;
  (* The imported declarations this run has referred to, reversed.  They are
     not emitted, but the later passes need to see them: the layout analysis
     has to adopt an imported type's verdict, and the backends have to know
     which namespace to qualify a name with. *)
  imports: ref (list (decl & option type_info));
  (* The lids named as roots, by string.  A projector or a discriminator is
     normally substituted at its uses and never emitted (section 21), which is
     right for anything inside the program but wrong for one that was asked
     for by name: an entry point exists precisely because something outside
     the extracted program calls it, and that caller has nothing to inline
     into.  See [pulse/src/custard-entrypoints.txt]. *)
  roots:   SMap.t bool;
}

let init (deps:Dep.deps) (env:TcEnv.env) : ML state = {
  deps    = deps;
  env     = mk_ref env;
  names   = SMap.create 100;
  emitted = SMap.create 100;
  order   = mk_ref [];
  classes = SMap.create 100;
  bflags = SMap.create 100;
  counts  = SMap.create 100;
  suffixes = SMap.create 100;
  fuel    = mk_ref (Options.custard_fuel ());
  chain   = mk_ref [];
  lifted  = SMap.create 20;
  cur     = mk_ref ({ ns = []; id = "custard"; spec = None });
  letdefs = SMap.create 100;
  effletdefs = SMap.create 100;
  defbinders = SMap.create 100;
  lettys  = SMap.create 100;
  abbrevs = SMap.create 100;
  links   = Unit.load_links (Options.custard_links ());
  imports = mk_ref [];
  roots   = SMap.create 20;
}

(* Just enough to fire the redexes that substituting a local function creates,
   and nothing else: this runs on the enclosing body, which is code, so any
   further reduction here would be reduction of the emitted program. *)
let local_inline_steps : list TcEnv.step = [
  TcEnv.AllowUnboundUniverses;
  TcEnv.Beta;
]

let custard_norm_steps : list TcEnv.step = [
  TcEnv.DontUnfoldAttr [no_specialize_lid];
  TcEnv.AllowUnboundUniverses;
  TcEnv.EraseUniverses;
  TcEnv.Beta;
  TcEnv.Iota;
  (* No [Zeta].  Custard never wants a fixpoint reduced: a local [let rec] is
     lambda-lifted to a top-level definition (section 5.10) and a top-level
     one is reached through a specialization request, so unfolding one here
     only duplicates code -- and, applied to an open argument, need not
     terminate.  [FStarC.SMTEncoding.Term.termToSmt] is the case that found
     this: its inner [let rec aux'] opens with [let aux = aux (depth + 1) in],
     a partial application of the recursive knot, and each unfolding produces
     another one.  Together with [PureSubtermsWithinComputations] below,
     omitting [Zeta] selects the normalizer's "no fixpoint reduction" branch,
     which normalizes under a [let rec] and puts it back rather than tying the
     knot.  Note that beta, iota and zeta are on by default in [Cfg], so zeta
     has to be switched off with [Exclude], not merely left out. *)
  TcEnv.Exclude TcEnv.Zeta;
  (* [SafePrimops], not [Primops].  A primitive step is free to answer with a
     *value* that has no term representation: [FStarC.TypeChecker.Primops.Docs]
     implements [FStar.Pprint.arbitrary_string] natively, so
     [arbitrary_string "hi"] reduces to an embedded [document] -- a [Tm_lazy]
     whose payload is an OCaml object.  That is exactly what the normalizer is
     for when a tactic runs, and exactly wrong when the term is code to be
     emitted: there is nothing to emit for it (that module's own FIXME says as
     much about the steps it has already had to disable).  Those few steps are
     marked [unrepresentable_result] and [SafePrimops] skips them; everything
     else still folds, which is what makes an integer literal a literal and
     what lets a loop over a constant bound unroll.  A specialization *key*
     asks for plain [Primops] ([key_norm_steps]), because there the reduct is
     only ever printed. *)
  TcEnv.SafePrimops;
  TcEnv.Eager_unfolding;
  TcEnv.Inlining;
  TcEnv.PureSubtermsWithinComputations;
  TcEnv.Unascribe;
  TcEnv.Unmeta;
  TcEnv.ForExtraction;
  (* [tcmethod] inlines a class's method accessor down to the record
     projection, which [ReduceProjections] then collapses against the concrete
     dictionary: no method projector survives into the IR (section 3.4). *)
  TcEnv.UnfoldAttr [PC.tcnorm_attr; PC.tcmethod_lid];
  TcEnv.ReduceProjections;
]

let tcenv (st:state) : ML TcEnv.env = !st.env

(* -------------------------------------------------------------------- *)
(* Diagnostics                                                          *)
(* -------------------------------------------------------------------- *)

(* Every Custard error is reported with the chain of specialization requests
   that reached it: without it a failure deep inside a specialized library
   function is impossible to act on. *)
let chain_display_limit : int = 10

let request_chain (st:state) : ML (list Pprint.document) =
  match !st.chain with
  | [] -> []
  | c ->
    let n = List.length c in
    let shown, elided =
      if n <= chain_display_limit
      then c, []
      else List.splitAt chain_display_limit c |> fst,
           [text ("... and " ^ show (n - chain_display_limit) ^ " more.")]
    in
    [text "Reached through:"] @
    (shown |> List.map (fun s -> Pprint.doc_of_string ("  " ^ s))) @
    elided

let custard_error (#a:Type) (st:state) (code:E.error_code) (msg:list Pprint.document) : ML a =
  E.raise_error0 code (msg @ request_chain st)

(* Every normalization Custard performs runs under a step budget.

   Custard reduces terms nobody wrote for it: a specialization key has to be a
   normal form, so [key_norm_steps] is the most aggressive reduction in the
   pipeline, and it is applied to whatever value happens to reach a [Mono]
   binder.  Reduction does not have to terminate -- with [zeta] on, which is
   the default, a recursive definition can be unfolded without bound -- and
   there is no way to know in advance that a given argument is safe.

   The failure mode this replaces is the worst kind: not a wrong answer or a
   rejection, but a compiler that never finishes and never says why.  With the
   budget the same program gets a fatal error naming the definition being
   specialized and the chain that reached it, which is the information needed
   to either fix the definition or raise the limit. *)
(* A key can be megabytes long; the first few hundred characters are what a
   reader needs and the rest is noise in a terminal. *)
let truncate_msg (s:string) : ML string =
  if String.length s <= 600 then s
  else String.substring s 0 600 ^ " ... (" ^ show (String.length s) ^ " chars)"

(* The extractor works on *open* terms almost everywhere: a definition body is
   entered with its binders opened, and every lambda, [let] and match branch
   underneath opens more.  The environment it carries around, on the other
   hand, is the top-level one, in which none of those variables exist.

   That is usually harmless, because normalization does not look a bound
   variable up -- it is already a [Tm_bvar]-free name carrying its own sort.
   It stops being harmless the moment normalization has to *typecheck*
   something: reifying an effectful application computes the universe of the
   result type, and if that type is one of the opened binders the lookup fails
   with "Variable 'a not found", from inside the normalizer, with no useful
   position.  ([Tac 'b] in [FStar.Tactics.Util.map] and [Tac 'a] in
   [FStar.Tactics.V2.Derived.trytac] are the two smallest examples.)

   Rather than thread a precise environment through every function -- which
   means an extra parameter on the whole of [expr_of_term] and [ty_of_typ],
   and a new way to get it wrong at each new recursive call -- we recover the
   binders from the term itself.  A name that occurs free in what we are about
   to normalize is exactly a name the normalizer may need, it carries its own
   sort, and pushing it can shadow nothing, since names are unique after
   opening.  The sorts may mention each other, so they go in creation order:
   indices are handed out by a global counter, so ascending index is a
   topological order on any set of names that arose from opening one term. *)
let with_free_names (env:TcEnv.env) (bvs:list bv) : ML TcEnv.env =
  Prof.timed "env" (fun () ->
    TcEnv.push_bvs env
      (List.sortWith (fun (a:bv) (b:bv) -> a.index - b.index) bvs))

let env_for_term (env:TcEnv.env) (t:term) : ML TcEnv.env =
  with_free_names env (elems (Free.names t))

let env_for_comp (env:TcEnv.env) (c:comp) : ML TcEnv.env =
  with_free_names env (elems (Free.names_comp c))

let norm_bounded_in (st:state) (env:TcEnv.env) (what:string)
                    (steps:list TcEnv.step) (t:term) : ML term =
  try let env = env_for_term env t in
      Prof.timed "norm" (fun () ->
        N.with_budget (Options.custard_norm_budget ())
                      (fun () -> N.normalize steps env t))
  with
  | N.Budget_exceeded ->
    custard_error st E.Error_CustardFuelExhausted [
      text ("Custard exceeded --custard_norm_budget (" ^
            show (Options.custard_norm_budget ()) ^
            " reduction steps) while normalizing " ^ what ^ ".");
      text "Reduction of an argument to a monomorphized binder need not terminate: a recursive definition reachable from it may unfold without bound. Either avoid specializing on this value, or raise --custard_norm_budget if the term is merely large.";
      (* The term *as written* is what identifies the culprit.  The normalized
         one does not exist -- that is the failure -- and the request chain
         names the callee but not which of its arguments was written how. *)
      text ("The term being normalized, before reduction, was: " ^
            truncate_msg (FStarC.Syntax.Print.term_to_string' (TcEnv.dsenv (tcenv st)) t))
    ]

let norm_bounded (st:state) (what:string) (steps:list TcEnv.step) (t:term) : ML term =
  norm_bounded_in st (tcenv st) what steps t

(* Section 30.6.  The same, for a reduction that is an *optimization*: it
   recovers precision a fallback would otherwise lose, so exhausting the
   budget must degrade to that fallback rather than fail the compile.  The
   projection of section 30.5 needs [Zeta] to see through a recursive builder,
   and [Zeta] is exactly what makes a budget overrun possible; without this,
   turning it on would convert programs that compile today -- with an [any] in
   a place they never used -- into a hard error 365. *)
let norm_optional_in (env:TcEnv.env) (steps:list TcEnv.step) (t:term)
  : ML (option term) =
  try Some (Prof.timed "norm" (fun () ->
              N.with_budget (Options.custard_norm_budget ())
                            (fun () -> N.normalize steps (env_for_term env t) t)))
  with
  | N.Budget_exceeded -> None

let norm_optional (st:state) (steps:list TcEnv.step) (t:term) : ML (option term) =
  norm_optional_in (tcenv st) steps t

(* Section 30.8.  A match that takes apart a constructor storing a type --
   [Mkbundle : (b_impl_type: Type0) -> (b_dflt: b_impl_type) -> bundle] -- has
   to fire at specialization time, because afterwards the field is a variable
   and a variable standing for a type is what error 364 reports.

   These are the names whose unfolding would let such a match fire: the head of
   every scrutinee that is taken apart by one.  Collected rather than assumed,
   because the alternative -- unfolding everything, or turning [Zeta] on
   globally -- is what {!custard_norm_steps} spends a paragraph explaining
   Custard must not do.  Here the set is small, known, and derived from the
   very shape that needs it. *)
let type_matched_heads (env:TcEnv.env) (t:term) : ML (list Ident.lident) =
  let acc : ref (list Ident.lident) = mk_ref [] in
  let _ = Visit.visit_term false (fun t ->
    (match (SS.compress t).n with
     | Tm_match {scrutinee; brs} ->
       let binds_type =
         brs |> List.existsb (fun (p, _, _) ->
                  match p.v with
                  | Pat_cons (fv, _, _) -> Mono.ctor_stores_type env (S.lid_of_fv fv)
                  | _ -> false) in
       if binds_type
       then (let h, _ = U.head_and_args_full scrutinee in
             match (U.un_uinst (SS.compress h)).n with
             | Tm_fvar fv -> acc := S.lid_of_fv fv :: !acc
             | _ -> ())
     | _ -> ());
    t) t in
  !acc

(* -------------------------------------------------------------------- *)
(* Loading                                                              *)
(* -------------------------------------------------------------------- *)

(* A definition may live in a module the driver never loaded; pull it in.  This
   is the on-demand part of section 4.1. *)
let ensure_lid_available (st:state) (l:Ident.lident) : ML unit =
  let m = Ident.nsstr l in
  if m <> "" && not (Loader.module_is_loaded st.deps (tcenv st) m) then
    st.env := Prof.timed "load" (fun () -> Loader.ensure_loaded st.deps (tcenv st) m)

(* Section 30.11.  Which of a definition's names have to be known at extraction
   time because something marked [@@custard_compile_time] is applied to them.

   §30.10 makes the evaluation opt-in but says nothing about how the argument
   comes to be a constant, and in EverParse it does not, by itself.
   [CDDL.Pulse.AST.Literal.impl_literal] destructures a literal and hands the
   string it finds to the marked function; the string is a pattern variable,
   so the application depends on a runtime name and error 372 fires.  The
   binder it came from has to be [Mono], and asking the author to write that
   is the annotation treadmill rule 4b exists to end.

   Two sources, both over-approximations, and deliberately so -- a demand that
   is met by a binder which did not need it costs a specialization, while one
   that is missed costs the extraction:

   - the free names of a marked application are needed, since they are exactly
     what stops it from reducing;
   - if a marked application occurs inside a *branch*, the scrutinee's names
     are needed too, because knowing the argument means first knowing which
     branch is taken.  This is also why the branch is not opened: a pattern
     variable is a de Bruijn index there, so it has no name to collect, and the
     scrutinee is the thing that can be specialized on anyway.

   Rule 5's fixpoint in [Mono.classify] then carries the demand to any binder
   these depend on, and §3.1 rule 5 at the call sites carries it up the chain,
   which is what keeps this from being one annotation per level. *)
let compile_time_demanded (st:state) (t:term) : ML (list int) =
  let is_marked_app (t:term) : ML bool =
    let hd, _ = U.head_and_args_full t in
    match (U.un_uinst (SS.compress hd)).n with
    | Tm_fvar fv ->
      let l = S.lid_of_fv fv in
      ensure_lid_available st l;
      TcEnv.fv_has_attr (tcenv st) fv PC.custard_compile_time_attr
    | _ -> false in
  let contains_marked (t:term) : ML bool =
    let found = mk_ref false in
    let _ = Visit.visit_term false (fun t ->
      (if not !found && is_marked_app t then found := true); t) t in
    !found in
  (* The answer is a list of binder *positions*, not of names: the caller
     classifies the binders of the declaration's arrow, which are opened
     separately from the lambda's and so are different [bv]s for the same
     parameter.  Opening the lambda here is also what turns its binders into
     [Tm_name]s that [Free.names] can see at all. *)
  let bs, body, _ = U.abs_formals t in
  let acc : ref (list bv) = mk_ref [] in
  let add (t:term) : ML unit = acc := FlatSet.elems (Free.names t) @ !acc in
  let _ = Visit.visit_term false (fun t ->
    (match (SS.compress t).n with
     | Tm_app _ -> if is_marked_app t then add t
     | Tm_match {scrutinee; brs} ->
       if brs |> List.existsb (fun (_, _, e) -> contains_marked e)
       then add scrutinee
     | _ -> ());
    t) body in
  let names = !acc in
  bs |> List.mapi (fun i (b:S.binder) ->
          if names |> List.existsb (fun v -> bv_eq v b.binder_bv)
          then [i] else [])
     |> List.flatten

(* Every consultation of a declaration's type goes through here.  Looking a
   lid up in an environment that has not loaded its module yet does not fail
   loudly: it returns [None], and every caller's fallback -- do not erase, do
   not filter, assume the worst -- is silently wrong rather than merely
   conservative.  A type constructor whose kind cannot be read keeps its
   dictionary arguments as if they were type arguments, which is how
   [writer<list _, monoid_list _, unit>] came about.  Whether the module is
   loaded depends only on what has been extracted *before*, so the same
   definition would come out differently depending on the order requests
   happened to arrive in. *)
let lookup_lid_typ (st:state) (l:Ident.lident) : ML (option ((universes & typ) & Range.range)) =
  ensure_lid_available st l;
  Prof.timed "lookup" (fun () -> TcEnv.try_lookup_lid (tcenv st) l)

(* Section 8.3.  A [FStar.Stubs.*] declaration is not a definition of
   anything: it is ulib restating, for metaprograms, something the compiler
   already declares under its [FStarC.*] name.  The two declarations mangle to
   one OCaml name, so compiling both would put two definitions of the same
   type in the same file -- and worse, the stub's phrasing drags in the
   realizations it is written against, which are themselves abbreviations back
   into the module the stub belongs to, so the file ends up depending on
   itself.  That is not a shape OCaml can compile at all.

   So a request for a stub is answered with the compiler's own declaration
   whenever there is one to answer it with.  When there is not -- the stub is
   of something whose only implementation is hand-written OCaml, which is what
   [FStar.Stubs.Tactics.V2.Builtins] and [FStar.Stubs.Reflection.Types] are --
   the rewritten module has no checked file, the stub stands, and
   {!Builtins.realized_modules} claims it in the usual way.

   The ML pipeline does not have to decide this: it extracts ulib with
   [--extract -FStar.Stubs] and the compiler separately, so the question never
   comes up in one program. *)
let unstub_lid (st:state) (l:Ident.lident) : ML Ident.lident =
  let ns = List.map Ident.string_of_id (Ident.ns_of_lid l) in
  if not (Builtins.is_stub_module ns) then l
  else
    (* A stub whose counterpart moved module is resolved from the table
       rather than from the namespace rewrite.  The rest of the function is
       the same either way, so that a name we fail to resolve still falls
       back to the stub. *)
    let ns, nm =
      match List.tryFind (fun (a, _) -> a = Ident.string_of_lid l)
                         Builtins.stub_aliases with
      | Some (_, b) ->
        let p = String.split ['.'] b in
        List.init p, List.last p
      | None ->
        Builtins.no_fstar_stubs ns, Ident.string_of_id (Ident.ident_of_lid l) in
    let m = String.concat "." ns in
    if not (Loader.module_is_loaded st.deps (tcenv st) m
            || Cons? (Loader.candidate_files st.deps m))
    then l
    else
      let l' = Ident.lid_of_path (ns @ [nm]) (Ident.range_of_lid l) in
      ensure_lid_available st l';
      if Some? (TcEnv.lookup_qname (tcenv st) l') then l' else l

(* -------------------------------------------------------------------- *)
(* Names                                                                *)
(* -------------------------------------------------------------------- *)

(* Section 8.3: [no_fstar_stubs] is applied here, at the one place an F* lid
   becomes a Custard name, so that nothing downstream -- the realization
   tables, output splitting, the linker -- has to know the [FStar.Stubs.*]
   spelling exists.  By the time a lid gets here it has usually been through
   {!unstub_lid} as well, and the rewrite is a no-op; it stays because the
   stubs Custard does *not* resolve away still have to be named. *)
let name_of_lid (l:Ident.lident) : ML name = {
  ns   = Builtins.no_fstar_stubs (List.map Ident.string_of_id (Ident.ns_of_lid l));
  id   = Ident.string_of_id (Ident.ident_of_lid l);
  spec = None;
}

let name_of_bv (b:bv) : ML string =
  uniq (Ident.string_of_id b.ppname) b.index

(* A readable spelling of one [Mono] argument, structurally: the same scheme
   {!Monomorphize.hint_of_cty} uses for a type instantiation, over terms.
   [mapM] specialized at the tactic monad and at [list] should be called
   [mapM__tac_list], not [mapM__1].

   The fuel is not decoration.  A [Mono] argument is any term known at
   specialization time, which includes a whole function body (section 3.2),
   so unlike a [cty] there is no bound on how deep this can go; three levels
   is enough for the type applications and dictionaries that make up almost
   all of them, and anything deeper is not readable as a name anyway.

   [None] means "nothing worth saying", not "failed": a [Tm_name] is a binder
   of the enclosing definition and its gensym index is noise, and a wildcard
   contributes nothing.  The caller drops those and keeps the rest, so one
   uninformative argument does not cost the others their spelling. *)
(* Is this argument a constructed value -- a typeclass dictionary or any other
   record -- rather than something with a name of its own?  Seen through the
   lambda that section 3.2c's hole abstraction wraps a skeleton in, since a
   dictionary with a runtime field is still a dictionary. *)
let rec datacon_headed (st:state) (t:term) : ML bool =
  let hd, _ = U.head_and_args_full t in
  match (U.un_uinst (SS.compress hd)).n with
  | Tm_fvar fv ->
    (match TcEnv.lookup_sigelt (tcenv st) (S.lid_of_fv fv) with
     | Some se -> Sig_datacon? se.sigel
     | None -> false)
  | Tm_abs {body} -> datacon_headed st body
  | _ -> false

let rec hint_of_term (st:state) (fuel:int) (t:term) : ML (option string) =
  if fuel <= 0 then None
  else
    let sub (ts:list term) : ML (list string) = hints_of st (fuel - 1) ts in
    let hd, args = U.head_and_args_full t in
    match (U.un_uinst (SS.compress hd)).n with
    (* A data constructor names itself and stops.  Almost every one that gets
       here is a typeclass dictionary, whose contents are a function of the
       type it was built for -- and that type is another [Mono] argument of
       the same call, so spelling the dictionary out repeats it.  Repeats it
       at length: the unbounded version of this produced
       [cons__tuple4_int_deferred_reason_ref_either_prob_clist_tuple4_int_-
       deferred_reason_ref_prob_Mklistlike_tuple4_..._CCons_tuple4], 225
       characters of which the first 40 were the whole content. *)
    | Tm_fvar fv when datacon_headed st hd ->
      Some (Ident.string_of_id (Ident.ident_of_lid (S.lid_of_fv fv)))
    | Tm_fvar fv ->
      let h = Ident.string_of_id (Ident.ident_of_lid (S.lid_of_fv fv)) in
      Some (String.concat "_" (h :: sub (args |> List.map fst)))
    | Tm_constant c ->
      (match c with
       | Const_int (v, _) -> Some (show v)
       | Const_machine_int (v, _, _, _) -> Some (show v)
       | Const_bool b     -> Some (if b then "true" else "false")
       | Const_string (s, _) -> Some s
       | Const_unit       -> Some "unit"
       | _ -> None)
    (* A type-level lambda is how a higher-kinded argument arrives --
       [fun a -> option a] instantiating an [m:Type -> Type] -- and what names
       it is its body. *)
    | Tm_abs {body} -> hint_of_term st (fuel - 1) body
    | Tm_arrow _ -> Some "fn"
    | Tm_type _ -> Some "type"
    | Tm_refine {b} -> hint_of_term st (fuel - 1) b.sort
    | _ -> None

(* The hints of a run of sibling terms -- the arguments of one application, or
   the [Mono] arguments of one call.  A constructed value is dropped when some
   sibling had something to say: it is a function of the type it was built for,
   and that type is almost always one of those siblings, so the constructor
   name only repeats it.  [parse] specialized at [parser_combinator (t & t)]
   wants to be called [parse__tuple2_t_t], not
   [parse__tuple2_t_t_Mkparser_combinator].  Kept when it is all there is,
   since a constructor name still beats a sequence number. *)
and hints_of (st:state) (fuel:int) (ts:list term) : ML (list string) =
  let hs = ts |> List.collect (fun t ->
                   match hint_of_term st fuel t with
                   | Some s -> [(datacon_headed st t, s)]
                   | None -> []) in
  match hs |> List.filter (fun (dc, _) -> not dc) |> List.map snd with
  | [] -> List.map snd hs
  | plain -> plain

(* The readable half of a specialization's name: every [Mono] argument in
   order, which is what makes two specializations of the same definition
   distinguishable *by their names* rather than by a number whose meaning is
   discovery order (section 12.3). *)
(* Two arguments that spell the same thing say it once: a dictionary and the
   type it is for very often agree, and [show__int_int] is no more informative
   than [show__int]. *)
let rec dedup (seen:list string) (hs:list string) : ML (list string) =
  match hs with
  | [] -> []
  | h :: hs ->
    if List.existsb (fun s -> s = h) seen
    then dedup seen hs
    else h :: dedup (h :: seen) hs

(* A name is for reading, and past some width it stops being readable however
   much information it carries.  Components are dropped from the right until
   the hint fits, since the leftmost argument is the one a reader recognizes;
   the first is kept whatever its length, because a hint of nothing is worse
   than a long one.  Dropping components can make two hints collide, which is
   exactly the case {!spec_suffix}'s [claim] already handles by falling back
   to the sequence number. *)
let hint_width : int = 48

(* Section 30.15.  "Whatever its length" was not a figure of speech: one
   component is one [Mono] argument rendered, and an argument can be a data
   structure that accumulates.  EverParse's CDDL layer builds an environment
   by extending the previous one, so the n-th extension's argument contains
   all n-1 before it, and the emitted C identifier reached 57,361 characters.
   C99 promises 63 significant characters for an internal identifier and 31
   for an external one, so that is well outside what any standard covers, and
   it was quadratic to print besides.  The first component is truncated rather
   than dropped -- a hint of nothing is still worse than a bad one -- and
   truncation can only make two hints collide, which is what {!spec_suffix}'s
   [claim] falls back to the sequence number for. *)
let truncate_hint (h:string) : ML string =
  if String.length h <= hint_width then h
  else String.substring h 0 hint_width

let rec fit (budget:int) (hs:list string) : ML (list string) =
  match hs with
  | [] -> []
  | h :: hs ->
    let h = if budget < 0 then truncate_hint h else h in
    let n = String.length h in
    (* [budget < 0] is the marker for "nothing has been kept yet", so that the
       first component goes in whatever its length -- up to [hint_width]. *)
    if budget >= 0 && n > budget then []
    else h :: fit ((if budget < 0 then hint_width else budget) - n - 1) hs

(* The readable half of a specialization's name: every [Mono] argument in
   order, which is what makes two specializations of the same definition
   distinguishable *by their names* rather than by a number whose meaning is
   discovery order (section 12.3). *)
let hint_of_args (st:state) (args:list (int & term)) : ML (option string) =
  match hints_of st 3 (args |> List.map snd) with
  | [] -> None
  | hs -> Some (String.concat "_" (fit (-1) (dedup [] hs)))

(* The suffix that distinguishes one specialization of [lstr] from its
   siblings.  A definition that was not specialized at all keeps its bare
   name; every specialization gets a suffix, even when it turns out to be the
   only one, so that a name means the same thing regardless of how many
   siblings happen to exist.  The readable hint is preferred, and falls back
   to the sequence number when it is missing or already taken. *)
let spec_suffix (st:state) (lstr:string) (args:list (int & term)) (n:int)
  : ML (option string) =
  if Nil? args then None
  else
    let claim (s:string) : ML bool =
      let key = lstr ^ "__" ^ s in
      if Some? (SMap.try_find st.suffixes key) then false
      else (SMap.add st.suffixes key true; true) in
    match hint_of_args st args with
    | Some h when claim h -> Some h
    | Some h -> Some (h ^ "_" ^ show n)
    | None -> Some (show n)

(* -------------------------------------------------------------------- *)
(* Effects                                                              *)
(* -------------------------------------------------------------------- *)

let eff_of_comp (st:state) (c:comp) : ML eff = Effects.of_comp (tcenv st) c

(* One step of abbreviation unfolding.  Custard emits an abbreviation as a
   name (section 5.5), but a name is not a shape: to apply arguments to a
   value of an abbreviated function type, or to read the effects of doing so,
   the arrow behind the name has to be recovered. *)
let unfold_abbrev (st:state) (ty:cty) : ML (option cty) =
  match ty with
  | TApp (n, args) ->
    (match SMap.try_find st.abbrevs (string_of_name n) with
     | Some (ps, body) ->
       let rec zip (ps:list string) (ts:list cty) : list (string & cty) =
         match ps, ts with
         | p :: ps, t :: ts -> (p, t) :: zip ps ts
         | p :: ps, [] -> (p, TAny) :: zip ps []
         | [], _ -> [] in
       Some (subst_cty (zip ps args) body)
     | None -> None)
  | _ -> None

(* Unfold abbreviations until the head is something else.  A builtin rule
   (section 8) dispatches on the *shape* of its argument's type -- section
   8.4's [read] is a [BufRead] on a [TBuf] and a dereference on a [TRef] --
   and an abbreviation hides that shape behind a name.  In a whole-program
   run the abbreviation is usually gone by the time the rule fires; across a
   unit boundary (section 12.6) it is not, because the imported declaration
   keeps the name the upstream unit gave it.  [FStarC.Tactics.Types.ref_-
   proofstate = ref proofstate] is the case that showed this up: read as a
   [TApp] it printed [(ps).(0)], an array index into an OCaml [ref].
   The fuel is against an abbreviation cycle, which F* rejects but a
   hand-built [.cui] could still carry. *)
let rec head_ty (st:state) (ty:cty) (fuel:int) : ML cty =
  if fuel <= 0 then ty
  else match unfold_abbrev st ty with
       | Some ty' -> head_ty st ty' (fuel - 1)
       | None -> ty

(* Applying [n] arguments to something of type [ty] runs the effects of the
   first [n] arrows.  This is how a call through a *variable* -- a function
   parameter, or a local closure -- gets its effect: there is no declaration to
   consult, only the type.  When the type is not arrow-shaped (typically
   [TAny]) we have to assume the worst, or section 7.3 would let us drop a call
   we know nothing about. *)
let rec apply_eff (st:state) (ty:cty) (n:int) : ML eff =
  if n <= 0 then E_Pure
  else
    match ty with
    | TArrow (_, e, r) -> join_eff e (apply_eff st r (n - 1))
    | _ ->
      match unfold_abbrev st ty with
      | Some ty -> apply_eff st ty n
      | None -> E_Impure

let rec apply_result (st:state) (ty:cty) (n:int) : ML cty =
  if n <= 0 then ty
  else
    match ty with
    | TArrow (_, _, r) -> apply_result st r (n - 1)
    | _ ->
      match unfold_abbrev st ty with
      | Some ty -> apply_result st ty n
      | None -> TAny

(* -------------------------------------------------------------------- *)
(* Requests                                                             *)
(* -------------------------------------------------------------------- *)

(* Remember an abbreviation's definition so that {!unfold_abbrev} can see
   through it later.  Recorded for imported declarations too: an upstream
   unit's abbreviation is just as opaque to a use site here. *)
let note_abbrev (st:state) (d:decl) : ML unit =
  match d with
  | DType t ->
    (match t.dt_body with
     | TAbbrev body -> SMap.add st.abbrevs (string_of_name t.dt_name) (t.dt_params, body)
     | _ -> ())
  | _ -> ()

(* Section 3.3, step 3: this is where the demand-driven loop lives. *)
(* Everything, because the point is to finish: delta and [Zeta] so a recursive
   definition over a literal runs, [Primops] so the primitives underneath it
   fold.  [SafePrimops] rather than [Primops] for {!custard_norm_steps}'s
   reason -- a step whose result has no term representation has nothing to
   emit -- which is also why the answer still has to be checked afterwards
   rather than assumed. *)
let compile_time_steps : list TcEnv.step = [
  TcEnv.AllowUnboundUniverses;
  TcEnv.EraseUniverses;
  TcEnv.Beta;
  TcEnv.Iota;
  TcEnv.Zeta;
  TcEnv.SafePrimops;
  TcEnv.Eager_unfolding;
  TcEnv.Inlining;
  TcEnv.Unascribe;
  TcEnv.Unmeta;
  TcEnv.UnfoldUntil S.delta_constant;
]


let rec request (st:state) (k:spec_key) : ML name =
  Prof.timed "request" (fun () ->
  let k = { k with sk_lid = unstub_lid st k.sk_lid } in
  let key = string_of_key k in
  match SMap.try_find st.names key with
  | Some nm -> nm
  | None ->
  match import st key with
  | Some nm -> nm
  | None ->
    check_budget st k;
    let l = k.sk_lid in
    let lstr = Ident.string_of_lid l in
    let n = (match SMap.try_find st.counts lstr with None -> 0 | Some n -> n) in
    SMap.add st.counts lstr (n + 1);
    let nm = { name_of_lid l with spec = spec_suffix st lstr k.sk_args n } in
    (* Register before translating: a self-reference must find this name
       rather than loop. *)
    SMap.add st.names key nm;
    ensure_lid_available st l;
    match datacon_owner st l with
    (* An exception constructor is not part of a declaration of [Prims.exn]:
       [exn] is extensible and has no declaration at all, so the constructor
       *is* the declaration.  Section 8.5. *)
    | Some ty_lid when Ident.lid_equals ty_lid PC.exn_lid ->
      let d = extract_exn st l nm in
      SMap.add st.emitted key d;
      st.order := key :: !st.order;
      nm
    | Some ty_lid ->
      (* A data constructor is part of its inductive's declaration, not a
         declaration of its own: request the type and emit nothing. *)
      let _ = request st { sk_lid = ty_lid; sk_args = []; sk_subst = []; sk_holes = 0 } in
      nm
    | None ->
      let saved = !st.chain in
      st.chain := key :: saved;
      (* The chain in [st] is what Custard's own errors report; [with_ctx] is
         what an *internal* failure -- a [failwith] from the normalizer, say --
         reports, and without it such a failure names no definition at all. *)
      let d = E.with_ctx ("While extracting " ^ key) (fun () ->
                Prof.timed "extract_lid"
                  (fun () -> extract_lid st l nm k.sk_subst k.sk_holes)) in
      st.chain := saved;
      SMap.add st.emitted key d;
      note_abbrev st d;
      st.order := key :: !st.order;
      nm)

(* Section 12.4, rule 1.  A request whose key a linked unit already exports is
   answered by a reference to that unit's definition: it is *not* translated,
   its body is never looked at, and -- the part that makes separate compilation
   worth anything -- the requests its body would have made are never made
   either.  Cutting the traversal off here is the whole mechanism; everything
   else is bookkeeping so that the later passes and the backend agree about
   what the reference denotes.

   The answer is recorded in [st.names] under the same key an ordinary
   translation would have used, so a second request for it takes the fast path
   above and nothing downstream can tell the two apart. *)
and import (st:state) (key:string) : ML (option name) =
  match Unit.lookup st.links key with
  | None -> None
  | Some (u, e) ->
    (* The interface's declaration is post-[Layout] and post-[Rename]: the name
       it carries is the one the upstream unit actually emitted, which is
       exactly what a reference has to spell.  Keeping that name here -- rather
       than minting a fresh one and remembering a mapping -- is what lets every
       later pass treat an import as an ordinary declaration it happens not to
       emit. *)
    let imp = Imported (u, e.ue_home) in
    let d =
      match e.ue_decl with
      | DType dt    -> DType { dt with dt_flags = imp :: dt.dt_flags }
      | DLet dl     -> DLet  { dl with dl_flags = imp :: dl.dl_flags }
      | DExternal dx -> DExternal { dx with dx_flags = imp :: dx.dx_flags }
      | DExn de     -> DExn { de with de_flags = imp :: de.de_flags }
    in
    let nm = name_of_decl d in
    SMap.add st.names key nm;
    (* Filed under the same key an ordinary translation would have used, and
       for the same reason: {!callee_sig} and {!callee_eff} read it to type a
       call and to decide whether the call may be dropped or reordered.
       Without this an import answers [TAny] and [E_Pure] -- so a
       dereference of an imported [ref] prints as an array index, and a call
       to an imported effectful function may be optimized away.  It does
       *not* join [st.order], so nothing is emitted for it. *)
    SMap.add st.emitted key d;
    note_abbrev st d;
    st.imports := (d, e.ue_type) :: !st.imports;
    if Options.custard_dump_specializations () then
      BU.print2 "Custard: %s comes from unit %s\n" key u;
    Some nm

(* Section 3.6: the budget is checked *before* the definition is looked up and
   before its body is normalized, so that a diverging specialization is cut off
   after a negligible amount of work. *)
and check_budget (st:state) (k:spec_key) : ML unit =
  Prof.timed "budget" (fun () ->
  let lstr = Ident.string_of_lid k.sk_lid in
  let n = match SMap.try_find st.counts lstr with None -> 0 | Some n -> n in
  if n >= Options.custard_max_specializations () then
    custard_error st E.Error_CustardFuelExhausted [
      text ("Custard created " ^ show n ^ " specializations of " ^ lstr ^
            ", which is the limit set by --custard_max_specializations.");
      text "This usually means a definition recurses through a monomorphized \
            binder. Use --custard_dump_specializations to see which \
            definitions are being specialized."
    ];
  st.fuel := !st.fuel - 1;
  if !st.fuel <= 0 then
    custard_error st E.Error_CustardFuelExhausted [
      text ("Custard ran out of specialization fuel while requesting " ^ lstr ^
            "; see --custard_fuel.")
    ])

(* [exception Foo of string] desugars to a data constructor of [Prims.exn],
   which is the one inductive with no [Sig_inductive_typ] to hang fields on:
   its constructors are declared one at a time and a program may add more at
   any point.  So the constructor gets a declaration of its own -- exactly
   what [DExn] is -- and the erased binders go the same way they do for an
   ordinary constructor, so that building one agrees with declaring it. *)
and extract_exn (st:state) (l:Ident.lident) (nm:name) : ML decl =
  let _, ty = TcEnv.lookup_datacon (tcenv st) l in
  let bs, _ = U.arrow_formals_comp ty in
  let bs = drop_flagged (bs |> List.map (Mono.is_erased_binder (tcenv st))) bs in
  DExn { de_name = nm;
         de_args = bs |> List.map (fun b -> ty_of_typ st b.binder_bv.sort);
         de_flags = [] }

and datacon_owner (st:state) (l:Ident.lident) : ML (option Ident.lident) =
  match TcEnv.lookup_sigelt (tcenv st) l with
  | Some ({ sigel = Sig_datacon {ty_lid} }) -> Some ty_lid
  | _ -> None

(* -------------------------------------------------------------------- *)
(* Binder classification                                                *)
(* -------------------------------------------------------------------- *)

(* Section 3.1.  Computed once per definition and cached: it is a property of
   the definition, not of a call site. *)
and binder_classes (st:state) (l:Ident.lident) : ML (list bclass) =
  Prof.timed "binder_classes" (fun () ->
  let key = Ident.string_of_lid l in
  match SMap.try_find st.classes key with
  | Some cs -> cs
  | None ->
    ensure_lid_available st l;
    let attrs = match TcEnv.lookup_sigelt (tcenv st) l with
                | Some se -> se.sigattrs
                | None -> [] in
    let cs =
      (* Section 30.14.  Classify the body that is *compiled*, not the body
         that was written.  [extract_as] replaces one with the other, and the
         two need not mention the same parameters: [Anf.tick]'s specification
         is [fun s n -> n] and its implementation prints [s].  Reading
         liveness off the specification deletes the argument the
         implementation needs. *)
      match TcEnv.lookup_sigelt (tcenv st) l |> Option.map fixup_extract_as with
      | Some se ->
        (match se.sigel with
         | Sig_let {lbs=(_, lbs)} ->
           (match lbs |> List.tryFind (fun lb ->
                    match lb.lbname with
                    | Inr fv -> Ident.lid_equals (S.lid_of_fv fv) l
                    | Inl _ -> false) with
            | Some lb ->
              (* Section 19.4: [lbdef] is what makes the classification as
                 long as the definition really is.  [lbtyp] stops at an
                 abbreviation in the codomain; the lambda does not. *)
              Mono.classify_def (tcenv st) (se.sigattrs @ lb.lbattrs)
                                lb.lbtyp (Some lb.lbdef)
                                (compile_time_demanded st lb.lbdef)
            | None -> [])
         | Sig_declare_typ {t} -> classify (tcenv st) se.sigattrs t
         | _ -> [])
      | None -> []
    in
    (* Section 18.4.  An empty classification is not "everything is [Poly]":
       [split_mono_args] short-circuits on it and hands the *whole* spine
       through unfiltered, so an erased argument is passed at runtime to a
       callee that deleted the parameter -- the section 18.1 failure, reached
       by the other path.

       [lookup_sigelt] is the narrower of the two lookups this module has.  It
       misses whenever the declaration is not a [Sig_let] or [Sig_declare_typ]
       the environment will hand back whole, which [try_lookup_lid] -- what
       {!binder_flags} has always used for the unit and erased flags -- still
       answers.  The two disagreeing is what let the spine and the flags be
       computed from different declarations.  Attributes are only on the
       sigelt, so a fallback classification cannot see a [@@monomorphize]; it
       does see every erased binder, which is the one that miscompiles. *)
    let cs =
      if Cons? cs then cs
      else match lookup_lid_typ st l with
           | Some ((_, ty), _) -> classify (tcenv st) attrs ty
           | None -> [] in
    SMap.add st.classes key cs;
    cs)

(* -------------------------------------------------------------------- *)
(* Types                                                                *)
(* -------------------------------------------------------------------- *)

(* The constructor a name projects a field out of, if it is a projector at
   all.  Section 30.5 uses it to decide whether a stuck type application is a
   field selection worth reducing. *)
and projector_of (st:state) (l:Ident.lident) : ML (option Ident.lident) =
  match TcEnv.lookup_sigelt (tcenv st) l with
  | Some se -> se.sigquals |> List.tryPick (function
                 | S.Projector (c, _) -> Some c
                 | _ -> None)
  | None -> None

and ty_of_typ (st:state) (t:typ) : ML cty =
  Prof.timed "ty" (fun () ->
  let t = SS.compress t in
  match t.n with
  | Tm_bvar b -> TVar (name_of_bv b)
  (* A name of higher kind binds no target type parameter, so there is nothing
     for a [TVar] to refer to; uniform compilation says [any] instead. *)
  | Tm_name b ->
    if Prof.timed "is_type_param" (fun () -> Mono.is_type_param (tcenv st) (S.mk_binder b))
    then TVar (name_of_bv b) else TAny

  | Tm_uinst (t, _) -> ty_of_typ st t

  (* As with {!erasable_app}, a non-informative type is collapsed *before* its
     head is requested.  Requesting it would emit its whole definition -- and
     recursively that of every type it mentions -- for a value that cannot
     exist at runtime; [Pulse.Lib.HashTable.Spec.repr_t] and its [Seq]/[nat]
     entourage are the motivating example. *)
  | Tm_fvar _
  | Tm_app _ when Prof.timed "must_erase" (fun () ->
                    TcUtil.must_erase_for_extraction (tcenv st) t) -> TUnit

  | Tm_fvar fv -> ty_of_fv st fv []

  | Tm_arrow _ ->
    let bs, c = U.arrow_formals_comp t in
    (* Section 7.5: a reifiable codomain is replaced by its representation
       type, which for [Tac a] is [ref_proofstate -> Dv a].  The arrow that
       *returns* it is then pure -- applying the function yields a closure and
       runs nothing -- and the effect reappears on the representation's own
       arrow, which [ty_of_typ] reads off it like any other. *)
    let res, e =
      if Effects.is_reifiable (tcenv st) (U.comp_effect_name c)
      then ty_of_typ st (Effects.reify_comp (env_for_comp (tcenv st) c) c), E_Pure
      else
        (* Section 7.2: a codomain of the form [stt b p q] contributes [b] as
           the result type and promotes the arrow to [E_Impure]. *)
        ty_of_typ st (Effects.result_typ (tcenv st) c), eff_of_comp st c in
    (* [keep_thunk] for the same reason [Mono.classify] applies it to a
       definition's own binders: an arrow all of whose binders are erased would
       stop being an arrow, and a value is not what a caller of it holds.  The
       two have to agree -- one describes what a definition *is*, the other
       what its type *says* -- so they run the same rule. *)
    let bs = Prof.timed "erased_binders" (fun () ->
               drop_flagged (Mono.keep_thunk (tcenv st) bs c
                               (Mono.erased_binders (tcenv st) t)) bs) in
    (* The effect belongs to the last arrow only; the intermediate ones are the
       pure arrows a curried function is made of. *)
    let rec build (bs:binders) : ML cty =
      match bs with
      | [] -> res
      | [b] -> TArrow (ty_of_typ st b.binder_bv.sort, e, res)
      | b :: bs -> TArrow (ty_of_typ st b.binder_bv.sort, E_Pure, build bs)
    in
    build bs

  | Tm_app _ ->
    (match Prof.timed "impure_result" (fun () ->
             Effects.impure_effect_result (tcenv st) t) with
     (* Section 7.2, rule 1: [stt b p q] is represented by [b]. *)
     | Some a -> ty_of_typ st a
     | None ->
       let hd, args = U.head_and_args_full t in
       (match (U.un_uinst hd).n with
        (* An abbreviation with a binder the target's type language cannot
           hold -- [restricted_t (a:Type) (b:a -> Type)], whose [b] is
           higher-kinded -- loses that argument at its *definition*: the body
           [x:a -> b x] compiles to [a -> any], and every use of the name
           inherits the [any] however concrete its own arguments were.
           [FStar.Set.set a = restricted_t a (fun _ -> bool)] is the case that
           showed this up: named, it is [a -> Obj.t], and [union]'s [||] on
           two of those does not typecheck.  Unfolding this one head recovers
           it, because the argument is then in hand: the body beta-reduces to
           [x:a -> bool].  Only heads of this shape are unfolded, and each
           step removes one, so this terminates. *)
        | Tm_fvar fv when has_unrepresentable_param st (S.lid_of_fv fv) ->
          let t' = norm_bounded st "a higher-kinded type abbreviation"
                     [TcEnv.AllowUnboundUniverses; TcEnv.EraseUniverses;
                      TcEnv.Beta; TcEnv.Iota;
                      TcEnv.UnfoldOnly [S.lid_of_fv fv]] t in
          if U.term_eq t' t then TAny else ty_of_typ st t'
        (* A beta-redex in *type* position, which is how a higher-kinded
           [Mono] argument arrives.  [FStarC.SMTEncoding.Pruning] is the case:
           its state monad is [st a = ctxt -> ML (a & ctxt)], and a [monad st]
           dictionary specializes [bind : m a -> (a -> m b) -> m b] with
           [m := fun a -> ctxt -> ML (a & ctxt)] -- rule 5 of section 3.1
           makes the higher-kinded [m] [Mono], since the dictionary's type
           mentions it.  {!specialize} substitutes that into the binder sorts
           and the result comp with [SS.subst], which does not reduce, so
           every [m a] becomes [(fun a -> ...) a].  Only the *body* is
           normalized, so the redex survives in the signature alone, and the
           head is a [Tm_abs] rather than a name: without this it fell through
           to [any], and the state monad's whole plumbing came out as [Obj.t]
           with an [Obj.magic] at every bind.

           Beta alone, and only when the head really is a lambda, so this
           cannot loop: each step removes one. *)
        | Tm_abs _ ->
          let t' = norm_bounded st "a type-level beta-redex"
                     [TcEnv.AllowUnboundUniverses; TcEnv.EraseUniverses;
                      TcEnv.Beta] t in
          if U.term_eq t' t then TAny else ty_of_typ st t'
        (* Section 30.5.  A [Type0] *field* projected out of a record whose
           construction is known: [b1.impl_type] where [b1] has been
           substituted by {!specialize} into [Mkbundle U8.t f].  Nothing else
           here reduces it -- a projector is not a type constructor, so the
           [Tm_fvar] case below hands it to {!ty_of_fv} and gets [any] -- and
           the CDDL bundles reach it through every one of their combinators.

           Unfolding the projector and letting [Iota] meet the constructor
           gives the ground type.  The *scrutinee* has to unfold too, and by
           delta rather than by name: the record is as often a top-level
           definition -- [leaf_bundle] -- as a literal constructor
           application, and a name is something [Iota] cannot see through.
           [Zeta] as well, because the builder is as often *recursive* -- the
           CDDL bundles are built by structural recursion over a grammar
           derivation -- and that is what {!norm_optional} is for: a recursive
           unfolding need not terminate, and giving up has to mean the [any]
           this would have produced anyway, not error 365.  As with the two cases above, this only
           fires when the redex is really there: if the scrutinee is still a
           variable the term comes back unchanged and the fallthrough to [any]
           stands, which is the honest answer.  Each step removes one
           projector, so this terminates. *)
        | Tm_fvar fv when Some? (projector_of st (S.lid_of_fv fv)) ->
          (match norm_optional st
                   [TcEnv.AllowUnboundUniverses; TcEnv.EraseUniverses;
                    TcEnv.Beta; TcEnv.Iota; TcEnv.Zeta; TcEnv.Weak;
                    TcEnv.HNF; TcEnv.UnfoldUntil S.delta_constant] t with
           | None -> TAny
           | Some t' -> if U.term_eq t' t then TAny else ty_of_typ st t')
        (* Section 18.2: a value-indexed arity is a type parameter, so an
           application of one is the parameter itself.  The arguments are
           values and values are erased from types, so [b h] and [b h'] are
           the same target type -- which is what made [b] representable in
           the first place.  Without this the field types of [dtuple2] name
           [b] only under an application and so came out [any]. *)
        | Tm_name bv when Mono.is_value_indexed_arity (tcenv st) bv.sort ->
          TVar (name_of_bv bv)
        | Tm_fvar fv ->
          (* A type constructor's arguments survive into the [cty] exactly when
             they are types: an index like the [n] of [vec n] has no
             counterpart in the target's type language. *)
          let l = S.lid_of_fv fv in
          let keep = match lookup_lid_typ st l with
                     | Some ((_, k), _) ->
                       fst (U.arrow_formals k)
                       |> List.map (fun b -> not (keeps_param st l b))
                     | None -> [] in
          let r = ty_of_fv st fv (drop_flagged keep args |> List.map fst) in
          (* Section 30.8.  Only once [ty_of_fv] has given up: the head is a
             name applied to arguments and there is no type constructor behind
             it, so it is an ordinary *function returning a type* --
             [get_bundle_impl_type b], the accessor EverParse uses in place of
             the projection section 30.5 handles.  There is no reason for the
             two spellings to differ, and reducing is the same move, with the
             same discipline: it fires only when it changes something, and it
             is allowed to run out of budget, since what it recovers is
             precision over the [any] that would otherwise stand.

             The reduct is fully normal, so a second pass through here cannot
             reduce further and the recursion is one level deep. *)
          if not (TAny? r) then r
          else (match norm_optional st
                        [TcEnv.AllowUnboundUniverses; TcEnv.EraseUniverses;
                         TcEnv.Beta; TcEnv.Iota; TcEnv.Zeta; TcEnv.Weak;
                         TcEnv.HNF; TcEnv.UnfoldUntil S.delta_constant] t with
                | None -> TAny
                | Some t' -> if U.term_eq t' t then TAny else ty_of_typ st t')
        | _ -> TAny))

  (* Section 18.2: the argument supplied for a value-indexed arity, which the
     source writes as a lambda -- [dtuple2 header (fun h -> payload h)].  The
     binders are values, and a value cannot reach a [cty], so the body's own
     translation is the answer; if it does depend on its index the body is a
     [match] or a name and falls through to [any] on its own. *)
  | Tm_abs _ when (let bs, _, _ = U.abs_formals t in
                   bs |> List.for_all (fun (b:S.binder) ->
                           not (Mono.is_type_binder (tcenv st) b))) ->
    let _, body, _ = U.abs_formals t in
    ty_of_typ st body

  | Tm_refine {b} -> ty_of_typ st b.sort
  | Tm_ascribed {tm} -> ty_of_typ st tm
  | Tm_meta {tm} -> ty_of_typ st tm

  (* A type in type position: this is where a higher-kinded or dependent type
     would land.  M1 does not represent those. *)
  | Tm_type _
  | _ -> TAny)

(* A binder of a type constructor's kind that is a type but not a *type
   parameter* -- one of higher kind, such as the [b:a -> Type] of
   [restricted_t] -- has no counterpart in the target's type language, and so
   is dropped both from the constructor's parameters and from every use of it.
   For an inductive that is exactly right, uniform compilation being the
   design (section 5.0), and [FStar.Pervasives.dtuple4] -- whose [b], [c] and
   [d] are all of higher kind -- has to keep coming out as a [dtuple4].  For
   an *abbreviation* it is not, because the body is a type the target does
   write down; see the use in {!ty_of_typ}. *)
and has_unrepresentable_param (st:state) (l:Ident.lident) : ML bool =
  match TcEnv.lookup_sigelt (tcenv st) l with
  | Some { sigel = Sig_let _ } ->
    (match lookup_lid_typ st l with
     | None -> false
     | Some ((_, k), _) ->
       let bs, _ = U.arrow_formals k in
       Prof.timed "is_type_param" (fun () ->
         bs |> List.existsb (fun b ->
           is_type_binder (tcenv st) b && not (Mono.is_type_param (tcenv st) b))))
  | _ -> false

(* Which of a type constructor's binders become parameters of the target type.
   Normally only the *type parameters*: a value index like the [n] of [vec n],
   and a binder of higher kind like the [b:a -> Type] of [dtuple4], have no
   counterpart in the target's type language, and uniform compilation (section
   5.0) is free to drop them.

   A *realized* type (section 8.2) is the exception, and it has to be: its
   OCaml declaration is the hand-written one, so its arity is not Custard's to
   choose.  [FStar.Pervasives.dtuple4] is [('a,'b,'c,'d) dtuple4] in
   [FStar_Pervasives.ml] and every use of it has to be applied to four
   arguments -- the three of higher kind simply come out as [any], which is
   what a value of them has no representation *means*. *)
and keeps_param (st:state) (l:Ident.lident) (b:S.binder) : ML bool =
  Prof.timed "is_type_param" (fun () ->
  if is_realized_type st l
  then is_type_binder (tcenv st) b
  else Mono.is_type_param (tcenv st) b)

and is_realized_type (st:state) (l:Ident.lident) : ML bool =
  match Builtins.lookup_rule l with
  | Some Builtins.Rule_realized -> true
  | _ -> false

(* Type constructors are compiled uniformly in their parameters (section 5.0),
   so an inductive is never specialized: it is always requested with an empty
   key. *)
and ty_of_fv (st:state) (fv:fv) (args:list term) : ML cty =  let l = S.lid_of_fv fv in
  if Ident.lid_equals l PC.unit_lid then TUnit
  else
    let args = List.map (ty_of_typ st) args in
    (* Section 8: a type with a custom rule has a representation fixed outside
       F*, so it is never requested and its F* definition is never seen. *)
    match Builtins.lookup_rule l with
    | Some (Builtins.Rule_type f) -> f args
    | _ -> TApp (request st { sk_lid = l; sk_args = []; sk_subst = []; sk_holes = 0 }, args)

(* -------------------------------------------------------------------- *)
(* Terms                                                                *)
(* -------------------------------------------------------------------- *)

and constant_of_sconst (c:sconst) : ML (option constant) =
  match c with
  | Const_unit -> Some CUnit
  | Const_bool b -> Some (CBool b)
  (* The source spelling is kept here, unlike in a key: a literal written
     [0xFF] should come out [0xFF] in the generated C.  This is exactly what
     the legacy ML extraction does with the same pair of cases. *)
  | Const_int (v, b) -> Some (CInt (string_of_int_literal v b, None))
  | Const_machine_int (v, b, sg, w) ->
    Some (CInt (string_of_int_literal v b, Some (sg, w)))
  | Const_char c -> Some (CChar c)
  | Const_string (s, _) -> Some (CString s)
  | _ -> None

and ty_of_constant (st:state) (c:constant) : ML cty =
  let prim (l:Ident.lident) : ML cty = TApp (request st { sk_lid = l; sk_args = []; sk_subst = []; sk_holes = 0 }, []) in
  match c with
  | CUnit -> TUnit
  | CBool _ -> prim PC.bool_lid
  | CInt (_, None) -> prim PC.int_lid
  | CInt (_, Some sw) -> TInt sw
  | CChar _ -> prim PC.char_lid
  | CString _ -> prim PC.string_lid

and is_data_ctor (fv:fv) : ML bool =
  match fv.fv_qual with
  | Some Data_ctor
  | Some (Record_ctor _) -> true
  | _ -> false

(* Section 30.10.  The head of an application, when it is a name that has
   asked for its applications to be evaluated rather than compiled. *)
and compile_time_head (st:state) (t:term) : ML (option Ident.lident) =
  let hd, _ = U.head_and_args_full t in
  match (U.un_uinst (SS.compress hd)).n with
  | Tm_fvar fv ->
    let l = S.lid_of_fv fv in
    ensure_lid_available st l;
    if TcEnv.fv_has_attr (tcenv st) fv PC.custard_compile_time_attr
    then Some l else None
  | _ -> None

and expr_of_term (st:state) (t:term) : ML expr =
  Prof.timed "expr" (fun () ->
  (* [unlazy_emb] before anything else: reducing a closed arithmetic
     expression leaves the result as an *embedding* rather than as a
     constant, so [-1] arrives as a [Tm_lazy] and would otherwise fall
     through to the erasure catch-all below and become [()]. *)
  let t = SS.compress (U.unlazy_emb t) in
  (* Section 30.10.  Custard does not evaluate closed terms on its own
     initiative: a program that computes something at run time means to.  But a
     definition may say that it exists only to produce a constant, and then
     evaluating it is the whole of its compilation.

     The promise is checked, not assumed.  If the head survives reduction the
     argument was not known after all, and saying so names the definition and
     the chain that reached it -- far better than quietly compiling a
     [list char] into a C program, which is what happens without the
     attribute. *)
  let t =
    match compile_time_head st t with
    | None -> t
    | Some l ->
      (* The promise is checked before it is used, and the check is on the
         term as written rather than on the reduct.  Unfolding removes the
         head whether or not anything was computed -- [string_length s] for an
         unknown [s] reduces to the [match] in its body, which is headed by
         nothing at all -- so a head test after the fact would pass exactly
         the case it exists to catch.  What decides the question is whether
         the arguments are known, and that is visible up front. *)
      let free = Free.names t in
      if not (FlatSet.is_empty free) then
        custard_error st E.Error_CustardNotCompileTime [
          text (Ident.string_of_lid l ^ " is marked [@@custard_compile_time], but this application of it depends on a runtime value.");
          text ("The attribute is a promise that every application is known at extraction time; this one is not, because it mentions " ^
                String.concat ", " (List.map (fun (b:bv) -> show b.ppname) (FlatSet.elems free)) ^ ".");
          text "Either the definition should be compiled rather than evaluated, in which case remove the attribute, or the caller should be applying it to a constant."
        ]
      else
      let t' = norm_bounded st ("an application of " ^ Ident.string_of_lid l)
                            compile_time_steps t in
      (match compile_time_head st t' with
       | Some _ ->
         (* Closed and still stuck: a definition it needs was hidden behind an
            interface, so delta had nothing to unfold. *)
         custard_error st E.Error_CustardNotCompileTime [
           text (Ident.string_of_lid l ^ " is marked [@@custard_compile_time], but this application of it does not reduce, although its arguments are all known.");
           text "Some definition it needs is abstract in the interface it was loaded through."
         ]
       | None -> SS.compress (U.unlazy_emb t')) in
  match t.n with
  | Tm_constant c ->
    (match constant_of_sconst c with
     | Some c -> mk (EConst c) (ty_of_constant st c) E_Pure
     | None -> unit_expr)

  | Tm_bvar b
  | Tm_name b ->
    (match lifted_ref st b with
     | Some e -> e
     | None ->
       let ty = ty_of_typ st b.sort in
       let ty =
         if TAny? ty then
           match SMap.try_find st.lettys (show b.index) with
           | Some ty' -> ty'
           | None -> ty
         else ty in
       mk (EVar (name_of_bv b)) ty E_Pure)

  | Tm_uinst (t, _) -> expr_of_term st t

  | Tm_fvar fv -> app_of_fv st fv []

  | Tm_abs _ ->
    let bs, body, rc = U.abs_formals t in
    (* Section 7.5: reify the body against the lambda's own residual effect,
       before translating it.  After this the body is a term of the effect's
       representation type -- a function expecting the proofstate -- and the
       lambda is pure. *)
    let body =
      match rc with
      | Some rc ->
        Effects.maybe_reify (env_for_term (tcenv st) body) body
                            rc.residual_effect
      | None -> body in
    let body = expr_of_term st body in
    let bs =
      let flags = bs |> List.map (Mono.is_erased_binder (tcenv st)) in
      (* Same guard as [Mono.keep_thunk], and unconditional for the same reason
         its own first clause is: a lambda whose binders all vanish stops being
         a lambda.  Its effects then run where it is built rather than where it
         is applied -- and, even when there are none, whatever it is passed to
         is still expecting a function.  A reified [let] whose bound variable
         is a proof is exactly that: the continuation [fun (tok:squash p) -> k]
         is [tac_bind]'s second argument, and [tac_bind] is polymorphic, so
         nothing there drops an argument to match. *)
      let flags = if Cons? flags && List.for_all (fun b -> b) flags
                  then (match List.rev flags with
                        | _ :: r -> List.rev (false :: r)
                        | [] -> flags)
                  else flags in
      drop_flagged flags bs in
    let bs = bs |> List.map (fun b ->
      { b_name = name_of_bv b.binder_bv; b_ty = ty_of_typ st b.binder_bv.sort }) in
    (match bs with
     | [] -> body
     | _ ->
       (* Give the lambda an arrow type: it is what tells a caller reached
          through a variable which effects applying it will run (section 7.3). *)
       let ty = List.fold_right (fun b (ty, e) -> (TArrow (b.b_ty, e, ty), E_Pure))
                                bs (body.ty, body.eff) |> fst in
       mk (EFun (bs, body)) ty E_Pure)

  | Tm_app _ ->
    let hd, args = U.head_and_args_full t in
    (match (U.un_uinst hd).n with
     | Tm_fvar fv -> app_of_fv st fv args

     (* Section 7.5: a [reify e] that survived the normalizer -- typically
        because it was written by hand, as the tactic library does -- is
        performed here.  It is not a function and has no value of its own; the
        result is [e]'s representation, applied to whatever [reify e] was
        applied to. *)
     | Tm_constant (Const_reify (Some l)) when Cons? args ->
       let e0 = args |> List.hd |> fst in
       let e = Effects.maybe_reify (env_for_term (tcenv st) e0) e0 l in
       expr_of_term st (S.mk_Tm_app (TcUtil.remove_reify e) (List.tl args) t.pos)

     | _ ->
       let hd_term = hd in
       let erasable = match (SS.compress hd_term).n with
                      | Tm_name bv -> erasable_result st bv.sort args
                      | _ -> false in
       if erasable then unit_expr else
       let hd = expr_of_term st hd in
       (* No declaration to consult, so the filter has to come from the head's
          own type; a head we cannot type is left alone. *)
       (* Unfolding, not the plain [erased_binders]: this filters a *call
          spine*, and a call runs straight through an abbreviation that the
          local's sort stops at.  Section 18.1. *)
       let flags = match (SS.compress hd_term).n with
                   | Tm_name bv -> Mono.erased_binders_unfold (tcenv st) bv.sort
                   | _ -> [] in
       (* A head with no type to consult -- a [match], a lambda left over from
          beta-reducing a specialized definition -- still must not be given
          its type arguments: they are erased, and one left behind is emitted
          as an unbound term variable. *)
       let args = drop_flagged flags args
                  |> List.filter (fun (a, _) ->
                       not (Mono.is_type_term (tcenv st) a)) in
       let args = args |> List.map fst |> List.map (expr_of_term st) in
       (match args with
        | [] -> hd
        | _ ->
          let n = List.length args in
          let e = List.fold_left (fun e a -> join_eff e a.eff)
                                 (join_eff hd.eff (apply_eff st hd.ty n)) args in
          mk (EApp (hd, args)) (apply_result st hd.ty n) e))

  | Tm_let {lbs=(true, lbs); body} -> lift_letrec st lbs body

  | Tm_let {lbs=(false, [lb]); body} ->
    (match lb.lbname with
     | Inl bv ->
       let bv, body = SS.open_term_bv bv body in
       if inlinable_local st lb then
         (* Section 5.11: a local function is substituted at its uses rather
            than compiled as a closure, so that each use instantiates its type
            and its [Mono] arguments concretely. *)
         expr_of_term st (norm_bounded st "an inlined local function"
                            local_inline_steps
                                      (SS.subst [NT (bv, U.unmeta lb.lbdef)] body))
       else
       let e1 = if TcUtil.must_erase_for_extraction (tcenv st) lb.lbtyp &&
                   U.is_pure_or_ghost_effect lb.lbeff
                then unit_expr
                else expr_of_term st lb.lbdef in
       (* Section 3.2b: remember what the variable stands for, so that a
          [Mono] argument written as [d] is judged by [d]'s definition rather
          than rejected as a runtime parameter.  Only pure definitions: an
          effectful one is evaluated by the [let] that stays behind, and
          baking it into a specialization as well would run it twice.  The
          test is Custard's own classification (section 7) rather than
          [lbeff], which in an [ML] function reports [ML] for a perfectly pure
          right-hand side. *)
       if e1.eff = E_Pure then
         SMap.add st.letdefs (show bv.index) lb.lbdef
       else SMap.add st.effletdefs (show bv.index) ();
       (* The annotation the typechecker left is authoritative when it says
          anything at all; a [--lax] run often leaves nothing, and then the
          right-hand side's own type is the better answer. *)
       let lty = ty_of_typ st lb.lbtyp in
       let lty = if TAny? lty then e1.ty else lty in
       SMap.add st.lettys (show bv.index) lty;
       let e2 = expr_of_term st body in
       mk (ELet (name_of_bv bv, lty, e1, e2)) e2.ty (join_eff e1.eff e2.eff)
     | Inr _ ->
       (* A top-level binding cannot appear here. *)
       expr_of_term st body)

  | Tm_match {scrutinee; brs} ->
    let scrut = expr_of_term st scrutinee in
    let brs = brs |> List.map (branch_of_branch st) in
    let e = List.fold_left (fun e (_, g, b) ->
              join_eff e (join_eff b.eff (match g with None -> E_Pure | Some g -> g.eff)))
              scrut.eff brs in
    let ty = match brs with [] -> TAny | (_, _, b) :: _ -> b.ty in
    mk (EMatch (scrut, brs)) ty e

  | Tm_ascribed {tm} -> expr_of_term st tm
  | Tm_meta {tm} -> expr_of_term st tm

  (* A static quotation is a *value* of type [term]: the syntax tree it
     quotes has to be rebuilt at runtime.  Reflection already knows how --
     embed the term's view and apply [pack_ln] to it -- so the quotation is
     turned into that ordinary term and extracted like any other, exactly as
     [FStarC.Extraction.ML.Term] does.  A bound variable is either a genuine
     [Tv_BVar] node of the quoted syntax or an antiquotation hole, in which
     case what fills it is a term of the *enclosing* program. *)
  | Tm_quoted (_, { qkind = Quote_dynamic }) ->
    mk (EAbort "Custard: cannot evaluate open quotation at runtime") TAny E_Impure

  | Tm_quoted (qt, { qkind = Quote_static; antiquotations = (shift, aqs) }) ->
    let repack (tv:term) : ML expr =
      expr_of_term st
        (U.mk_app (RC.refl_constant_term RC.fstar_refl_pack_ln) [S.as_arg tv]) in
    (match R.inspect_ln qt with
     | RD.Tv_BVar bv ->
       if bv.index < shift
       then repack (EMB.embed (RD.Tv_BVar bv) t.pos None EMB.id_norm_cb)
       else expr_of_term st (S.lookup_aq bv (shift, aqs))
     | tv ->
       repack (EMB.embed #_ #(RE.e_term_view_aq (shift, aqs)) tv t.pos None
                 EMB.id_norm_cb))

  (* A lazy node stands for a value the compiler holds natively.  Most of them
     do have syntax and [unfold_lazy] produces it: an embedded [fv] unfolds to
     the [pack_fv [\"FStar\"; ...]] that rebuilds it, which is code and extracts
     like any other.  [unlazy_emb] at the top of this function has already
     handled the [Lazy_embedding] kind, so this is the rest; unfolding is tried
     exactly once, because [unfold_lazy] hands back what it was given when
     there is nothing to unfold and looping is the other failure mode.

     What is left over is a value with no syntax at all -- an OCaml object some
     primitive step produced.  There is nothing to emit for it, and quietly
     emitting [()] instead is a miscompilation that typechecks only by
     accident, which is how {!custard_norm_steps} came to drop [Primops]. *)
  | Tm_lazy i ->
    let u = U.unfold_lazy i in
    (match (SS.compress u).n with
     | Tm_lazy _ ->
       custard_error st E.Error_CustardUnrepresentableValue [
         text "Custard reached a value with no syntactic representation.";
         text ("The term was: " ^ truncate_msg (show t));
         text "This is a value produced by a primitive implementation rather than by the program, so there is no code to generate for it."
       ]
     | _ -> expr_of_term st u)

  (* Types and proofs in term position are erased. *)
  | Tm_type _ -> unit_expr
  | _ -> unit_expr)

(* -------------------------------------------------------------------- *)
(* Local [let rec] (section 5.10)                                       *)
(* -------------------------------------------------------------------- *)

(* A local [let rec] is lambda-lifted to a declaration of its own rather than
   given an IR node.  Two reasons.  The IR's [ELet] is documented
   non-recursive, and a recursive one would have to be threaded through every
   pass in [Simplify], several of which traverse with a catch-all -- a node
   they did not know about would be silently left untraversed, which is the
   failure mode this whole pipeline exists to avoid.  And a lifted function is
   an ordinary declaration, so it gets specialization, the [scc] pass's
   recursion analysis, and *all three* backends for free; a local [let rec] is
   a closure, and C has no closures.

   The transformation is the textbook one: the variables the definition
   captures from its enclosing scope become extra leading parameters, and every
   reference to the recursive name -- inside the definitions as much as in the
   body -- becomes the lifted name applied to those captures.  The captured
   *type* variables become the declaration's type parameters instead, since
   uniform compilation (section 5.0) passes no types at runtime.

   Nothing is renamed: [open_let_rec] has already made every name unique, and
   a capture keeps its name when it becomes a parameter, so a reference reads
   the same inside the lifted body as outside it. *)
and lifted_ref (st:state) (b:S.bv) : ML (option expr) =
  match SMap.try_find st.lifted (name_of_bv b) with
  | None -> None
  | Some (nm, tyargs, caps, ty, _) ->
    let hd = mk (EQual (nm, tyargs)) ty E_Pure in
    (match caps with
     | [] -> Some hd
     | _ ->
       let args = caps |> List.map (fun (b:binder) ->
                    mk (EVar b.b_name) b.b_ty E_Pure) in
       let n = List.length args in
       (* A partial application builds a closure, so it runs nothing: the
          lifted function always has at least the binders it was written
          with left over. *)
       Some (mk (EApp (hd, args)) (apply_result st ty n) E_Pure))

and is_type_bv (st:state) (b:S.bv) : ML bool =
  Mono.is_type_binder (tcenv st) (S.mk_binder b)

and lift_letrec (st:state) (lbs:list letbinding) (body:term) : ML expr =
  let lbs, body = SS.open_let_rec lbs body in
  let recbvs = lbs |> List.collect (fun lb ->
                 match lb.lbname with Inl bv -> [bv] | Inr _ -> []) in
  if List.length recbvs <> List.length lbs then
    (* [Inr] is a top-level name, which cannot occur in term position. *)
    expr_of_term st body
  else begin
    (* The capture set is shared by the whole nest: a mutually recursive group
       is lifted as a group, so every member takes every member's captures and
       a call from one to another needs no adjustment. *)
    let free = lbs |> List.collect (fun lb -> elems (Free.names lb.lbdef)) in
    let free = free |> List.filter (fun (v:S.bv) ->
                 not (List.existsb (fun (r:S.bv) -> S.bv_eq r v) recbvs)) in
    let rec dedup (l:list S.bv) : ML (list S.bv) =
      match l with
      | [] -> []
      | x :: xs -> x :: dedup (List.filter (fun (y:S.bv) -> not (S.bv_eq x y)) xs) in
    (* Sorted, so that the parameter order depends on the term and not on the
       order [Free.names] happened to walk it. *)
    (* A free variable that is itself a lifted local is not a capture: every
       reference to it becomes a call to its top-level name, applied to *its*
       captures ({!lifted_ref}).  Those are what this nest has to receive, so
       they replace it here.  Without this the emitted body would name
       variables no parameter binds.  A nest's captures are expanded before
       they are recorded, so one pass suffices; the fuel guards a cycle that
       should not arise. *)
    let rec expand (fuel:int) (l:list S.bv) : ML (list S.bv) =
      if fuel <= 0 then l
      else
        let hit : ref bool = alloc false in
        let l = l |> List.collect (fun (v:S.bv) ->
                  match SMap.try_find st.lifted (name_of_bv v) with
                  | Some (_, _, _, _, vs) -> hit := true; vs
                  | None -> [v]) in
        if !hit then expand (fuel - 1) l else l in
    let free = expand 100 free in
    let free = dedup free |> List.sortWith (fun (x:S.bv) (y:S.bv) -> x.index - y.index) in
    let tyvars, valvars = List.partition (is_type_bv st) free in
    (* A higher-kinded one is erased with the rest but is not a parameter the
       target can bind ({!Mono.is_type_param}). *)
    let typars = tyvars |> List.filter (fun (v:S.bv) ->
                   Mono.is_type_param (tcenv st) (S.mk_binder v))
                        |> List.map name_of_bv in
    let tyargs = typars |> List.map (fun v -> TVar v) in
    let caps = valvars |> List.map (fun (v:S.bv) ->
                 { b_name = name_of_bv v; b_ty = ty_of_typ st v.sort }) in
    (* One entry per member, all registered before any body is translated: a
       call from one member to another must find the lifted name, and so must
       a self-call. *)
    let entries = lbs |> List.map (fun lb ->
      let bv = Inl?.v lb.lbname in
      (* A lifted local inherits the *enclosing* specialization's suffix, the
         way {!Monomorphize.with_spec} gives a constructor its type's: it is
         one function per specialization of its enclosing definition, and
         numbering them by discovery order says only that.  This is where the
         great majority of the numeric suffixes came from -- 43 of them for
         [show_list_aux] alone, one per instance [show] was specialized at.
         The counter stays as a tiebreak, for the definition that has two
         locals of the same name in different scopes. *)
      let base = (!st.cur).id ^ "__" ^ Ident.string_of_id bv.ppname in
      let ns = (!st.cur).ns in
      let esp = (!st.cur).spec in
      let ckey = base ^ (match esp with None -> "" | Some s -> "@" ^ s) in
      let n = (match SMap.try_find st.counts ckey with None -> 0 | Some n -> n) in
      SMap.add st.counts ckey (n + 1);
      let nm = { ns = ns; id = base;
                 spec = (match esp, n with
                         | None,   0 -> None
                         | None,   n -> Some (show n)
                         | Some s, 0 -> Some s
                         | Some s, n -> Some (s ^ "_" ^ show n)) } in
      (* Opened exactly once: each [abs_formals] invents *fresh* names for the
         binders it opens, so a second opening would give the body variables
         that no binder here binds. *)
      let xs, def_body, rc = U.abs_formals lb.lbdef in
      (* Section 7.5, exactly as for a lambda ({!expr_of_term}'s [Tm_abs]) and
         for a top-level definition: the body is reified against the effect the
         definiens was written in, before it is translated.  [abs_formals] just
         stripped the lambda, so the [Tm_abs] case will never see this body and
         cannot do it for us -- and a local [let rec] in a tactic is written in
         [Tac] as much as its enclosing function is. *)
      let def_body =
        let ambient () : ML Ident.lident =
          let _, c = U.arrow_formals_comp lb.lbtyp in
          U.comp_effect_name c in
        let eff_name = match rc with
                       | Some rc -> rc.residual_effect
                       | None -> ambient () in
        Effects.maybe_reify (env_for_term (tcenv st) def_body) def_body eff_name in
      let ret, eff = local_result st lb.lbtyp xs in
      (* F* generalizes a local [let rec] just as it does a top-level one, so
         the definiens may bind type variables of its own.  They hold no
         runtime value (section 5.0) and no call site passes them, so they
         belong in the declaration's type parameters, not its binders. *)
      let tybs, valbs = List.partition (fun (b:S.binder) -> is_type_bv st b.binder_bv) xs in
      let own_typars = tybs |> List.map (fun (b:S.binder) -> name_of_bv b.binder_bv) in
      let arg_binders = valbs |> List.map (fun (b:S.binder) ->
                          { b_name = name_of_bv b.binder_bv;
                            b_ty   = ty_of_typ st b.binder_bv.sort }) in
      let binders = caps @ arg_binders in
      let ty = List.fold_right (fun (b:binder) (t, e) -> (TArrow (b.b_ty, e, t), E_Pure))
                               binders (ret, eff) |> fst in
      SMap.add st.lifted (name_of_bv bv) (nm, tyargs, caps, ty, free);
      (nm, binders, ret, eff, own_typars, def_body)) in
    (* The whole group's signatures go in before any body is extracted: the
       calls that make the group recursive are extracted from those bodies,
       and {!callee_eff} has to find an exact effect for each of them or fall
       back to [E_Impure] (see there).  The placeholder bodies are all
       overwritten by the loop below. *)
    let local_key (nm:name) : ML string = "<local>" ^ mangled_name nm in
    entries |> List.iter (fun (nm, binders, ret, eff, own_typars, _) ->
      SMap.add st.emitted (local_key nm) (DLet {
        dl_name    = nm;
        dl_typars  = typars @ own_typars;
        dl_binders = binders;
        dl_ret     = ret;
        dl_eff     = eff;
        dl_body    = mk (EAbort "Custard: provisional body") ret eff;
        dl_flags   = [];
      }));
    entries |> List.iter (fun (nm, binders, ret, eff, own_typars, def_body) ->
      (* A local nested inside this one is lifted too, and names itself after
         whatever [st.cur] holds: that must be *this* definition, not the
         top-level one we are somewhere inside of, or every specialization of
         an enclosing local contributes another indistinguishable numbered
         copy of the same inner name. *)
      let saved_cur = !st.cur in
      st.cur := nm;
      let d = DLet {
        dl_name    = nm;
        dl_typars  = typars @ own_typars;
        dl_binders = binders;
        dl_ret     = ret;
        dl_eff     = eff;
        dl_body    = expr_of_term st def_body;
        (* Provisional, exactly as for a top-level definition: [Simplify.scc]
           recomputes it from the final call graph. *)
        dl_flags   = [Rec (entries |> List.map (fun (nm, _, _, _, _, _) -> nm))];
      } in
      (* Not a specialization of anything -- no source lid names it -- so it
         gets a key of its own, which nothing will ever request. *)
      let key = local_key nm in
      st.cur := saved_cur;
      SMap.add st.emitted key d;
      st.order := key :: !st.order);
    expr_of_term st body
  end

(* The result type and effect of a local definition whose definiens has [xs]
   binders.  As at top level (see [extract_letbinding]), the definiens may have
   more binders than its type has arrows, and each extra one consumes an arrow
   -- and with it the effect that a call site actually runs. *)
and local_result (st:state) (ty:typ) (xs:binders) : ML (cty & eff) =
  let bs, c = U.arrow_formals_comp ty in
  (* The type's binders and the definiens' are different names for the same
     things, and the result type may mention them. *)
  let rec realign (bs:binders) (xs:binders) : ML (list subst_elt) =
    match bs, xs with
    | b :: bs, x :: xs -> NT (b.binder_bv, S.bv_to_name x.binder_bv) :: realign bs xs
    | _ -> [] in
  let c = SS.subst_comp (realign bs xs) c in
  let rec peel (n:int) (e:eff) (t:cty) : ML (eff & cty) =
    if n <= 0 then (e, t)
    else match t with
         | TArrow (_, e', r) -> peel (n - 1) e' r
         | _ -> (e, t) in
  (* Section 7.5: a reifiable result type is replaced by its representation and
     the definition becomes pure, the same trade the top level makes -- what it
     returns is now the closure the representation describes. *)
  let n_extra = List.length xs - List.length bs in
  let eff, ret =
    if Effects.is_reifiable (tcenv st) (U.comp_effect_name c)
    then peel n_extra E_Pure
              (ty_of_typ st (Effects.reify_comp (env_for_comp (tcenv st) c) c))
    else peel n_extra (eff_of_comp st c) (ty_of_typ st (U.comp_result c)) in
  (ret, eff)

(* Delete the entries flagged [true].  A flag list shorter than the list being
   filtered leaves the surplus entries alone, which is what we want when a
   spine is longer than its head's declared arity.

   Note there is no test on implicit/explicit anywhere in Custard: whether an
   argument was written by the user or inferred says nothing about whether it
   has to exist at runtime, and unlike the ML extraction we have no
   interoperability reason to preserve the source arity. *)
(* The complement of {!drop_flagged}: keep exactly the entries flagged [true].
   A flag list shorter than the list keeps nothing of the surplus. *)
and keep_flagged (#a:Type) (flags:list bool) (xs:list a) : ML (list a) =
  match flags, xs with
  | _, [] -> []
  | [], _ -> []
  | f :: flags, x :: xs ->
    let rest = keep_flagged flags xs in
    if f then x :: rest else rest

and drop_flagged (#a:Type) (flags:list bool) (xs:list a) : ML (list a) =
  match flags, xs with
  | _, [] -> []
  | [], xs -> xs
  | f :: flags, x :: xs ->
    let rest = drop_flagged flags xs in
    if f then rest else x :: rest

(* -------------------------------------------------------------------- *)
(* Call sites                                                           *)
(* -------------------------------------------------------------------- *)

(* The core of monomorphization: split a call's arguments into the [Mono] ones,
   which become part of the specialization key, and the rest, which are passed
   at runtime. *)
and app_of_fv (st:state) (fv:fv) (args:args) : ML expr =
  let l = S.lid_of_fv fv in
  if erasable_app st (lookup_lid_typ st l) args
  then unit_expr
  else
    match Builtins.lookup_rule l with
    | Some (Builtins.Rule_prim (n, f)) -> prim_app st l n f args
    | _ -> app_of_fv' st fv args

(* Section 5.1: a term whose *result* is non-informative is replaced by [()]
   without ever being looked at.  This has to happen before the spine is
   traversed, not after: extracting an erased subterm issues specialization
   requests for everything it mentions, and although the simplifier then
   deletes the reference, the requested declarations have already been emitted.
   That is how the ghost model of a Pulse data structure -- [mk_init_pht],
   [Seq.create], [lift_hash_fun] -- used to follow [Ghost.hide] into the
   output, where it is at best dead weight and at worst rejected by karamel for
   using mathematical integers.

   The effect has to be pure or ghost for this to be sound: an erased *result*
   says nothing about whether the call has side effects to run, so
   [unit -> ML (erased int)] is extracted normally. *)
and erasable_app (st:state) (lookup:option ((universes & typ) & Range.range)) (args:args)
  : ML bool =
  match lookup with
  | None -> false
  | Some ((_, ty), _) -> erasable_result st ty args

and erasable_result (st:state) (ty:typ) (args:args) : ML bool =
  Prof.timed "erasable" (fun () ->
  let bs, c = U.arrow_formals_comp ty in
  (* Over-application leaves an unknown residue, and under-application leaves
     a closure; only an exactly saturated call has a result we can judge. *)
  List.length bs = List.length args &&
  U.is_pure_or_ghost_comp c &&
  (* The result type has to be instantiated first, or a polymorphic signature
     is judged on its *variable*: [Pulse.RuntimeUtils.magic : #a:Type -> unit
     -> GTot a] has result [a], which is informative for all this test can
     tell, and the call survives into the output as a reference to a name no
     realization defines -- it is [GTot], so nothing was ever meant to.  With
     the arguments substituted the result is the [squash] the call site asked
     for, and the call disappears. *)
  (let subst = List.map2 (fun (b:S.binder) (a, _) -> NT (b.binder_bv, a)) bs args in
   TcUtil.must_erase_for_extraction (tcenv st) (SS.subst subst (U.comp_result c))))

(* A primitive is a function in F* but an operator in the IR, so an
   under-applied use has to be eta-expanded rather than passed along. *)
and prim_app (st:state) (l:Ident.lident) (n:int)
             (f : list cty -> list expr -> ML expr) (args:args) : ML expr =
  let decl_ty = match lookup_lid_typ st l with
                | Some ((_, ty), _) -> Some ty
                | None -> None in
  let flags = match decl_ty with
              | Some ty -> Mono.erased_binders (tcenv st) ty
              | None -> [] in
  (* A rule that builds a buffer, a null pointer or a cast needs to know at
     which type; the type arguments are erased from the value spine, so they
     are collected separately rather than reconstructed from it. *)
  let tyargs = match decl_ty with
               | Some ty ->
                 keep_flagged (Mono.type_params (tcenv st) ty) args
                 |> List.map fst |> List.map (ty_of_typ st)
               | None -> [] in
  (* A rule may fire for a name the environment cannot type -- [FStar.Custard]
     is not among the modules a whole-program run loads, so [dyn] arrives with
     no declaration at all.  [flags] is then empty and the type arguments would
     survive into the value spine, where the rule takes one of them for its
     own argument and applies the result to the rest: [dyn e] came out as
     [() e].  With nothing to consult, the terms decide, exactly as in the
     application case above. *)
  let args = if None? decl_ty
             then args |> List.filter (fun (a, _) -> not (Mono.is_type_term (tcenv st) a))
             else drop_flagged flags args in
  let args = args |> List.map fst |> List.map (expr_of_term st) in
  (* Section 8's rules dispatch on the shape of an argument's type, so an
     abbreviation has to be seen through first; see {!head_ty}. *)
  let args = args |> List.map (fun (e:expr) -> { e with ty = head_ty st e.ty 10 }) in
  let given, extra =
    if List.length args <= n then args, []
    else List.splitAt n args in
  let missing = n - List.length given in
  if missing > 0
  then
    (* The eta binders stand for the arguments the source did not supply, so
       their types are the primitive's own remaining binder sorts. *)
    let sorts = match decl_ty with
                | Some ty -> Mono.retained_sorts (tcenv st) ty
                | None -> [] in
    let nth_sort (i:int) : ML cty =
      let j = List.length given + i in
      if j < List.length sorts then ty_of_typ st (List.nth sorts j) else TAny in
    let bs = List.mapi (fun i _ -> { b_name = uniq "eta" (GenSym.next_id ());
                                     b_ty = nth_sort i })
                       (repeat_unit missing) in
    let vs = bs |> List.map (fun b -> mk (EVar b.b_name) b.b_ty E_Pure) in
    let body = f tyargs (given @ vs) in
    mk (EFun (bs, body))
       (List.fold_right (fun (b:binder) t -> TArrow (b.b_ty, E_Pure, t)) bs body.ty)
       E_Pure
  else
    let e = f tyargs given in
    match extra with
    | [] -> e
    | _ -> mk (EApp (e, extra)) (apply_result st e.ty (List.length extra))
              (List.fold_left (fun x a -> join_eff x a.eff)
                              (apply_eff st e.ty (List.length extra)) extra)

(* Which of a constructor's arguments do not survive, positionally.

   Two separate reasons.  The leading [num_ty_params] arguments are the
   *inductive's* parameters, which every constructor re-binds but which the
   emitted type does not store -- [extract_inductive] drops all of them, so a
   constructor application and a constructor pattern have to drop exactly the
   same ones or they disagree about the arity.  Erasure alone is not the same
   test: a parameter can be a typeclass dictionary, which is not erased where
   it stands but is still not a field.  The remaining arguments are the real
   fields, and those go by erasure as usual. *)
(* Cached [Mono] binder-flag queries.  The answer depends only on the
   declaration's type, which does not change once its module is loaded, and
   [lookup_lid_typ] has loaded it; a [None] there is not cached, because that
   is the one case that can still change. *)
and binder_flags (st:state) (tag:string) (l:Ident.lident)
                 (f : TcEnv.env -> typ -> ML (list bool)) : ML (list bool) =
  let key = tag ^ Ident.string_of_lid l in
  match SMap.try_find st.bflags key with
  | Some fs -> fs
  | None ->
    match lookup_lid_typ st l with
    | None -> []
    | Some ((_, ty), _) ->
      let fs = f (tcenv st) ty in
      SMap.add st.bflags key fs;
      fs

and ctor_dropped_flags (st:state) (l:Ident.lident) : ML (list bool) =
  let n_params = match TcEnv.lookup_sigelt (tcenv st) l with
                 | Some { sigel = Sig_datacon {num_ty_params} } -> num_ty_params
                 | _ -> 0 in
  binder_flags st "e:" l Mono.erased_binders
  |> List.mapi (fun i erased -> erased || i < n_params)

and repeat_unit (n:int) : ML (list unit) =
  if n <= 0 then [] else () :: repeat_unit (n - 1)

and app_of_fv' (st:state) (fv:fv) (args:args) : ML expr =
  Prof.timed "app_of_fv" (fun () ->
  let l = S.lid_of_fv fv in
  ensure_lid_available st l;
  if is_data_ctor fv
  then
    let nm = request st { sk_lid = l; sk_args = []; sk_subst = []; sk_holes = 0 } in
    let flags = ctor_dropped_flags st l in
    let ufs = binder_flags st "u:" l Mono.unit_binders in
    mk (ECtor (nm, value_args st (drop_flagged flags ufs) (drop_flagged flags args)))
       (ctor_result_ty st l args) E_Pure
  else
    let cs = binder_classes st l in
    let margs, msubst, rest, holes = split_mono_args st l cs args in
    let key = { sk_lid = l; sk_args = margs; sk_subst = msubst;
                sk_holes = List.length holes } in
    let nm = request st key in
    (* Uniform compilation (section 5.0) deletes the type arguments from the
       value spine, but the karamel backend still needs them: it is karamel's
       own monomorphization that turns a polymorphic Custard declaration into C.
       So they are carried on the [EQual] node instead, as a type application. *)
    let tyargs = call_type_args st l cs args in
    let hd_ty = callee_sig st (string_of_key key) tyargs in
    let hd = mk (EQual (nm, tyargs)) hd_ty E_Pure in
    (* [split_mono_args] has already removed the [Mono] and [Dropped]
       arguments, so everything left is passed at runtime. *)
    let rest = value_args st (call_unit_flags st l cs args) rest in
    (* Section 3.2c: the values abstracted out of the [Mono] arguments are
       passed *first*, in the order [specialize] binds them.

       First and not last, because neither end of the spine is otherwise
       stable.  A definition whose result type is an abbreviation hiding an
       arrow -- [f_term : {| lvm m |} -> endo m term], with [endo m a = a -> ML
       (m a)] -- has fewer binders in its type than a saturated call has
       arguments, so holes appended to the spine would land after the ones the
       body's own lambdas bind; and a use that supplies fewer arguments than
       there are [Poly] binders -- [map_optM f_aqual], where [f_aqual]'s own
       argument is the one [map_optM] will pass -- would put them too early.
       Only the front is the same position in both. *)
    let hargs = List.map (fun (v:S.bv) -> expr_of_term st (S.bv_to_name v)) holes in
    let rest = hargs @ rest in
    match rest with
    | [] -> hd
    | _ ->
      let e = List.fold_left (fun e a -> join_eff e a.eff)
                             (callee_eff st (string_of_key key) (List.length rest)) rest in
      mk (EApp (hd, rest)) (apply_result st hd_ty (List.length rest)) e)

(* A constructor application's type is the constructor's result type with the
   inductive's parameters instantiated -- which the spine supplies, since the
   parameters come first.  karamel needs it: [ECons] carries the type of the
   value being built, and an [any] there makes its datatype passes fail. *)
and ctor_result_ty (st:state) (l:Ident.lident) (spine:args) : ML cty =
  match lookup_lid_typ st l with
  | None -> TAny
  | Some ((_, ty), _) ->
    let bs, c = U.arrow_formals_comp ty in
    let rec go (bs:binders) (sp:args) (acc:list subst_elt) : ML (list subst_elt) =
      match bs, sp with
      | b :: bs, (a, _) :: sp -> go bs sp (NT (b.binder_bv, a) :: acc)
      | _ -> acc in
    ty_of_typ st (SS.subst (go bs spine []) (U.comp_result c))

(* A binder whose type is unit-shaped is kept (it may be a thunk) but carries
   no value, so the argument is [()] rather than whatever the source wrote --
   which for a proof obligation can be a [Prims.magic ()] that aborts at
   runtime, or an arbitrarily expensive piece of ghost code. *)
and value_args (st:state) (ufs:list bool) (spine:args) : ML (list expr) =
  match ufs, spine with
  | true :: ufs, _ :: sp -> unit_expr :: value_args st ufs sp
  | _ :: ufs, (a, _) :: sp -> expr_of_term st a :: value_args st ufs sp
  | [], (a, _) :: sp -> expr_of_term st a :: value_args st [] sp
  | _, [] -> []

(* [Mono.unit_binders] restricted to the arguments a call actually passes, in
   the order [split_mono_args] leaves them. *)
and call_unit_flags (st:state) (l:Ident.lident) (cs:list bclass) (spine:args) : ML (list bool) =
  Prof.timed "call_unit_flags" (fun () ->
  let ub = binder_flags st "u:" l Mono.unit_binders in
  let rec go (cs:list bclass) (uf:list bool) (sp:args) : ML (list bool) =
    match cs, sp with
    | [], _ -> []
    | c :: cs, _ :: sp ->
      let u, uf = match uf with
                  | u :: uf -> (u, uf)
                  | [] -> (false, []) in
      if Poly? c then u :: go cs uf sp else go cs uf sp
    | _, [] -> [] in
  go cs ub spine)

(* The type arguments of a call, in the order [extract_letbinding] records them
   in [dl_typars]: source order, restricted to the type binders that survived
   as parameters rather than being specialized away. *)
and call_type_args (st:state) (l:Ident.lident) (cs:list bclass) (spine:args) : ML (list cty) =
  Prof.timed "call_type_args" (fun () ->
  let tflags = binder_flags st "t:" l Mono.type_binders in
  let rec go (cs:list bclass) (tf:list bool) (sp:args) : ML (list cty) =
    match cs, tf, sp with
    | c :: cs, t :: tf, (a, _) :: sp ->
      if t && not (Mono? c)
      then ty_of_typ st a :: go cs tf sp
      else go cs tf sp
    | _ -> [] in
  go cs tflags spine)

(* The callee's signature, instantiated at this call site.  It is available
   because requests are depth-first; a recursive call is the exception, and
   falls back to [TAny]. *)
and callee_sig (st:state) (key:string) (tyargs:list cty) : ML cty =
  Prof.timed "callee_sig" (fun () ->
  match SMap.try_find st.emitted key with
  | Some (DLet d) ->
    let rec zip (ps:list string) (ts:list cty) : list (string & cty) =
      match ps, ts with
      | p :: ps, t :: ts -> (p, t) :: zip ps ts
      | _ -> [] in
    let rec build (bs:list binder) : ML cty =
      match bs with
      | [] -> d.dl_ret
      | [b] -> TArrow (b.b_ty, d.dl_eff, d.dl_ret)
      | b :: bs -> TArrow (b.b_ty, E_Pure, build bs) in
    subst_cty (zip d.dl_typars tyargs) (build d.dl_binders)
  | Some (DExternal d) ->
    (* A type parameter the call site did not supply -- the same shortfall
       {!external_ty} handles for an unspecialized [Mono] binder, seen from
       the other side -- becomes [any] rather than escaping as a free type
       variable, which no backend can print. *)
    let rec zipx (ps:list string) (ts:list cty) : list (string & cty) =
      match ps, ts with
      | p :: ps, t :: ts -> (p, t) :: zipx ps ts
      | p :: ps, [] -> (p, TAny) :: zipx ps []
      | [], _ -> [] in
    subst_cty (zipx d.dx_typars tyargs) d.dx_ty
  | _ -> TAny)

(* Section 3.2: the two ways a call site can fail to be specializable.
   Returns the key arguments, the terms to substitute into the body, and the
   remaining spine. *)
and split_mono_args (st:state) (l:Ident.lident) (cs:list bclass) (spine:args)
  : ML (list (int & term) & list (int & term) & args & list S.bv) =
  Prof.timed "split_mono_args" (fun () ->
  if not (has_mono cs) && not (has_dropped cs) then ([], [], spine, [])
  else
    let n_args = List.length spine in
    let rec go (i:int) (cs:list bclass) (sp:args) (margs:list (int & term))
               (msubst:list (int & term)) (rest:args)
      : ML (list (int & term) & list (int & term) & args) =
      match cs, sp with
      | [], _ -> (List.rev margs, List.rev msubst, List.rev rest @ sp)
      | Poly :: cs, a :: sp -> go (i + 1) cs sp margs msubst (a :: rest)
      (* Section 5.1: an erased argument is deleted, not passed as unit. *)
      | Dropped :: cs, _ :: sp -> go (i + 1) cs sp margs msubst rest
      | Mono :: cs, a :: sp ->
        let a0 = unfold_lets st 100 (fst a) in
        let what = "the argument to binder " ^ show i ^ " of " ^
                   Ident.string_of_lid l in
        let t = norm_bounded st ("a specialization key -- " ^ what) key_norm_steps a0 in
        check_mono_arg st l i t;
        let w = norm_bounded st what subst_norm_steps a0 in
        (* Full reduction can eliminate a free variable that weak reduction
           leaves behind ([fst (x, 1)]); if that happens the two disagree
           about what is a hole, so use the reduced one for both. *)
        let w = if subset (Free.names w) (Free.names t) then w else t in
        go (i + 1) cs sp ((i, t) :: margs) ((i, w) :: msubst) rest
      | Mono :: _, [] ->
        (* Section 3.2(a): partial application of a specializing definition. *)
        custard_error st E.Error_CustardCannotMonomorphize [
          text ("This use of " ^ Ident.string_of_lid l ^ " supplies only " ^
                show n_args ^ " argument(s), but its binder number " ^ show i ^
                " is monomorphized and so must be given at every call site.");
          text "Eta-expand the use, or drop the [@@monomorphize] attribute."
        ]
      | Poly :: _, []
      | Dropped :: _, [] -> (List.rev margs, List.rev msubst, List.rev rest)
    in
    let margs, msubst, rest = go 0 cs spine [] [] [] in
    (* Section 3.2c: whatever the [Mono] arguments still mention of the
       runtime becomes a parameter of the specialization instead of a reason
       to reject the call. *)
    let holes = mono_holes st l margs msubst in
    match holes with
    | [] -> (margs, msubst, rest, [])
    | _ ->
      (* One shared list of holes across all the [Mono] arguments, so that a
         value occurring in two of them is one parameter and not two. *)
      let abs (t:term) : ML term = U.abs (List.map S.mk_binder holes) t None in
      (List.map (fun (i, t) -> (i, abs t)) margs,
       List.map (fun (i, t) -> (i, abs t)) msubst,
       rest, holes))

(* Section 3.2c: the runtime values a call's [Mono] arguments still mention,
   in a deterministic order.

   Everything here is a *free name* of an already normalized argument, so it
   is a value the enclosing definition receives at runtime and nothing more
   can be learned about it.  Two kinds have to be told apart.  A name whose
   sort is a type cannot become a runtime parameter, because types are erased
   and there would be nothing to pass; that stays the section 3.2b rejection
   it has always been.  Any other name is an ordinary value, and passing it is
   exactly what this does. *)
and mono_holes (st:state) (l:Ident.lident)
               (margs:list (int & term)) (msubst:list (int & term))
  : ML (list S.bv) =
  let names_of (acc:list S.bv) (it:int & term) : ML (list S.bv) =
    List.fold_left (fun acc v ->
                      if List.existsb (S.bv_eq v) acc then acc else acc @ [v])
                   acc (elems (Free.names (snd it))) in
  let vs = List.fold_left names_of [] (margs @ msubst) in
  (* Sorted so that the order cannot depend on the order the arguments happen
     to be visited in, which would make the key unstable. *)
  List.sortWith (fun a b -> a.index - b.index) vs

(* Section 5.11: is this local binding a function that should be substituted
   at its uses instead of compiled as a closure?

   Only functions, and only pure ones.  A local function is the one construct
   that has no top-level identity, so it can be neither specialized nor
   annotated: its type parameters and its [Mono] arguments are whatever its
   single definition site says they are, which is to say runtime-opaque, and
   every call it makes into a specializing definition is a section 3.2b
   rejection.  Substituting it gives each use its own instantiation, which is
   what the caller meant and what a monomorphizing compiler owes it.

   Only the shape of the definition is consulted, not [lbeff]: binding a
   lambda builds a closure and is pure whatever the function itself does, and
   [lbeff] reports the *function's* effect -- [ML] for every local helper in
   an [ML] definition, which is most of them.  For the same reason the shape
   is read through [unmeta]: a local helper in an [ML] definition arrives as
   [Meta_monadic_lift (PURE, ALL)] around its [Tm_abs], the lift of a pure
   *value* into the ambient effect, which carries no computational content and
   would otherwise hide every such helper from this test.  Custard computes
   effects from the IR arrow it builds, not from these markers, so dropping
   them changes nothing about the emitted code.

   A local [let rec] cannot be substituted and is lambda-lifted instead
   (section 5.10). *)
(* Section 5.11.  Only *polymorphic* local functions are inlined, and the
   restriction is not a heuristic -- it is the whole reason the pass exists.
   Inlining is what gives a local function's type arguments a concrete value at
   each use, which a local function cannot get any other way: specialization is
   keyed on a lid and a local function has none.  A local function with no type
   binder has nothing to gain from it.

   Inlining every local lambda instead is not merely wasteful, it does not
   terminate in practice.  A local function used twice is duplicated twice, so
   a body with n nested local helpers each used twice costs 2^n -- and since
   inlining runs on the result of inlining, the helpers nest.  Pointed at
   [FStarC.TypeChecker.Normalize.normalize] this consumed 73GB without
   finishing: the give-away in the trace was that no new specializations were
   being requested at all, so it was not a runaway request loop but the same
   already-named code being re-extracted exponentially often.  Restricted to
   the polymorphic case the same run finishes in minutes. *)
and inlinable_local (st:state) (lb:S.letbinding) : ML bool =
  match (SS.compress (U.unmeta lb.lbdef)).n with
  | Tm_abs _ ->
    let bs, _, _ = U.abs_formals (U.unmeta lb.lbdef) in
    bs |> List.existsb (fun b ->
            match (SS.compress b.binder_bv.sort).n with
            | Tm_type _ -> true
            | _ -> false)
  | _ -> false

(* Replace the local [let]-bound variables of a [Mono] argument by what they
   are bound to, to a fixpoint.

   The normalizer cannot do this.  A [let] is only reducible as part of the
   term that binds it, and by the time an argument is inspected it is the bare
   variable; worse, [custard_norm_steps] carries
   [PureSubtermsWithinComputations] precisely so that pure [let]s are *not*
   substituted into the body, which is what keeps sharing and evaluation order
   intact in the emitted code.  That is the right answer for code and the
   wrong one for a key, so the two are separated here: unfolding happens on
   the way to the key and to the substituted value, and never to the body.

   This is what lets a dictionary assembled on the fly be specialized on --
   [let d = { cmp = f } in sort #a #d], the shape [FStarC.Class.Ord.sort_by]
   is written in.  [d] is not a runtime parameter, it is a name for a value
   that section 3.2b can see through. *)
and unfold_lets (st:state) (fuel:int) (t:term) : ML term =
  if fuel <= 0 then t
  else
    let sub = elems (Free.names t) |> List.collect (fun (bv:S.bv) ->
                match SMap.try_find st.letdefs (show bv.index) with
                | Some d -> [NT (bv, d)]
                | None -> []) in
    if Nil? sub then t else unfold_lets st (fuel - 1) (SS.subst sub t)

(* Section 3.2(b): the argument has to be known at specialization time, i.e. it
   must not mention any of the enclosing definition's runtime parameters.  Note
   the check happens *after* canonicalization, so an argument computed out of
   another [Mono] value (a projection out of a dictionary, say) has already
   been reduced to a closed term and is accepted. *)
(* Section 3.2b, narrowed by section 3.2c.  A [Mono] argument may mention
   runtime *values*: those are abstracted out and passed at runtime.  What it
   still may not mention is a runtime *type*, because types are erased and
   there would be nothing to pass at runtime -- the specialization would have
   to be chosen by a value that does not exist in the emitted program. *)
and check_mono_arg (st:state) (l:Ident.lident) (i:int) (t:term) : ML unit =
  (* An argument that is *nothing but* a runtime value has no shape to
     specialize on, and abstracting it would silently turn monomorphization
     into ordinary runtime passing -- which is the performance cliff the
     [Mono] annotation exists to make visible.  Section 3.2c widens what may
     be specialized; it does not remove the guarantee.  So a bare variable is
     still rejected, and it is the case the user can act on: either the value
     should have been static, the binder should not have been marked, or the
     call site asks for runtime passing explicitly with [FStar.Custard.dyn].

     Note that the [dyn] case never reaches here.  [dyn v] is not a name, and
     Custard refuses to unfold it (see [no_specialize_lid]), so [v] becomes an
     ordinary hole and the argument abstracts to [fun h -> dyn h] -- the
     identity skeleton.  Nothing else in the pipeline has to know about it:
     the machinery that already passes a hole at runtime is exactly the
     machinery dictionary passing needs. *)
  (match (SS.compress t).n with
   | Tm_name v ->
     let nm = Ident.string_of_id v.ppname in
     let where = "the monomorphized binder number " ^ show i ^ " of " ^
                 Ident.string_of_lid l in
     (* [dyn] passes the value at runtime, so it is no help at all for a
        *type* argument: under uniform compilation (5.0) there is no runtime
        value to pass.  Only option 2's promotion reaches that case, so do not
        suggest [dyn] for it. *)
     let dynable = match (SS.compress v.sort).n with
                   | Tm_type _ -> false
                   | _ -> true in
     let dyn_hint (lead:string) : list Pprint.document =
       if dynable
       then [text (lead ^ "write [FStar.Custard.dyn " ^ nm ^ "].")]
       else [] in
     (* Whether the name stands for a parameter or for the result of an
        effectful [let] decides what can be done about it, so the two get
        different messages.  Suggesting [@@monomorphize] for a computation's
        result would be advice that cannot be followed. *)
     let msg : list Pprint.document =
       if Some? (SMap.try_find st.effletdefs (show v.index))
       then
         [ text ("The argument passed to " ^ where ^ " is " ^ nm ^ ", the \
                 result of an effectful computation, so the whole argument is \
                 a hole (section 3.2c) and no skeleton is left to specialize \
                 on.");
           text ("Unlike a runtime parameter, this cannot be fixed by an \
                 annotation: the computation runs when the program runs, so " ^
                 nm ^ " is never known earlier.  What is left is to pass the \
                 value at runtime -- for a typeclass dictionary, ordinary \
                 dictionary passing -- which is the identity-skeleton end of \
                 section 3.2c.") ]
         @ dyn_hint "To ask for that here, "
         @ [ text "It is opt-in, and per call site, because it reintroduces \
                   the indirect calls monomorphization exists to remove: \
                   other calls to this function are still specialized." ]
       else
         [ text ("The argument passed to " ^ where ^ " is the runtime \
                 parameter " ^ nm ^ ", so there is nothing to specialize \
                 on.");
           text ("Mark " ^ nm ^ " with [@@monomorphize] in the enclosing \
                 definition so that it, too, is known at specialization time, \
                 or drop the annotation on binder " ^ show i ^ " and pass it \
                 at runtime.") ]
         @ dyn_hint "To pass it at runtime at this call site only, without \
                     changing either signature, "
     in
     custard_error st E.Error_CustardCannotMonomorphize msg
   | _ -> ());
  let is_type_name (v:S.bv) : ML bool =
    match (SS.compress v.sort).n with
    | Tm_type _ -> true
    | _ -> false in
  match elems (Free.names t) |> List.filter is_type_name with
  | [] -> ()
  | v :: _ ->
    custard_error st E.Error_CustardCannotMonomorphize [
      text ("The argument passed to the monomorphized binder number " ^ show i ^
            " of " ^ Ident.string_of_lid l ^ " is not known at specialization \
            time: it mentions the runtime type parameter " ^
            Ident.string_of_id v.ppname ^ ".");
      (if Some? (SMap.try_find st.defbinders (show v.index))
       then text ("Mark " ^ Ident.string_of_id v.ppname ^ " with \
                  [@@monomorphize] in the enclosing definition so that it, \
                  too, is known at specialization time.  (A runtime *value* \
                  would be passed at runtime instead -- see section 3.2c -- \
                  but a type is erased, so there would be nothing to pass.)")
       (* Section 30.4.  Advice that cannot be followed is worse than none:
          the reader writes the attribute somewhere it is never read and gets
          the same error back with nothing to distinguish the two attempts. *)
       else text (Ident.string_of_id v.ppname ^ " is not a parameter of the \
                  enclosing definition, so there is nowhere to write \
                  [@@monomorphize]: the attribute classifies the arguments of \
                  a function (section 3.2), and writing it on a constructor \
                  field is read by nothing.  A type that arrives as a field \
                  rather than as a parameter makes its record an existential \
                  package, which section 30.3 records as unsupported."))
    ]

(* The effect of a call: we know it exactly, because the callee has already
   been extracted by the time we get here (requests are depth-first). *)
(* A *partially* applied callee is a closure, and building a closure is pure
   however impure calling it will be. *)
(* The exception is a call into a recursion whose declaration is still being
   built.  [extract_letbinding] and the local-[let rec] case both register a
   *provisional* declaration -- the right signature, a placeholder body --
   before extracting a body, so a self-recursive call still gets its exact
   effect.  A call between two members of a mutually recursive group is
   reached through a separate request and does not, and neither does anything
   else that is missing here, so the fallback has to assume the worst: read
   pure, a discarded [scan_stmt cbs s1; ...] is deleted by section 7.3 and the
   recursion silently stops traversing half of its argument. *)
and callee_eff (st:state) (key:string) (n_args:int) : ML eff =
  match SMap.try_find st.emitted key with
  | Some (DLet l) ->
    let n = List.length l.dl_binders in
    if n_args < n then E_Pure
    else
      (* Over-application is not a curiosity here, it is what section 7.5
         produces: a [Tac] function extracts with a *pure* declaration whose
         result type is the representation [ref_proofstate -> Dv a], so a
         reified call site has one argument more than the declaration has
         binders and the effect that matters is the one on that arrow.  Reading
         only [dl_eff] would call it pure and let section 7.3 delete it. *)
      join_eff l.dl_eff (apply_eff st l.dl_ret (n_args - n))
  (* An external's declared arrow type is the whole contract we have with its
     realization, exactly as for a call through a variable -- and it is the
     same contract the ML pipeline and karamel work from.  Treating every
     external as impure instead would put a barrier around [Prims.op_Addition]
     and every other arithmetic primitive, which are all [Tot].  [apply_eff]
     still answers [E_Impure] when the type is not an arrow, so a symbol we
     genuinely know nothing about ([dx_ty = TAny]) stays opaque. *)
  | Some (DExternal x) -> apply_eff st x.dx_ty n_args
  | _ -> E_Impure

and branch_of_branch (st:state) (br:S.branch) : ML branch =
  let p, g, b = SS.open_branch br in
  (pat_of_pat st p,
   (match g with None -> None | Some g -> Some (expr_of_term st g)),
   expr_of_term st b)

and pat_of_pat (st:state) (p:S.pat) : ML pat =
  match p.v with
  | Pat_constant c ->
    (match constant_of_sconst c with
     | Some c -> PConst c
     | None -> PWild)
  | Pat_var bv -> PVar (name_of_bv bv)
  | Pat_dot_term _ -> PWild
  | Pat_cons (fv, _, pats) ->
    (* Which subpatterns survive has to be decided exactly as for a
       constructor *application* (see [app_of_fv']), from the constructor's own
       type -- not from the implicit/explicit marks on the subpatterns.  A
       pattern built by a metaprogram (Pulse's elaboration, for one) marks
       nothing implicit, and the two paths disagreeing produces a constructor
       pattern of the wrong arity. *)
    let l = S.lid_of_fv fv in
    let flags = ctor_dropped_flags st l in
    let pats = drop_flagged flags pats |> List.map (fun (p, _) -> pat_of_pat st p) in
    PCtor (request st { sk_lid = l; sk_args = []; sk_subst = []; sk_holes = 0 }, pats)

(* -------------------------------------------------------------------- *)
(* Declarations                                                         *)
(* -------------------------------------------------------------------- *)

and extract_lid (st:state) (l:Ident.lident) (nm:name) (margs:list (int & term))
                (n_holes:int) : ML decl =
  let se = Prof.timed "sigelt"
             (fun () -> TcEnv.lookup_sigelt (tcenv st) l |> Option.map fixup_extract_as) in
  (* A rule declared by the definition's own attributes wins over the built-in
     table, so that a program can override a rule it does not like. *)
  let rule = match se with
             | Some se ->
               (match Builtins.rule_of_attributes se.sigattrs with
                | Some r -> Some r
                | None -> Builtins.lookup_rule l)
             | None -> Builtins.lookup_rule l in
  match rule with
  | Some (Builtins.Rule_extern x) when (match se with
                                        | Some { sigel = Sig_declare_typ {t} } ->
                                          is_type_sig st t
                                        | _ -> false) ->
    (* An external *type*: [Spec.Hash.Definitions.hash_alg] is a C enum the
       hand-written HACL headers declare, and [FStar.Bytes.bytes] a struct
       krmllib declares.  There is nothing to emit -- the declaration exists
       only so that uses have a name -- but the arity still has to be right,
       or a use carrying type arguments would not be the same constructor. *)
    let t = (match se with
             | Some { sigel = Sig_declare_typ {t} } -> t
             | _ -> failwith "unreachable") in
    let bs, _ = U.arrow_formals t in
    let ps = bs |> List.collect (fun b ->
               if Mono.is_type_param (tcenv st) b then [name_of_bv b.binder_bv] else []) in
    DType { dt_name = nm; dt_params = ps; dt_body = TAbstract;
            dt_flags = [Extern (x.Builtins.x_name, x.Builtins.x_header); NoNewtype] }
  | Some (Builtins.Rule_extern x) ->
    (* Section 8.1, kind 4: the F* "definition" is a specification (often
       literally [admit ()]); the real one lives in a hand-written .ml or .c
       file, and all we owe the backend is the type. *)
    let typars, ty = external_ty st l margs in
    DExternal { dx_name = nm; dx_typars = typars; dx_ty = ty;
                dx_target = x.Builtins.x_name; dx_header = x.Builtins.x_header;
                dx_flags = [] }
  | _ ->
  let is_opaque = (match rule with Some Builtins.Rule_opaque -> true | _ -> false) in
  let is_realized = (match rule with Some Builtins.Rule_realized -> true | _ -> false) in
  match se with
  | None ->
    custard_error st E.Error_CustardEntryNotFound [
      text ("Custard cannot find a definition for " ^ Ident.string_of_lid l ^ ".")
    ]
  | Some se when is_realized && Sig_let? se.sigel && not (is_inlinable se)
              && not (is_inline_for_extraction st se)
              && not (Builtins.is_type_only_realized_module
                        (Builtins.no_fstar_stubs
                           (Ident.ns_of_lid l |> List.map Ident.string_of_id))) ->
    (* Section 8.2: a realization replaces the F* module, values included.
       The F* definition is a model -- often written for proof rather than for
       execution, and free to describe a representation the realization does
       not use -- so compiling it would be picking silently between two
       implementations of the same name.

       Three kinds of declaration are not models, and stay compiled:

       - a projector or discriminator, which is derived from the type
         declaration Custard already has, and which section 5's inlining turns
         into the one field read it is;
       - anything [inline_for_extraction], which in a realized module means
         precisely that the realization does *not* define it -- that is what
         [FStarC.PSMap]'s own comment says about its [psmap_*] aliases -- so
         an external would be an unresolved symbol at link time;
       - a type abbreviation, which F* also represents as a [Sig_let]: it is
         a type declaration, and there is no such thing as an external one.
         A realized module's genuine types are handled by [with_realized]
         below. *)
    let typars, ty = external_ty st l margs in
    DExternal { dx_name = nm; dx_typars = typars; dx_ty = ty; dx_target = None;
                dx_header = None;
                dx_flags = if is_modelled_lid l then [Modelled] else [] }
  | Some se ->
    let d = Prof.timed "extract_sigelt"
              (fun () -> extract_sigelt st l nm margs n_holes se) in
    let d = if is_opaque || is_realized then with_no_newtype d else d in
    (* [inline_for_extraction] on a type in a realized module means what it
       says: the alias is not in the hand-written .ml, and the realization
       expects to be named through what it stands for.  [FStarC.PSMap.psmap]
       is that; [FStar.Dyn.dyn], which the realization does define, is not.
       [unfold] says the same thing more strongly -- the definition is one
       the normalizer should always expand, so the name is not meant to
       survive anywhere, least of all into a hand-written file.
       [FStar.Stubs.Tactics.V2.Builtins.ret_t] is that case: flagged
       [Realized] it printed a reference to a type its realization has no
       reason to define, and left alone section 5.5 resolves it away. *)
    let inlined = se.sigquals |> List.existsb (fun q ->
                    q = S.Inline_for_extraction ||
                    q = S.Unfold_for_unification_and_vcgen) in
    let d = if is_realized && not inlined then with_realized d else d in
    let d = if is_modelled_lid l && not inlined then with_modelled d else d in
    if is_inlinable se && not (Some? (SMap.try_find st.roots (Ident.string_of_lid l)))
    then with_inline d else d

(* [@@FStar.ExtractAs.extract_as impl] replaces a definition's body by [impl]
   for extraction.  This is how Pulse hands us its programs: the F* definition
   of a [fn] is a proof term in Pulse's own syntax, and the attribute carries
   the ordinary [Dv] F* term that it elaborates to.  The ML pipeline does the
   same thing in [FStarC.Extraction.ML.Modul.fixup_sigelt_extract_as]; unlike
   it we do not force the result to be recursive, since Custard's [Rec] flag
   drives the emission order and a spurious cycle would be noise.  Pulse's own
   knot-tying makes the recursive uses visible as ordinary occurrences of [l],
   so testing for them is enough. *)
and fixup_extract_as (se:sigelt) : ML sigelt =
  match se.sigel, List.tryPick ExtractAs.is_extract_as_attr se.sigattrs with
  | Sig_let {lids; lbs=(is_rec, [lb])}, Some impl ->
    let self = match lb.lbname with
               | Inr fv -> mem (S.lid_of_fv fv) (Free.fvars impl)
               | Inl _ -> false in
    { se with sigel = Sig_let {lids; lbs=(is_rec || self, [{lb with lbdef = impl}])} }
  (* A [val] with the attribute is the case the ML pipeline does not handle,
     because there the implementation is always in scope: [--cmi] loads the
     [.fst] alongside the [.fsti].  Custard meets declarations whose [.fst] was
     never installed -- [Pulse.Lib.Core] is checked into the Pulse plugin and
     only its interface is shipped -- and for those the attribute is the whole
     of what we know.  It is also exactly what it was written for: [as_atomic]
     is an [admit ()] whose [extract_as] says "compile me as the identity". *)
  | Sig_declare_typ {lid; us; t}, Some impl ->
    let fv = S.lid_as_fv lid None in
    let lb = U.mk_letbinding (Inr fv) us t PC.effect_Tot_lid impl [] se.sigrng in
    { se with sigel = Sig_let {lids=[lid];
                               lbs=(mem lid (Free.fvars impl), [lb])};
              sigquals = S.Inline_for_extraction :: se.sigquals }
  | _ -> se

(* The projectors and discriminators F* derives for an inductive are one field
   read or one tag test each; leaving them as calls would make the output
   unreadable and, in C, slow. *)
(* [inline_for_extraction] in a realized module means the realization does not
   define the symbol and expects to be named through what it stands for.  A
   type abbreviation counts as one whether or not it says so: F* represents it
   as a [Sig_let] whose result is a [Type], and a type is not a value. *)
(* The letbinding [TcInductive] would have produced for a projector or a
   discriminator that [@@no_auto_projectors] left as a bare [val].  The shapes
   are copied from that pass, so what Custard extracts here is exactly what it
   extracts for an ordinary projector: the same match, which section 5's
   inlining then collapses into one [EProj] or one [EDiscrim].

   [t] is the declared type: the inductive's parameters and indices, then the
   projectee.  The *constructor*'s binders are those parameters again followed
   by the fields, so a field is looked for past the parameter count.  A
   parameter is matched by a dot pattern, since the scrutinee's type
   determines it and nothing stores it. *)
and assumed_projector_lb (st:state) (se:sigelt) (l:Ident.lident) (t:typ)
  : ML (option letbinding) =
  let env = tcenv st in
  match se.sigquals |> List.tryPick (function
          | S.Projector (c, f) -> Some (c, Some f)
          | S.Discriminator c  -> Some (c, None)
          | _ -> None) with
  | None -> None
  | Some (ctor, field) ->
    let bs, _ = U.arrow_formals_comp t in
    (* The projectee is *not* the last binder.  [arrow_formals_comp] flattens
       the whole spine, and when the projected field's own type is an arrow --
       [impl_validate: U64.t -> bool] -- the spine runs on past the projectee
       into that arrow.  Taking the last binder then scrutinizes the field's
       argument instead of the record, which is a miscompilation and not a
       rejection: [run] came out as [i.contents.impl_validate].  So find it by
       its type instead, as the first binder headed by the inductive that
       [ctor] belongs to; everything before it is a parameter or an index, and
       everything after belongs to the field.

       The trailing binders are kept and the match is applied to them, which
       is verbatim the shape F* itself used to generate for this case and the
       one [Simplify.eta_reduce] exists to clean up.  Dropping them instead
       would leave the definition with fewer binders than its declared type,
       which section 19.4 is about. *)
    let ind = TcEnv.typ_of_datacon env ctor in
    let is_projectee (b:S.binder) : ML bool =
      let hd, _ = U.leftmost_head_and_args (Mono.strip b.binder_bv.sort) in
      match (SS.compress hd).n with
      | Tm_fvar fv -> Ident.lid_equals (S.lid_of_fv fv) ind
      | Tm_uinst ({n=Tm_fvar fv}, _) -> Ident.lid_equals (S.lid_of_fv fv) ind
      | _ -> false in
    let rec split_at_projectee (bs:list S.binder)
      : ML (option (S.binder & list S.binder)) =
      match bs with
      | [] -> None
      | b :: rest ->
        if is_projectee b then Some (b, rest)
        else split_at_projectee rest in
    match split_at_projectee bs with
    | None -> None
    | Some (projectee, post) ->
      let _, cty = TcEnv.lookup_datacon env ctor in
      let all_params, _ = U.arrow_formals cty in
      let ntps = match TcEnv.num_inductive_ty_params env (TcEnv.typ_of_datacon env ctor) with
                 | Some n -> n
                 | None -> 0 in
      let var (x:bv) : ML S.pat = S.withinfo (Pat_var x) Range.dummyRange in
      let fresh (b:S.binder) : ML S.pat =
        var (S.gen_bv (Ident.string_of_id b.binder_bv.ppname) None S.tun) in
      (* [chosen] is the index of the field being projected, absent for a
         discriminator, which looks at the tag and at no field. *)
      let ctor_pat (chosen : option int) : ML S.pat =
        let args = all_params |> List.mapi (fun j b ->
          let imp = S.is_bqual_implicit_or_meta b.binder_qual in
          let p = if imp && j < ntps
                  then S.withinfo (Pat_dot_term None) Range.dummyRange
                  else fresh b in
          (p, imp)) in
        S.withinfo (Pat_cons (S.lid_as_fv ctor None, None, args)) Range.dummyRange in
      let scrut = S.bv_to_name projectee.binder_bv in
      let body =
        match field with
        | None ->
          let pt = ctor_pat None in
          let pf = var (S.new_bv None S.tun) in
          Some (S.mk (Tm_match { scrutinee = scrut; ret_opt = None;
                                 brs = [U.branch (pt, None, U.exp_true_bool);
                                        U.branch (pf, None, U.exp_false_bool)];
                                 rc_opt = None }) Range.dummyRange)
        | Some f ->
          (* By name rather than by index: the projector's own binders say
             nothing about where the field sits in the constructor. *)
          let fname = Ident.string_of_id f in
          match all_params |> List.mapi (fun j b ->
                  if j >= ntps && Ident.string_of_id b.binder_bv.ppname = fname
                  then [j] else []) |> List.flatten with
          | [] -> None
          | j :: _ ->
            let x = S.gen_bv fname None S.tun in
            let args = all_params |> List.mapi (fun k b ->
              let imp = S.is_bqual_implicit_or_meta b.binder_qual in
              let p = if k = j then var x
                      else if imp && k < ntps
                      then S.withinfo (Pat_dot_term None) Range.dummyRange
                      else fresh b in
              (p, imp)) in
            let pat = S.withinfo (Pat_cons (S.lid_as_fv ctor None, None, args))
                                 Range.dummyRange in
            Some (S.mk (Tm_match { scrutinee = scrut; ret_opt = None;
                                   brs = [U.branch (pat, None, S.bv_to_name x)];
                                   rc_opt = None }) Range.dummyRange) in
      match body with
      | None -> None
      | Some body ->
        (* The match returns the field; if the field is itself a function the
           spine had more binders, and they are handed straight back to it. *)
        let body = match post with
                   | [] -> body
                   | _ -> S.mk_Tm_app body
                            (post |> List.map (fun (b:S.binder) ->
                               S.as_arg (S.bv_to_name b.binder_bv)))
                            Range.dummyRange in
        Some (U.mk_letbinding (Inr (S.lid_and_dd_as_fv l None)) []
                t PC.effect_Tot_lid (U.abs bs body None) [] Range.dummyRange)

and is_inline_for_extraction (st:state) (se:sigelt) : ML bool =
  se.sigquals |> List.existsb (fun q -> q = S.Inline_for_extraction)
  || (match se.sigel with
      | Sig_let {lbs=(_, [lb])} ->
        let _, c = U.arrow_formals_comp lb.lbtyp in
        (* Through {!Mono.is_type_binder}, because the result is written
           [eqtype] as often as [Type] and an abbreviation has to be unfolded
           before it can be recognised. *)
        is_type_binder (tcenv st) (S.mk_binder (S.new_bv None (U.comp_result c)))
      | _ -> false)

and is_inlinable (se:sigelt) : ML bool =
  (se.sigquals |> List.existsb (fun q ->
     match q with
     | S.Projector _ | S.Discriminator _ -> true
     | _ -> false))
  (* An [inline_for_extraction] definition given by [extract_as] is a wrapper
     written to disappear: every one of them in ulib and Pulse is an identity
     or a constant.  Left standing they defeat the backends that need to see
     the operation itself -- karamel rejects [let tmp = r[0] <- x in as_atomic
     tmp], because an assignment is a statement and only the inlined form puts
     it in statement position. *)
  || (se.sigquals |> List.existsb (fun q -> q = S.Inline_for_extraction)
      && Some? (List.tryPick ExtractAs.is_extract_as_attr se.sigattrs))

and with_inline (d:decl) : ML decl =
  match d with
  | DLet l when not (l.dl_flags |> List.existsb Rec?) ->
    DLet { l with dl_flags = Inline :: l.dl_flags }
  | d -> d

(* [@@custard_opaque]: the representation is fixed outside F*, so neither
   erasure nor the newtype collapse of section 5.2 may touch it. *)
and with_no_newtype (d:decl) : ML decl =
  match d with
  | DType t ->
    DType { t with dt_flags = NoNewtype :: List.filter (fun f -> not (Erased? f)) t.dt_flags }
  | d -> d

(* A type of a realized module (section 8.2): the declaration stays, so that
   the passes can see its constructors and fields, but it belongs to the
   hand-written OCaml file and only the backend's reference to it is emitted.
   The flag rides on the declaration; {!with_no_newtype} above has already
   pinned the representation.

   This applies to an abbreviation too, and has to: [FStar.Set.set a = a ->
   prop] is realized by an OCaml [type 'a set], and expanding the F\* model
   instead would give every operation the model's type rather than the
   realization's.  The obligation it puts on a realization is that every type
   its interface names is in the .ml, abbreviations included -- ML extraction
   does not need that, because it prints few type annotations, and Custard
   does, because it prints them all.  See section 8.2. *)
and with_realized (d:decl) : ML decl =
  match d with
  | DType t -> DType { t with dt_flags = Realized :: t.dt_flags }
  | d -> d

(* Section 20.  Unlike {!with_realized} this marks values too: a model's
   operations are karamel's to translate, at their use sites, so Custard must
   emit no declaration for them either.  Everything else about the declaration
   is kept -- the shape, the arity, the polymorphism -- because the passes
   still have to typecheck uses of it. *)
and with_modelled (d:decl) : ML decl =
  match d with
  | DType t -> DType { t with dt_flags = Modelled :: t.dt_flags }
  | DExternal x -> DExternal { x with dx_flags = Modelled :: x.dx_flags }
  | DLet l -> DLet { l with dl_flags = Modelled :: l.dl_flags }
  | d -> d

and is_modelled_lid (l:Ident.lident) : ML bool =
  Builtins.is_krml_model_name
    (Builtins.no_fstar_stubs (Ident.ns_of_lid l |> List.map Ident.string_of_id))
    (Ident.string_of_id (Ident.ident_of_lid l))

(* The type an external is *used* at.  An external has no body to specialize,
   but its declared type is still polymorphic, and taking it at face value
   would type every call to [FStar.Pervasives.Native.fst] as returning [any] --
   which is how a hand-written realization written polymorphically, as they all
   are, would otherwise poison every program that touches it.

   Nothing about the target changes: OCaml's [fst] really is polymorphic, so
   naming its result type at the instantiation the call site asked for is
   describing the target more precisely, not coercing it.  So the [Mono]
   arguments are substituted into the declared type and their binders dropped,
   exactly as [specialize] does for a definition; the [Poly] binders stay, and
   erasure handles them as usual. *)
and external_ty (st:state) (l:Ident.lident) (margs:list (int & term))
  : ML (list string & cty) =
  match lookup_lid_typ st l with
  | None -> ([], TAny)
  | Some ((_, ty), _) ->
    let cs = binder_classes st l in
    let bs, c = U.arrow_formals_comp ty in
    (* A [Mono] binder the call site did not supply is a call that could not be
       specialized; its type variable is not a parameter the caller will
       instantiate, so it becomes [any] here just as it did before, rather
       than escaping as a free variable. *)
    let rec go (i:int) (bs:binders) (cs:list bclass) (subst:list subst_elt)
               (keep:binders) (anys:list string)
      : ML (binders & list subst_elt & list string) =
      match bs with
      | [] -> (List.rev keep, subst, anys)
      | b :: bs' ->
        let cs' = match cs with [] -> [] | _ :: cs' -> cs' in
        let cls = match cs with [] -> Poly | c :: _ -> c in
        let sort = SS.subst subst b.binder_bv.sort in
        let b' = { b with binder_bv = { b.binder_bv with sort = sort } } in
        (match cls, margs |> List.tryFind (fun (j, _) -> j = i) with
         | Mono, Some (_, a) -> go (i + 1) bs' cs' (NT (b.binder_bv, a) :: subst) keep anys
         | Mono, None when is_type_binder (tcenv st) b ->
           go (i + 1) bs' cs' subst (b' :: keep) (name_of_bv b.binder_bv :: anys)
         | _ -> go (i + 1) bs' cs' subst (b' :: keep) anys)
    in
    let keep, subst, anys = go 0 bs cs [] [] [] in
    let c = SS.subst_comp subst c in
    let typars = keep |> List.collect (fun b ->
                   let n = name_of_bv b.binder_bv in
                   if Mono.is_type_param (tcenv st) b && not (List.mem n anys) then [n] else []) in
    (* Built from [keep] rather than by handing [U.arrow keep c] to
       {!ty_of_typ}: rebuilding the arrow closes its binders, and reopening
       them names them afresh, so the [TVar]s in the result would no longer be
       the ones [typars] lists and a call site's instantiation would miss
       them. *)
    let res = ty_of_typ st (Effects.result_typ (tcenv st) c) in
    let e = eff_of_comp st c in
    let vs = drop_flagged (Mono.erased_binders (tcenv st) (U.arrow keep c)) keep in
    let rec build (bs:binders) : ML cty =
      match bs with
      | [] -> res
      | [b] -> TArrow (ty_of_typ st b.binder_bv.sort, e, res)
      | b :: bs -> TArrow (ty_of_typ st b.binder_bv.sort, E_Pure, build bs) in
    (typars, subst_cty (anys |> List.map (fun a -> (a, TAny))) (build vs))

and extract_sigelt (st:state) (l:Ident.lident) (nm:name) (margs:list (int & term))
                   (n_holes:int) (se:sigelt)
  : ML decl =
  match se.sigel with
  | Sig_let {lbs=(is_rec, lbs)} ->
    (match lbs |> List.tryFind (fun lb ->
             match lb.lbname with
             | Inr fv -> Ident.lid_equals (S.lid_of_fv fv) l
             | Inl _ -> false) with
     | Some lb ->
       (* A type abbreviation is a [Sig_let] too; it must not become a value. *)
       if is_type_sig st lb.lbtyp
       then (let d = Prof.timed "abbrev" (fun () -> extract_type_abbrev st nm lb) in
             if is_erasable st se || is_prop_sig st lb.lbtyp
             then with_erased_flag d else d)
       else Prof.timed "letbinding"
              (fun () -> extract_letbinding st l nm lb is_rec margs n_holes)
     | None -> DExternal { dx_name = nm; dx_typars = []; dx_ty = TAny; dx_target = None; dx_header = None; dx_flags = [] })

  | Sig_declare_typ {t} ->
    (* An [assume val], or a type whose definition is not available: an
       external symbol, to be realized by the backend or by a custom rule
       (section 8). *)
    if is_type_sig st t
    then
      (* The declaration's arity is its kind's type binders.  It has to be
         written down even though the type has no body: a use of it carries
         those arguments, and a declaration that binds none of them would not
         be the same type constructor. *)
      let bs, _ = U.arrow_formals t in
      let ps = bs |> List.collect (fun b ->
                 if Mono.is_type_param (tcenv st) b then [name_of_bv b.binder_bv] else []) in
      let extern = match Builtins.extern_type_of_lid l with
                   | Some x -> [Extern (x.Builtins.x_name, x.Builtins.x_header); NoNewtype]
                   | None -> [] in
      DType { dt_name = nm; dt_params = ps; dt_body = TAbstract;
              dt_flags = extern @ (if is_erasable st se || is_prop_sig st t
                                   then [Erased] else []) }
    else
      (* [@@no_auto_projectors] makes F* declare a type's projectors and
         discriminators without defining them: [TcInductive] emits the [val]
         and stops there.  They are still derived from the type declaration
         and still mean exactly one field read or one tag test, so Custard
         builds the definition F* would have built and extracts that.  Left
         as externals they would be unresolved symbols at link time; Pulse's
         [st_term] carries the attribute, and its projectors are what a
         record update compiles to. *)
      (match assumed_projector_lb st se l t with
       | Some lb -> with_inline (extract_letbinding st l nm lb false margs n_holes)
       | None ->
         DExternal { dx_name = nm; dx_typars = []; dx_ty = ty_of_typ st t;
                     dx_target = None; dx_header = None; dx_flags = [] })

  | Sig_inductive_typ {params} ->
    let d = Prof.timed "inductive" (fun () -> extract_inductive st l nm params) in
    if is_erasable st se then with_erased_flag d else d

  | Sig_datacon _ ->
    (* Reached through a constructor application or pattern: what we actually
       want is the type it belongs to, which the layout analysis (M3) will
       need.  For now record it as external so the name exists. *)
    DExternal { dx_name = nm; dx_typars = []; dx_ty = TAny; dx_target = None; dx_header = None; dx_flags = [] }

  | Sig_bundle {ses} ->
    (match ses |> List.tryFind (fun se ->
             match se.sigel with
             | Sig_inductive_typ {lid} -> Ident.lid_equals lid l
             | _ -> false) with
     | Some se -> extract_sigelt st l nm margs n_holes se
     | None -> DType { dt_name = nm; dt_params = []; dt_body = TAbstract; dt_flags = [] })

  | _ ->
    DExternal { dx_name = nm; dx_typars = []; dx_ty = TAny; dx_target = None; dx_header = None; dx_flags = [] }

(* Section 5.1: a type declared [erasable] has no runtime representation at any
   instantiation, which is what makes it safe to erase uniformly (section
   5.0).  The structural closure -- a type all of whose fields are erased is
   itself erased -- is computed later, by the layout analysis. *)
and is_erasable (st:state) (se:sigelt) : ML bool =
  U.has_attribute se.sigattrs PC.erasable_attr

and with_erased_flag (d:decl) : ML decl =
  match d with
  | DType t -> DType { t with dt_flags = Erased :: t.dt_flags }
  | d -> d

(* [eqtype], [Type0] and friends are all abbreviations, so we have to unfold
   before we can tell a type declaration from a value declaration. *)
and is_type_sig (st:state) (t:typ) : ML bool =
  let _, c = U.arrow_formals_comp t in
  (* Section 19.14.  Strip *before* normalizing, not only after.  A refinement
     is a proposition, and whether a declaration is a type does not depend on
     one; handing the whole [x: t{p}] to the normalizer reduces [p] in full
     and then discards it.  On EverParse's CDDL layer that is a hard stop
     rather than a cost: [env9 : bundle_env ... { bundle_env_included ... /\
     ... == wf_ast_env_extend_typ_with_weak ... }] exhausts a budget of 10^9
     steps in a proof that has no bearing on the answer.  [Mono.strip] is
     syntactic and costs nothing. *)
  let res = norm_bounded st "a type signature"
                         [TcEnv.AllowUnboundUniverses; TcEnv.EraseUniverses;
                          TcEnv.Beta; TcEnv.Iota;
                          TcEnv.UnfoldUntil delta_constant]
                         (Mono.strip (U.comp_result c)) in
  (* [eqtype] is a refinement of [Type0], so peel refinements too.  [prop] is
     [assume val prop : Type0], i.e. opaque, so the normalizer cannot reduce it
     to a [Tm_type]; but a [prop]-valued definition such as [eq2] or [l_and] is
     a type constructor all the same. *)
  let rec is_type (t:typ) : ML bool =
    match (SS.compress t).n with
    | Tm_type _ -> true
    | Tm_refine {b} -> is_type b.sort
    | Tm_fvar fv -> S.fv_eq_lid fv PC.prop_lid
    | _ -> false
  in
  is_type res

(* A [prop]-valued type constructor is by definition non-informative, so we can
   tell the layout analysis so directly instead of waiting for the structural
   closure to (fail to) discover it: these are all opaque. *)
and is_prop_sig (st:state) (t:typ) : ML bool =
  let _, c = U.arrow_formals_comp t in
  (* Section 19.14, exactly as in [is_type_sig]: the result is already stripped
     below, so stripping first only moves the same peel to the cheap side of
     the normalization. *)
  let res = norm_bounded st "a type signature"
                         [TcEnv.AllowUnboundUniverses; TcEnv.EraseUniverses;
                          TcEnv.Beta; TcEnv.Iota;
                          TcEnv.UnfoldUntil delta_constant]
                         (Mono.strip (U.comp_result c)) in
  match (Mono.strip res).n with
  | Tm_fvar fv -> S.fv_eq_lid fv PC.prop_lid
  | _ -> false

and extract_type_abbrev (st:state) (nm:name) (lb:letbinding) : ML decl =
  let bs, body, _ = U.abs_formals lb.lbdef in
  (* An abbreviation may be *under-abstracted*: [let mymon = writer (list
     primitive_step)] has kind [Type -> Type] but no binders at all.  The IR
     has no partial application of a type constructor, so the missing
     arguments have to become binders here; left alone, the abbreviation is
     emitted with fewer parameters than its uses supply, and resolving it
     leaves the *definition's* own parameters free.  Section 5.5. *)
  let bs, body =
    let kbs, _ = U.arrow_formals lb.lbtyp in
    let n = List.length kbs - List.length bs in
    if n <= 0 then bs, body
    else
      let extra = List.splitAt (List.length kbs - n) kbs |> snd
                  |> List.map (fun (b:S.binder) ->
                       S.mk_binder (S.new_bv None b.binder_bv.sort)) in
      let args = extra |> List.map (fun (b:S.binder) -> S.as_arg (S.bv_to_name b.binder_bv)) in
      bs @ extra, U.mk_app body args
  in
  DType {
    dt_name   = nm;
    dt_params = bs |> List.collect (fun b ->
                  if Mono.is_type_param (tcenv st) b then [name_of_bv b.binder_bv] else []);
    dt_body   = TAbbrev (ty_of_typ st body);
    dt_flags  = [];
  }

(* Substitute the [Mono] arguments into the definition and re-abstract over the
   [Poly] ones.  Instead of taking the definition apart we apply it to a
   spine made of the concrete [Mono] arguments and fresh names for the [Poly]
   ones, and let the normalizer do the substitution: that copes uniformly with
   definitions that are eta-short, that have more binders than their type
   shows, or that are not syntactically lambdas at all.

   Applying a definition to a spine and re-abstracting is eta-expansion, and
   eta-expansion is only meaning-preserving when reaching the lambda is pure.
   [FStarC.TypeChecker.Cfg.cached_steps] is the counterexample:

     let cached_steps : unit -> ML prim_step_set =
       let memo = mk_ref (empty_prim_steps ()) in
       fun () -> ...

   The [ref] is allocated once, when the module is initialized, and every call
   shares it.  Eta-expanded to [fun x -> (let memo = ... in fun () -> ...) x]
   it is allocated per call and the memo table is always empty.  So the spine
   is cut at the definition's own lambdas unless the definition is a value,
   in which case duplicating it costs nothing. *)
and eta_safe (t:term) : ML bool =
  match (SS.compress (U.unascribe t)).n with
  | Tm_abs _ | Tm_fvar _ | Tm_name _ | Tm_bvar _
  | Tm_constant _ | Tm_uinst _ | Tm_type _ | Tm_arrow _ -> true
  | Tm_meta {tm} -> eta_safe tm
  | _ -> false

and specialize (st:state) (ty:typ) (def:term) (cs:list bclass) (margs:list (int & term))
               (n_holes:int)
  : ML (term & comp & list bclass & binders) =
  (* Section 3.2c.  Each [Mono] argument arrives abstracted over the same
     [n_holes] runtime values, so they are re-opened under *one* shared set of
     fresh binders -- a value that occurred in two arguments has to stay one
     parameter -- and those binders are appended to the specialization's own.
     The call site passes them in the same order. *)
  let hbs, margs =
    match margs with
    | (_, a0) :: _ when n_holes > 0 ->
      let bs0, _, _ = U.abs_formals a0 in
      let hbs = List.splitAt n_holes bs0 |> fst
                |> List.map (fun (b:S.binder) ->
                     S.mk_binder (S.new_bv None b.binder_bv.sort)) in
      let hargs = hbs |> List.map (fun (b:S.binder) -> S.as_arg (S.bv_to_name b.binder_bv)) in
      let inst (t:term) : ML term =
        norm_bounded st "a monomorphized argument"
                     [TcEnv.AllowUnboundUniverses; TcEnv.Beta]
                     (U.mk_app t hargs) in
      hbs, List.map (fun (i, t) -> (i, inst t)) margs
    | _ -> [], margs
  in
  let bs, c = U.arrow_formals_comp ty in
  (* How far the spine may run.  A value may be duplicated freely, so it takes
     the whole arrow; anything else only takes the binders its own lambdas
     absorb.  A [Mono] argument past that point has to be substituted all the
     same -- there is no other way to specialize on it -- and the definition's
     prefix is then re-evaluated per call; that has not come up, and rejecting
     it would rule out eta-short definitions that are pure in practice. *)
  let cut =
    if eta_safe def then List.length bs
    else
      let dbs, _, _ = U.abs_formals def in
      let n_lams = List.length dbs in
      margs |> List.fold_left (fun n (j, _) -> if j + 1 > n then j + 1 else n) n_lams
  in
  let rec go (i:int) (bs:binders) (cs:list bclass) (subst:list subst_elt)
             (spine:args) (poly:binders) (polycs:list bclass)
    : ML (args & binders & list bclass & comp) =
    match bs with
    | [] -> (List.rev spine, List.rev poly, List.rev polycs, SS.subst_comp subst c)
    | _ :: _ when i >= cut ->
      (* The residual arrow becomes the result type: the declaration is emitted
         as a value of function type and its callers apply it, which is what
         the source said. *)
      (List.rev spine, List.rev poly, List.rev polycs,
       S.mk_Total (U.arrow (SS.subst_binders subst bs) (SS.subst_comp subst c)))
    | b :: bs' ->
      let cls, cs' = match cs with
                     | [] -> Poly, []
                     | c :: cs' -> c, cs' in
      let sort = SS.subst subst b.binder_bv.sort in
      let marg = margs |> List.tryFind (fun (j, _) -> j = i) in
      match cls, marg with
      | Mono, Some (_, a) ->
        go (i + 1) bs' cs' (NT (b.binder_bv, a) :: subst)
           ((a, U.aqual_of_binder b) :: spine) poly polycs
      | _ ->
        (* A [Dropped] binder still has to bind, or the body would have a free
           variable; it is deleted from the emitted signature instead. *)
        let bv = { b.binder_bv with sort = sort } in
        let b' = { b with binder_bv = bv } in
        go (i + 1) bs' cs' subst
           ((S.bv_to_name bv, U.aqual_of_binder b) :: spine) (b' :: poly) (cls :: polycs)
  in
  let spine, poly, polycs, c = go 0 bs cs [] [] [] [] in
  (* Before the [Poly] binders: see the call site in {!app_of_fv'}. *)
  let poly = hbs @ poly in
  let polycs = List.map (fun _ -> Poly) hbs @ polycs in
  let applied = match spine with [] -> def | _ -> U.mk_app def spine in
  let benv = TcEnv.push_binders (tcenv st) poly in
  (* Section 30.8.  A match that takes apart a constructor binding a type has
     to fire here or never: after this, the field is a variable, and a variable
     standing for a type is what error 364 reports.  A syntactic projection is
     already handled -- section 30.5 reduces it in {!ty_of_typ} -- and the only
     difference between the two is how the source happens to spell the field,
     so they should not differ in what they support.

     The extra steps are as narrow as the trigger: [Zeta] and delta for the
     scrutinee heads *this body actually matches on*, and nothing else.  That
     is deliberate -- {!custard_norm_steps} excludes [Zeta] for reasons that
     have not stopped being true, and turning it on wholesale would unfold
     every recursive definition in reach.  Here it is on for a handful of
     named builders, and only when the shape that needs it is present.

     It may also fail, so it is allowed to: on a budget overrun the ordinary
     normalization runs instead, and the program gets whatever diagnostic it
     would have got before rather than a fresh error 365 from a reduction that
     was only ever an attempt to do better. *)
  let extra =
    match type_matched_heads benv applied with
    | [] -> None
    | lids ->
      let steps = custard_norm_steps |> List.filter (fun s ->
                    match s with TcEnv.Exclude TcEnv.Zeta -> false | _ -> true) in
      norm_optional_in benv (steps @ [TcEnv.Zeta;
                                      TcEnv.UnfoldUntil S.delta_constant;
                                      TcEnv.UnfoldOnly lids]) applied in
  (* The chain in the error names the definition, so "a body" is enough. *)
  let body =
    match extra with
    | Some b -> b
    | None -> norm_bounded_in st benv "a definition body" custard_norm_steps applied in
  (U.abs poly body None, c, polycs, poly)

and extract_letbinding (st:state) (l:Ident.lident) (nm:name) (lb:letbinding)
                       (is_rec:bool) (margs:list (int & term)) (n_holes:int) : ML decl =
  let cs = binder_classes st l in
  (* Lifted local functions are named after whatever encloses them. *)
  let saved_cur = !st.cur in
  st.cur := nm;
  let def, c, polycs, poly = Prof.timed "specialize"
    (fun () -> specialize st lb.lbtyp lb.lbdef cs margs n_holes) in
  let bs, body, rc = U.abs_formals def in
  bs |> List.iter (fun (b:S.binder) ->
          SMap.add st.defbinders (show b.binder_bv.index) ());
  (* [abs_formals] opens the binders under fresh names, but [c] still speaks of
     the ones [specialize] abstracted over.  Left unrelated, the two sets of
     names produce a signature whose result type mentions type variables no
     binder introduces -- fatal in the karamel backend. *)
  let rec realign (ps:binders) (bs:binders) : ML (list subst_elt) =
    match ps, bs with
    | p :: ps, b :: bs -> NT (p.binder_bv, S.bv_to_name b.binder_bv) :: realign ps bs
    | _ -> [] in
  let c = SS.subst_comp (realign poly bs) c in
  (* [U.abs] put the specialized binders first, so [polycs] lines up with the
     head of [bs]; any further binders come from the body's own lambdas and are
     not classified. *)
  let nth_class (i:int) : ML bool =
    let rec go (cs:list bclass) (i:int) : ML bool =
      match cs with
      | [] -> false
      | c :: cs -> if i <= 0 then Dropped? c else go cs (i - 1)
    in
    go polycs i in
  (* Binders past [polycs] come from the body's own lambdas and are filtered by
     the same predicate the call sites use. *)
  let n_poly = List.length polycs in
  let flags = bs |> List.mapi (fun i b ->
                nth_class i || (i >= n_poly && Mono.is_erased_binder (tcenv st) b)) in
  (* [abs_formals] sees through nested lambdas, so a definition written
     [let f x = fun y -> e] has more binders than its type has arrows.  Each
     such extra binder consumes one arrow of the result type -- and its
     effect, which is the one that matters at a call site.  *Every* extra
     binder does, including the ones [flags] drops: a binder that disappears
     from the emitted signature because it is erased still had an arrow in the
     source type, and leaving that arrow in the result type would make the
     declaration claim a larger arity than its body has (section 13.5). *)
  let n_extra = let n = List.length bs - n_poly in if n > 0 then n else 0 in
  (* Erased type binders carry no value but do parameterize the signature; the
     karamel backend resolves [TVar]s against this list, so they have to be
     recorded even though they take no runtime argument. *)
  let typars = bs |> List.collect (fun b ->
                 if Mono.is_type_param (tcenv st) b then [name_of_bv b.binder_bv] else []) in
  (* Reification and the result-type normalization below both compute the
     universe of a type that may be one of these binders -- [Tac 'b] in
     [FStar.Tactics.Util.map] is the smallest example -- so they have to run in
     an environment that binds them.  [bs] is what [abs_formals] opened and
     what [c] was realigned to, so it is the right set. *)
  let benv = Prof.timed "push_binders" (fun () -> TcEnv.push_binders (tcenv st) bs) in
  let bs = drop_flagged flags bs in
  (* A type binder that survived [drop_flagged] is the one {!Mono.keep_thunk}
     put back so that the definition does not become a value.  It carries no
     type at runtime and no value either, and its callers pass [()]
     ({!Mono.unit_binders}), so [unit] is both its honest type and the one that
     needs no coercion -- typing it by its sort would make it [any] and put an
     [Obj.magic] at every call. *)
  let binders = bs |> List.map (fun b ->
    { b_name = name_of_bv b.binder_bv;
      b_ty = if is_type_binder (tcenv st) b then TUnit
             else ty_of_typ st b.binder_bv.sort }) in
  (* The effect is the one of the *codomain*: [lbeff] is the effect of
     evaluating the lambda, which is always Tot.

     [head_ty] at *every* step, not only on the way in.  One arrow can hide
     behind an abbreviation whose codomain is another abbreviation, and then a
     peel that unfolds once consumes the first arrow, lands on the second name,
     and stops with binders still to account for -- leaving exactly the
     over-stated result type this whole comment block is about.
     [CDDL.Spec.EqTest.eq_test] is the case: it unfolds to [restricted_t t (fun
     x1 -> eq_test_for x1)], one arrow whose codomain is [eq_test_for], which
     unfolds to a second arrow.  Peeling two binders left one of them standing,
     and the definition was emitted with two parameters and a return type of
     [bool -> bool] over a body of type [bool] (section 26). *)
  let rec peel (n:int) (e:eff) (t:cty) : ML (eff & cty) =
    if n <= 0 then (e, t)
    else match head_ty st t 10 with
         | TArrow (_, e', r) -> peel (n - 1) e' r
         (* Not an arrow even unfolded, so [n] is over-stated by the caller
            and the type is returned as it was written rather than as it
            unfolds -- the abbreviation is the better name for it. *)
         | _ -> (e, t) in
  (* The arrows the extra binders consume can be hidden behind an
     abbreviation: [let st a = ctxt -> ML (a & ctxt)] makes [let get : st ctxt
     = fun s -> (s, s)] a one-binder definition whose declared type is an
     application, not an arrow.  So the peeling runs on the *term*, unfolding
     at each step, rather than on the [cty]: [ty_of_typ] emits an abbreviation
     by name, and a name is not a [TArrow], so a [cty]-level peel stops at the
     first one and leaves the arrows it should have consumed standing in the
     result type while their binders are also emitted -- a definition that
     claims a bigger arity than it has.  One unfolding is not enough either,
     because the abbreviation an unfolding exposes can be another one: Pulse's
     [cont_elab] unfolds to [frame:_ -> continuation_elaborator ...], and that
     is two further arrows behind a second name. *)
  let rec peel_typ (n:int) (e:eff) (t:typ) : ML (eff & cty) =
    if n <= 0 then (e, ty_of_typ st t)
    else
      let t = norm_bounded_in st benv "a result type"
                [TcEnv.AllowUnboundUniverses; TcEnv.Beta; TcEnv.Weak; TcEnv.HNF;
                 TcEnv.UnfoldUntil S.delta_constant]
                t in
      (* Section 19.7, exactly as in [Mono.arrow_formals_unfold]: what comes
         back is an arrow inside the ascription the elaborator wrote.  The
         stripped term is what the rest of this branch works on, and not
         merely what the tag is read off: [arrow_formals_comp] of an
         ascription yields *no* binders, so peeling zero of [n] and recursing
         on the same term is a loop that never ends. *)
      let t = Mono.strip t in
      match t.n with
      | Tm_arrow _ ->
        (* [arrow_formals_comp] flattens the *total* arrows only, so [c'] is
           either the group's own effectful comp or the first non-arrow. *)
        let bs, c' = U.arrow_formals_comp t in
        let k = List.length bs in
        if k > n
        then (E_Pure, ty_of_typ st (U.arrow (List.splitAt n bs |> snd) c'))
        (* Section 7.5, exactly as below: the binders run out on a reifiable
           comp, so what is left is the representation and the definition is
           pure. *)
        else if k = n && Effects.is_reifiable (tcenv st) (U.comp_effect_name c')
        then (E_Pure, ty_of_typ st (Effects.reify_comp (env_for_comp benv c') c'))
        else peel_typ (n - k) (eff_of_comp st c') (U.comp_result c')
      (* Not an arrow that the term level can see, so what is left is handed
         to the [cty]-level peel -- through {!head_ty}, because the arrows may
         still be behind an abbreviation *there*.  [FStar.Set.set a =
         restricted_t a (fun _ -> bool)] is the case: [restricted_t]'s second
         parameter is a value-indexed arity (section 18.2), so the application
         is a perfectly ordinary [TApp] of a two-parameter abbreviation whose
         body is an arrow -- and a [TApp] is not a [TArrow]. *)
      | _ -> peel n e (head_ty st (ty_of_typ st t) 10) in
  let res_typ = U.comp_result c in
  (* Section 7.5: a reifiable result type is replaced by its representation,
     and the definition itself becomes pure -- what it now returns is the
     closure the representation describes. *)
  let eff, ret =
    if Effects.is_reifiable (tcenv st) (U.comp_effect_name c)
    then peel n_extra E_Pure
              (ty_of_typ st (Effects.reify_comp (env_for_comp benv c) c))
    else peel_typ n_extra (eff_of_comp st c) res_typ in
  (* The body is reified against the residual effect of the lambdas
     [abs_formals] just opened, which is what actually describes it; [c] only
     agrees with it when there were no extra binders. *)
  let body =
    Prof.timed "reify" (fun () ->
    match rc with
    | Some rc -> Effects.maybe_reify (env_for_term benv body) body
                                     rc.residual_effect
    | None -> Effects.maybe_reify (env_for_term benv body) body
                                  (U.comp_effect_name c)) in
  (* Register the signature before extracting the body, so that a
     self-recursive call inside it finds an exact effect and an exact type
     instead of {!callee_eff}'s and {!callee_sig}'s conservative fallbacks.
     The body is a placeholder: nothing reads it, because [request] overwrites
     the whole declaration below, and this key is not joined to [st.order]. *)
  let () =
    match !st.chain with
    | key :: _ ->
      SMap.add st.emitted key (DLet {
        dl_name    = nm;
        dl_typars  = typars;
        dl_binders = binders;
        dl_ret     = ret;
        dl_eff     = eff;
        dl_body    = mk (EAbort "Custard: provisional body") ret eff;
        dl_flags   = [];
      })
    | [] -> () in
  let dl_body = expr_of_term st body in
  st.cur := saved_cur;
  DLet {
    dl_name    = nm;
    dl_typars  = typars;
    dl_binders = binders;
    dl_ret     = ret;
    dl_eff     = eff;
    dl_body    = dl_body;
    (* Provisional: [Simplify.scc] recomputes this from the final call graph,
       which is the only place the answer is knowable -- specialization and
       inlining change it in both directions.  Setting it here at all is just
       so that a self-recursive body is well-formed before then. *)
    dl_flags   = (if is_rec then [Rec [nm]] else []);
  }

(* A field whose contents belong in the constructor rather than behind a
   pointer to them (section 5.6).  A tuple is inlined without asking: [| Bar of
   a & b] is how F* source spells a two-argument constructor, and the pair it
   builds is never what the author meant to pay for (issue #4382).  Anything
   else has to say so with [@@@custard_inline_field] on the binder.

   The marker rides on the field's *type* so that it survives the passes that
   rewrite field lists without any of them having to know about it;
   [Simplify.inline_fields] strips every one. *)
and is_tuple_name (n:name) : bool =
  n.ns = ["FStar"; "Pervasives"; "Native"] && FStarC.Util.starts_with n.id "tuple"

and field_ty (st:state) (b:S.binder) : ML cty =
  let t = ty_of_typ st b.binder_bv.sort in
  let asked = U.has_attribute b.binder_attrs PC.custard_inline_field_attr in
  match t with
  | TApp (n, _) when asked || is_tuple_name n -> TInline t
  | _ -> t

and extract_inductive (st:state) (l:Ident.lident) (nm:name) (params:binders) : ML decl =
  (* [Sig_inductive_typ] stores its parameters closed, so a parameter whose
     sort mentions an earlier one -- a typeclass dictionary [{| monoid m |}]
     standing after its [m:Type] is the usual case -- still holds a de Bruijn
     index.  Anything that inspects a sort, [is_type_binder] first among them,
     has to see a name there instead. *)
  let params = SS.open_binders params in
  let _, ctors = TcEnv.datacons_of_typ (tcenv st) l in
  let n_params = List.length params in
  (* Only the *type* parameters become parameters of the target type; a value
     index has no counterpart in the target's type language. *)
  let ty_params = params |> List.collect (fun b ->
                    if keeps_param st l b then [name_of_bv b.binder_bv] else []) in
  let ctor (c:Ident.lident) : ML (name & list (string & cty)) =
    let _, ty = TcEnv.lookup_datacon (tcenv st) c in
    let bs, _ = U.arrow_formals_comp ty in
    (* Drop the inductive's own parameters, which are re-bound by every
       constructor's type under fresh names; the fields' types mention those
       fresh names, so rename them back to the ones the type declaration
       binds. *)
    let bs = if List.length bs >= n_params
             then let pre, bs = List.splitAt n_params bs in
                  let subst = List.map2 (fun (pb:S.binder) (b:S.binder) ->
                                NT (pb.binder_bv, S.bv_to_name b.binder_bv)) pre params in
                  SS.subst_binders subst bs
             else bs in
    (* Section 30.4.  [@@@monomorphize] classifies the binders of a *function*
       (section 3.2); a constructor field never reaches [Mono.classify], so
       the attribute on one is read by nothing at all.  It is worth saying so,
       because the advice attached to error 364 sends a reader here: told to
       mark the offending name, and finding that name is a [Type0] field, the
       obvious thing to try is to write it on the field -- and silence is
       indistinguishable from having fixed it. *)
    bs |> List.iter (fun (b:S.binder) ->
      if U.has_attribute b.binder_attrs PC.monomorphize_attr
      then E.log_issue0 E.Warning_CustardIneffectiveAttribute [
        text ("[@@monomorphize] on the field " ^
              Ident.string_of_id b.binder_bv.ppname ^ " of " ^
              Ident.string_of_lid c ^ " has no effect.");
        text "The attribute selects which *arguments of a function* are known \
              at specialization time (section 3.2).  A constructor field is \
              not an argument of anything, so there is no call site at which \
              a value for it could be known, and nothing reads the attribute.";
        text "A field of kind Type0 whose siblings' types mention it makes the \
              type an existential package rather than an instance of a \
              parameterized type, which section 30.3 records as unsupported. \
              There is no annotation that changes that." ]);
    (* The remaining binders are the constructor's fields; those without
       runtime content are deleted here, matching what [app_of_fv] does to a
       constructor application. *)
    let bs = drop_flagged (bs |> List.map (Mono.is_erased_binder (tcenv st))) bs in
    (name_of_lid c,
     bs |> List.map (fun b ->
       (name_of_bv b.binder_bv, field_ty st b)))
  in
  (* Section 5.5: whether the source said [{ a; b }] or [| C : ... -> t] does
     not decide the target representation -- the layout does -- but it is the
     one thing a *realization* mirrors, so it has to be recorded. *)
  let is_record =
    match TcEnv.lookup_sigelt (tcenv st) l with
    | Some se -> se.sigquals |> List.existsb (fun q -> RecordType? q)
    | None -> false in
  DType {
    dt_name   = nm;
    dt_params = ty_params;
    dt_body   = TVariant (ctors |> List.map ctor);
    dt_flags  = (if is_record then [SourceRecord] else []);
  }

(* -------------------------------------------------------------------- *)
(* Driving                                                              *)
(* -------------------------------------------------------------------- *)

let dump_specializations (st:state) : ML unit =
  BU.print_string "Custard specializations:\n";
  SMap.iter st.counts (fun l n ->
    if n > 1 then BU.print2 "  %s -> %s\n" l (show n));
  BU.print1 "  (total: %s)\n" (show (SMap.fold st.counts (fun _ n acc -> acc + n) 0))

(* {!Mono} runs below the extractor and so cannot read the chain out of a
   [state]; it holds a callback instead, and this is where it is filled in.
   A budget exhausted in a *type-level* normalization -- an arity spine, a
   binder's kind -- otherwise named no definition at all. *)
let install_chain_reporter (st:state) : ML unit =
  Mono.chain_reporter := (fun () -> request_chain st)

(* Whether a top-level definition has anything to extract, judged from its
   declared type alone: a ghost computation has no runtime meaning, and
   neither has one whose result is [prop], [slprop], [squash] or any other
   type the extraction must erase. *)
let erased_definition (st:state) (ty:typ) : ML bool =
  let _, c = U.arrow_formals_comp ty in
  U.is_ghost_effect (U.comp_effect_name c) ||
  TcUtil.must_erase_for_extraction (tcenv st) (U.comp_result c)

(* Section 19.11.  The same question asked of an explicit root, before it is
   requested rather than after.

   [--custard_entry_module] skips a specification quietly, because "whatever
   of this module is code" does not include one.  A root named one at a time
   used to be taken at its word, and taking a separation-logic predicate at
   its word means extracting it: [rep : tree -> sizet -> slprop] becomes a
   function whose argument is a recursive datatype, and the direct backend
   rejects that with error 368 -- a true statement about [tree] and a
   thoroughly misleading answer to what was asked, since nothing in the
   program holds a [tree] at runtime and the whole-module path compiles the
   same file.

   So the answer is given here, where the question was asked.  Not silently:
   a name the user typed that turns out to have no runtime content is worth
   saying out loud, which is the same reasoning that makes a misspelled
   [--custard_entry] an error rather than an empty output.

   The predicate is *not* [erased_definition], and the difference is the
   effect.  [non_info_norm] answers yes for [unit], which is right about the
   value and wrong about the definition: [main : unit -> ML unit] returns
   nothing and is the whole program.  A definition is contentless only when
   its result is non-informative *and* computing it does nothing -- a total
   or ghost computation.  An effectful one is called for what it does.

   A *type* is exempt for the same reason it is a legitimate root at all: its
   result is [Type], which is as non-informative as a result gets, and yet a
   type abbreviation named by [--custard_entry] is exactly what a
   hand-written realization needs emitted (see [tests/custard/TypeEntry.fst]). *)
let root_is_erased (st:state) (l:Ident.lident) : ML bool =
  let contentless (ty:typ) : ML bool =
    let _, c = U.arrow_formals_comp ty in
    not (is_type_sig st ty) &&
    (U.is_ghost_effect (U.comp_effect_name c) ||
     (U.is_pure_or_ghost_comp c &&
      TcUtil.must_erase_for_extraction (tcenv st) (U.comp_result c))) in
  match lookup_lid_typ st l with
  | Some ((_, ty), _) when contentless ty ->
    E.log_issue0 E.Error_CustardEntryNotFound [
      text ("Custard entry point " ^ Ident.string_of_lid l ^
            " is a specification, not code.");
      text "Its result type is erased -- ghost, prop, slprop or squash -- so \
            there is nothing to extract from it.";
      text "Name the function that uses it instead, or use \
            --custard_entry_module, which skips specifications."
    ];
    true
  | _ -> false

let run (st:state) (roots:list Ident.lident) (main:option Ident.lident)
         (per_module : S.modul -> ML unit) : ML program =
  let mark' (quiet:bool) (f:flag) (l:Ident.lident) : ML unit =
    let key = string_of_key { sk_lid = l; sk_args = []; sk_subst = []; sk_holes = 0 } in
    let _ = request st { sk_lid = l; sk_args = []; sk_subst = []; sk_holes = 0 } in
    (* Mark the root so backends know which symbols must survive.  A type is
       as good a root as a function: a hand-written realization that mentions,
       say, [FStarC_Range.t] needs the abbreviation emitted even though the
       extracted code unfolds it and never refers to it (section 8.2). *)
    match SMap.try_find st.emitted key with
    | Some (DLet d) ->
      SMap.add st.emitted key (DLet { d with dl_flags = f :: d.dl_flags })
    | Some (DType d) ->
      SMap.add st.emitted key (DType { d with dt_flags = f :: d.dt_flags })
    | Some (DExternal d) ->
      SMap.add st.emitted key (DExternal { d with dx_flags = f :: d.dx_flags })
    | Some _ -> ()
    | None when quiet -> ()
    | None ->
      (* Nothing was emitted for this root.  The driver's own check cannot see
         entry points in modules it has not loaded, so this is where a
         misspelled [--custard_entry] is caught. *)
      E.log_issue0 E.Error_CustardEntryNotFound [
        text ("Custard entry point " ^ Ident.string_of_lid l ^
              " did not produce a declaration.");
        text "It may be misspelled, or erased, or not defined in the module named."
      ] in
  let mark = mark' false in
  (* An entry point may name a *module* rather than a declaration.  That is the
     only way to reach a module that exists purely for its side effects -- 
     [FStarC.Hooks] defines nothing anyone calls and does nothing but install
     callbacks -- which the demand-driven loop would otherwise never load, and
     whose absence turns into a run-time failure ("callback not yet set")
     rather than a compile-time one. *)
  (* Before any of them is marked: a root is reached like anything else, and a
     projector or discriminator that some *other* root gets to first would be
     extracted, marked [Inline] and cached before its own turn came. *)
  roots |> List.iter (fun (l:Ident.lident) ->
    SMap.add st.roots (Ident.string_of_lid l) true);
  let modroots, roots =
    roots |> List.partition (fun (l:Ident.lident) ->
               Cons? (Loader.candidate_files st.deps (Ident.string_of_lid l))) in
  Prof.timed "run.modroots" (fun () ->
    modroots |> List.iter (fun (l:Ident.lident) ->
      st.env := Loader.ensure_loaded st.deps (tcenv st) (Ident.string_of_lid l)));
  (* [--custard_entry_module M] roots every top-level definition of [M], which
     is what [--extract_module] means for the other backends: the module is
     compiled as a *library*, not as the program reachable from one name.

     Quietly, unlike [--custard_entry].  Naming a definition that extracts to
     nothing is a mistake worth reporting; naming a *module* is not, because a
     module normally holds specifications and proofs alongside the code, and
     the request is "whatever of this is code", not "all of this is code".

     Only values.  A type is rooted by the definitions that use it, and under
     [--custard_monomorphize_types] a parametric type has no single instance
     to root anyway.  A projector or a discriminator is derived rather than
     written, and comes along with its type. *)
  Prof.timed "run.entry_modules" (fun () ->
    Options.custard_entry_modules () |> List.iter (fun (m:string) ->
      st.env := Loader.ensure_loaded st.deps (tcenv st) m;
      match TcEnv.modules (tcenv st)
            |> List.tryFind (fun (md:S.modul) -> Ident.string_of_lid md.name = m) with
      | None ->
        E.log_issue0 E.Error_CustardEntryNotFound [
          text ("Custard entry module " ^ m ^ " was not loaded.");
          text "It may be misspelled, or not among the input files."
        ]
      | Some md ->
        md.declarations |> List.iter (fun (se:S.sigelt) ->
          match se.sigel with
          | Sig_let {lbs=(_, lbs)}
            when not (se.sigquals |> List.existsb (function
                        | NoExtract | Projector _ | Discriminator _ -> true
                        | _ -> false)) ->
            lbs |> List.iter (fun lb ->
              match lb.lbname with
              (* A specification is a definition too.  [Null.live r : slprop]
                 and [Null.null_or_live] are proof-level, and rooting them
                 puts a function returning [unit] and doing nothing into the
                 output.  Nothing calls them, so only being a root keeps them
                 alive; asking whether the result has a runtime meaning is
                 what tells them apart from a genuine [unit] function. *)
              | Inr fv when not (erased_definition st lb.lbtyp) ->
                mark' true Root (S.lid_of_fv fv)
              | _ -> ())
          | _ -> ())));
  Prof.timed "run.roots" (fun () ->
    roots |> List.iter (fun l -> if not (root_is_erased st l) then mark Root l));
  Prof.timed "run.main" (fun () ->
    match main with Some l -> mark Entrypoint l | None -> ());
  (* A top-level [let] whose definiens is *effectful* is a module initializer:
     [let _ = clear ()] in [FStarC.Options], [let _ = register_pass ...] in
     [FStarC.Syntax.Resugar].  Nothing in the program refers to it, so the
     demand-driven loop never reaches it, and dropping it silently changes what
     the program does -- the registration never happens.  So once the closure
     is complete, every module it pulled in contributes its initializers, and
     that may pull in more modules, hence the fixpoint.

     Order: an initializer is requested after everything it can call, so it
     lands at the end of [st.order], and OCaml runs the emitted [let]s in the
     order they appear.  Across a split, the linker runs each unit's in
     dependency order.  What is *not* guaranteed is the order of two
     initializers in unrelated modules; F* gives no meaning to that either. *)
  let seen_inits : SMap.t unit = SMap.create 100 in
  let rec inits (fuel:int) : ML unit =
    if fuel <= 0 then () else
    let fresh = TcEnv.modules (tcenv st) |> List.collect (fun (md:S.modul) ->
      let m = Ident.string_of_lid md.name in
      match SMap.try_find seen_inits m with
      | Some () -> []
      | None -> SMap.add seen_inits m (); [md]) in
    if Nil? fresh then () else begin
      Prof.timed "inits" (fun () ->
       fresh |> List.iter (fun (md:S.modul) ->
        md.declarations |> List.iter (fun (se:S.sigelt) ->
          match se.sigel with
          | Sig_let {lbs=(_, lbs)} ->
            lbs |> List.iter (fun lb ->
              match lb.lbname with
              | Inr fv when not (U.is_pure_or_ghost_effect lb.lbeff) ->
                (* An initializer may erase to nothing at all, which is fine
                   and is not the user naming a missing entry point. *)
                mark' true Root (S.lid_of_fv fv)
              | _ -> ())
          | _ -> ())));
      (* Section 13: the same fixpoint carries the generated declarations,
         because generating one is itself a source of requests and so of newly
         loaded modules -- a plugin registration refers to the interpretation
         functions, whose module the program may otherwise never mention. *)
      Prof.timed "regemb" (fun () -> fresh |> List.iter per_module);
      inits (fuel - 1)
    end in
  Prof.timed "run.inits" (fun () -> inits 100);
  if Options.custard_dump_specializations () then dump_specializations st;
  Prof.timed "run.collect" (fun () ->
    List.rev !st.order |> List.collect (fun key ->
      match SMap.try_find st.emitted key with
      | Some d -> [d]
      | None -> []))

let request_lid (st:state) (l:Ident.lident) : ML name =
  request st { sk_lid = l; sk_args = []; sk_subst = []; sk_holes = 0 }

(* Section 13.  A generated declaration is not the translation of any F*
   definition, so it has no specialization key; the key it is filed under is
   its own name, which is unique by construction and cannot collide with a
   real key (those always name a lid and a list of arguments). *)
let emit (st:state) (key:string) (d:decl) : ML unit =
  match SMap.try_find st.emitted key with
  | Some _ -> ()
  | None ->
    SMap.add st.emitted key d;
    st.order := key :: !st.order

let emitted (st:state) (key:string) : ML bool =
  Some? (SMap.try_find st.emitted key)

let imports (st:state) : ML (list (decl & option type_info)) = List.rev !st.imports

let link_homes (st:state) : ML (list string) = Unit.link_homes st.links

let exported_keys (st:state) : ML (list (string & string)) =
  SMap.fold st.names (fun key nm acc -> (string_of_name nm, key) :: acc) []

let loaded_digests (_:state) : ML (list (string & string)) = Loader.loaded_digests ()
