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
module Ident  = FStarC.Ident
module Loader = FStarC.Custard.Loader
module Mono   = FStarC.Custard.Mono
module Builtins = FStarC.Custard.Builtins
module GenSym = FStarC.GenSym
module N      = FStarC.TypeChecker.Normalize
module PC     = FStarC.Parser.Const
module ExtractAs = FStarC.Parser.Const.ExtractAs
module S      = FStarC.Syntax.Syntax
module SMap   = FStarC.SMap
module Unit   = FStarC.Custard.Unit
module SS     = FStarC.Syntax.Subst
module TcEnv  = FStarC.TypeChecker.Env
module U      = FStarC.Syntax.Util
module UF     = FStarC.Syntax.Unionfind
module TcUtil = FStarC.TypeChecker.Util
module Range = FStarC.Range


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

let key_norm_steps : list TcEnv.step = [
  TcEnv.DontUnfoldAttr [no_specialize_lid];
  TcEnv.Weak;
  TcEnv.AllowUnboundUniverses;
  TcEnv.EraseUniverses;
  TcEnv.Beta;
  TcEnv.Iota;
  TcEnv.Primops;
  TcEnv.Unascribe;
  TcEnv.Unmeta;
  TcEnv.UnfoldUntil delta_constant;
]

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
let subst_norm_steps : list TcEnv.step =
  TcEnv.Weak :: TcEnv.HNF :: key_norm_steps

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
  | Const_real r        -> r ^ "R"
  | Const_char c        -> "'" ^ show (FStarC.Util.int_of_char c) ^ "'"
  | Const_string (s, _) -> "\"" ^ s ^ "\""
  (* The width and signedness are part of the constant: [0uy] and [0ul] are
     different values of different types, and [const_to_string] prints both as
     "0". *)
  | Const_int (s, sw)   ->
    s ^ (match sw with
         | None -> ""
         | Some (s, w) ->
           (match s with Unsigned -> "u" | Signed -> "s") ^
           (match w with Int8 -> "8" | Int16 -> "16" | Int32 -> "32"
                       | Int64 -> "64" | Sizet -> "sz"))
  (* A range is a position, so it cannot appear in a key: two identical calls
     on different lines would specialize twice, and the key would change
     whenever anything above it moved. *)
  | Const_range _       -> "<range>"
  | Const_range_of      -> "range_of"
  | Const_set_range_of  -> "set_range_of"
  | Const_reify lopt    ->
    "reify" ^ (match lopt with None -> "" | Some l -> "<" ^ Ident.string_of_lid l ^ ">")
  | Const_reflect l     -> "reflect<" ^ Ident.string_of_lid l ^ ">"

let rec key_of_term (t:S.term) : ML string =
  match (SS.compress t).n with
  | Tm_bvar bv          -> "@" ^ show bv.index
  (* A [Tm_name] is bound outside the term, so its identity is the gensym
     index and there is nothing canonical to print.  A key containing one is
     not portable across runs; see section 12.3. *)
  | Tm_name bv          -> "%" ^ Ident.string_of_id bv.ppname ^ "#" ^ show bv.index
  | Tm_fvar fv          -> Ident.string_of_lid (S.lid_of_fv fv)
  | Tm_uinst (t, _)     -> key_of_term t
  | Tm_constant c       -> key_of_const c
  | Tm_type _           -> "Type"
  | Tm_abs {b; body}    -> "(fun " ^ key_of_binder b ^ " -> " ^ key_of_term body ^ ")"
  | Tm_arrow {b; comp}  -> "(" ^ key_of_binder b ^ " -> " ^ key_of_comp comp ^ ")"
  | Tm_refine {b; phi}  -> "({" ^ key_of_term b.sort ^ "|" ^ key_of_term phi ^ "})"
  | Tm_app {hd; arg}    -> "(" ^ key_of_term hd ^ " " ^ key_of_arg arg ^ ")"
  | Tm_match {scrutinee; brs} ->
    "(match " ^ key_of_term scrutinee ^ " with" ^
    (brs |> List.map key_of_branch |> String.concat "") ^ ")"
  (* [Unascribe] and [Unmeta] are in [key_norm_steps], so these are only
     reached on a term the normalizer declined to touch; either way neither
     node changes what the term means. *)
  | Tm_ascribed {tm}    -> key_of_term tm
  | Tm_meta {tm}        -> key_of_term tm
  | Tm_let {lbs = (r, lbs); body} ->
    "(let" ^ (if r then " rec" else "") ^
    (lbs |> List.map key_of_lb |> String.concat " and ") ^
    " in " ^ key_of_term body ^ ")"
  | Tm_uvar (u, _)      -> "?" ^ show (UF.uvar_id u.ctx_uvar_head)
  | Tm_quoted (t, _)    -> "(quote " ^ key_of_term t ^ ")"
  | Tm_lazy _ ->
    (* One step only: [unlazy] on something that does not unfold gives back
       what it was handed, and we must not loop. *)
    (match (SS.compress (U.unlazy t)).n with
     | Tm_lazy _ -> "<lazy>"
     | _ -> key_of_term (U.unlazy t))
  | Tm_unknown          -> "_"
  | Tm_delayed _        -> "<delayed>"  (* unreachable: compressed above *)

(* The qualifier is dropped: whether an argument was written [#a] or [a] does
   not change the value, and the two must not key differently.  Attributes are
   dropped for the same reason. *)
and key_of_binder (b:S.binder) : ML string = key_of_term b.binder_bv.sort

and key_of_arg (a:S.arg) : ML string = key_of_term (fst a)

and key_of_comp (c:S.comp) : ML string =
  match c.n with
  | Total t  -> key_of_term t
  | GTotal t -> "GTot " ^ key_of_term t
  | Comp ct  ->
    Ident.string_of_lid ct.effect_name ^ " " ^ key_of_term ct.result_typ ^
    (ct.effect_args |> List.map (fun a -> " " ^ key_of_arg a) |> String.concat "")

and key_of_branch (br:S.branch) : ML string =
  let (p, w, e) = br in
  " | " ^ key_of_pat p ^
  (match w with None -> "" | Some w -> " when " ^ key_of_term w) ^
  " -> " ^ key_of_term e

and key_of_pat (p:S.pat) : ML string =
  match p.v with
  | Pat_constant c   -> key_of_const c
  (* Pattern variables are positional, so their names carry no information. *)
  | Pat_var _        -> "_"
  | Pat_dot_term _   -> "."
  | Pat_cons (fv, _, ps) ->
    "(" ^ Ident.string_of_lid (S.lid_of_fv fv) ^
    (ps |> List.map (fun (p, _) -> " " ^ key_of_pat p) |> String.concat "") ^ ")"

and key_of_lb (lb:S.letbinding) : ML string =
  (match lb.lbname with
   | Inl _ -> "@"                        (* recursive group binders are positional *)
   | Inr fv -> Ident.string_of_lid (S.lid_of_fv fv)) ^
  " : " ^ key_of_term lb.lbtyp ^ " = " ^ key_of_term lb.lbdef

let string_of_key (k:spec_key) : ML string =
  Ident.string_of_lid k.sk_lid ^
  (if k.sk_holes = 0 then "" else "/" ^ show k.sk_holes) ^
  (k.sk_args |> List.map (fun (i, t) -> "#" ^ show i ^ "=" ^ key_of_term t)
             |> String.concat "")

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
  lifted:  SMap.t (name & list cty & list binder & cty);
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
}

let init (deps:Dep.deps) (env:TcEnv.env) : ML state = {
  deps    = deps;
  env     = mk_ref env;
  names   = SMap.create 100;
  emitted = SMap.create 100;
  order   = mk_ref [];
  classes = SMap.create 100;
  counts  = SMap.create 100;
  suffixes = SMap.create 100;
  fuel    = mk_ref (Options.custard_fuel ());
  chain   = mk_ref [];
  lifted  = SMap.create 20;
  cur     = mk_ref ({ ns = []; id = "custard"; spec = None });
  letdefs = SMap.create 100;
  effletdefs = SMap.create 100;
  links   = Unit.load_links (Options.custard_links ());
  imports = mk_ref [];
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
  TcEnv.Primops;
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

let norm_bounded (st:state) (what:string) (steps:list TcEnv.step) (t:term) : ML term =
  try N.with_budget (Options.custard_norm_budget ())
                    (fun () -> N.normalize steps (tcenv st) t)
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

(* -------------------------------------------------------------------- *)
(* Loading                                                              *)
(* -------------------------------------------------------------------- *)

(* A definition may live in a module the driver never loaded; pull it in.  This
   is the on-demand part of section 4.1. *)
let ensure_lid_available (st:state) (l:Ident.lident) : ML unit =
  let m = Ident.nsstr l in
  if m <> "" && not (Loader.module_is_loaded st.deps (tcenv st) m) then
    st.env := Loader.ensure_loaded st.deps (tcenv st) m

(* -------------------------------------------------------------------- *)
(* Names                                                                *)
(* -------------------------------------------------------------------- *)

let name_of_lid (l:Ident.lident) : ML name = {
  ns   = List.map Ident.string_of_id (Ident.ns_of_lid l);
  id   = Ident.string_of_id (Ident.ident_of_lid l);
  spec = None;
}

let name_of_bv (b:bv) : ML string =
  uniq (Ident.string_of_id b.ppname) b.index

(* A readable suffix for a specialization: the head symbol of its first [Mono]
   argument is almost always the interesting one (the type, or the instance). *)
let hint_of_args (args:list (int & term)) : ML (option string) =
  match args with
  | [] -> None
  | (_, t) :: _ ->
    let hd, _ = U.head_and_args_full t in
    (match (U.un_uinst (SS.compress hd)).n with
     | Tm_fvar fv -> Some (Ident.string_of_id (Ident.ident_of_lid (S.lid_of_fv fv)))
     | Tm_constant (Const_int (s, _)) -> Some s
     | Tm_constant (Const_bool b) -> Some (if b then "true" else "false")
     | _ -> None)

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
    match hint_of_args args with
    | Some h when claim h -> Some h
    | Some h -> Some (h ^ "_" ^ show n)
    | None -> Some (show n)

(* -------------------------------------------------------------------- *)
(* Effects                                                              *)
(* -------------------------------------------------------------------- *)

let eff_of_comp (st:state) (c:comp) : ML eff = Effects.of_comp (tcenv st) c

(* Applying [n] arguments to something of type [ty] runs the effects of the
   first [n] arrows.  This is how a call through a *variable* -- a function
   parameter, or a local closure -- gets its effect: there is no declaration to
   consult, only the type.  When the type is not arrow-shaped (typically
   [TAny]) we have to assume the worst, or section 7.3 would let us drop a call
   we know nothing about. *)
let rec apply_eff (ty:cty) (n:int) : ML eff =
  if n <= 0 then E_Pure
  else
    match ty with
    | TArrow (_, e, r) -> join_eff e (apply_eff r (n - 1))
    | _ -> E_Impure

let rec apply_result (ty:cty) (n:int) : ML cty =
  if n <= 0 then ty
  else
    match ty with
    | TArrow (_, _, r) -> apply_result r (n - 1)
    | _ -> TAny

(* -------------------------------------------------------------------- *)
(* Requests                                                             *)
(* -------------------------------------------------------------------- *)

(* Section 3.3, step 3: this is where the demand-driven loop lives. *)
let rec request (st:state) (k:spec_key) : ML name =
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
                extract_lid st l nm k.sk_subst k.sk_holes) in
      st.chain := saved;
      SMap.add st.emitted key d;
      st.order := key :: !st.order;
      nm

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
    let d =
      match e.ue_decl with
      | DType dt    -> DType { dt with dt_flags = Imported u :: dt.dt_flags }
      | DLet dl     -> DLet  { dl with dl_flags = Imported u :: dl.dl_flags }
      | DExternal dx -> DExternal { dx with dx_flags = Imported u :: dx.dx_flags }
      | DExn de     -> DExn de
    in
    let nm = name_of_decl d in
    SMap.add st.names key nm;
    st.imports := (d, e.ue_type) :: !st.imports;
    if Options.custard_dump_specializations () then
      BU.print2 "Custard: %s comes from unit %s\n" key u;
    Some nm

(* Section 3.6: the budget is checked *before* the definition is looked up and
   before its body is normalized, so that a diverging specialization is cut off
   after a negligible amount of work. *)
and check_budget (st:state) (k:spec_key) : ML unit =
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
    ]

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
         de_args = bs |> List.map (fun b -> ty_of_typ st b.binder_bv.sort) }

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
  let key = Ident.string_of_lid l in
  match SMap.try_find st.classes key with
  | Some cs -> cs
  | None ->
    ensure_lid_available st l;
    let cs =
      match TcEnv.lookup_sigelt (tcenv st) l with
      | Some se ->
        (match se.sigel with
         | Sig_let {lbs=(_, lbs)} ->
           (match lbs |> List.tryFind (fun lb ->
                    match lb.lbname with
                    | Inr fv -> Ident.lid_equals (S.lid_of_fv fv) l
                    | Inl _ -> false) with
            | Some lb -> classify (tcenv st) (se.sigattrs @ lb.lbattrs) lb.lbtyp
            | None -> [])
         | Sig_declare_typ {t} -> classify (tcenv st) se.sigattrs t
         | _ -> [])
      | None -> []
    in
    SMap.add st.classes key cs;
    cs

(* -------------------------------------------------------------------- *)
(* Types                                                                *)
(* -------------------------------------------------------------------- *)

and ty_of_typ (st:state) (t:typ) : ML cty =
  let t = SS.compress t in
  match t.n with
  | Tm_bvar b
  | Tm_name b -> TVar (name_of_bv b)

  | Tm_uinst (t, _) -> ty_of_typ st t

  (* As with {!erasable_app}, a non-informative type is collapsed *before* its
     head is requested.  Requesting it would emit its whole definition -- and
     recursively that of every type it mentions -- for a value that cannot
     exist at runtime; [Pulse.Lib.HashTable.Spec.repr_t] and its [Seq]/[nat]
     entourage are the motivating example. *)
  | Tm_fvar _
  | Tm_app _ when TcUtil.must_erase_for_extraction (tcenv st) t -> TUnit

  | Tm_fvar fv -> ty_of_fv st fv []

  | Tm_arrow _ ->
    let bs, c = U.arrow_formals_comp t in
    (* Section 7.2: a codomain of the form [stt b p q] contributes [b] as the
       result type and promotes the arrow to [E_Impure]. *)
    let res = ty_of_typ st (Effects.result_typ (tcenv st) c) in
    let e = eff_of_comp st c in
    let bs = drop_flagged (Mono.erased_binders (tcenv st) t) bs in
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
    (match Effects.impure_effect_result (tcenv st) t with
     (* Section 7.2, rule 1: [stt b p q] is represented by [b]. *)
     | Some a -> ty_of_typ st a
     | None ->
       let hd, args = U.head_and_args_full t in
       (match (U.un_uinst hd).n with
        | Tm_fvar fv ->
          (* A type constructor's arguments survive into the [cty] exactly when
             they are types: an index like the [n] of [vec n] has no
             counterpart in the target's type language. *)
          let keep = match TcEnv.try_lookup_lid (tcenv st) (S.lid_of_fv fv) with
                     | Some ((_, k), _) -> Mono.type_binders (tcenv st) k
                                           |> List.map (fun b -> not b)
                     | None -> [] in
          ty_of_fv st fv (drop_flagged keep args |> List.map fst)
        | _ -> TAny))

  | Tm_refine {b} -> ty_of_typ st b.sort
  | Tm_ascribed {tm} -> ty_of_typ st tm
  | Tm_meta {tm} -> ty_of_typ st tm

  (* A type in type position: this is where a higher-kinded or dependent type
     would land.  M1 does not represent those. *)
  | Tm_type _
  | _ -> TAny

(* Type constructors are compiled uniformly in their parameters (section 5.0),
   so an inductive is never specialized: it is always requested with an empty
   key. *)
and ty_of_fv (st:state) (fv:fv) (args:list term) : ML cty =
  let l = S.lid_of_fv fv in
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
  | Const_int (s, w) -> Some (CInt (s, w))
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

and expr_of_term (st:state) (t:term) : ML expr =
  let t = SS.compress t in
  match t.n with
  | Tm_constant c ->
    (match constant_of_sconst c with
     | Some c -> mk (EConst c) (ty_of_constant st c) E_Pure
     | None -> unit_expr)

  | Tm_bvar b
  | Tm_name b ->
    (match lifted_ref st b with
     | Some e -> e
     | None -> mk (EVar (name_of_bv b)) (ty_of_typ st b.sort) E_Pure)

  | Tm_uinst (t, _) -> expr_of_term st t

  | Tm_fvar fv -> app_of_fv st fv []

  | Tm_abs _ ->
    let bs, body, _ = U.abs_formals t in
    let body = expr_of_term st body in
    let bs =
      let flags = bs |> List.map (Mono.is_erased_binder (tcenv st)) in
      (* Same guard as [Mono.erased_binders]: a lambda whose binders all vanish
         would become a value, running its effects where it is built. *)
      let flags = if List.for_all (fun b -> b) flags && not (is_pure body.eff)
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
     | _ ->
       let hd_term = hd in
       let erasable = match (SS.compress hd_term).n with
                      | Tm_name bv -> erasable_result st bv.sort (List.length args)
                      | _ -> false in
       if erasable then unit_expr else
       let hd = expr_of_term st hd in
       (* No declaration to consult, so the filter has to come from the head's
          own type; a head we cannot type is left alone. *)
       let flags = match (SS.compress hd_term).n with
                   | Tm_name bv -> Mono.erased_binders (tcenv st) bv.sort
                   | _ -> [] in
       let args = drop_flagged flags args |> List.map fst |> List.map (expr_of_term st) in
       (match args with
        | [] -> hd
        | _ ->
          let n = List.length args in
          let e = List.fold_left (fun e a -> join_eff e a.eff)
                                 (join_eff hd.eff (apply_eff hd.ty n)) args in
          mk (EApp (hd, args)) (apply_result hd.ty n) e))

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
       let e2 = expr_of_term st body in
       mk (ELet (name_of_bv bv, ty_of_typ st lb.lbtyp, e1, e2)) e2.ty (join_eff e1.eff e2.eff)
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

  (* Types and proofs in term position are erased. *)
  | Tm_type _ -> unit_expr
  | _ -> unit_expr

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
  | Some (nm, tyargs, caps, ty) ->
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
       Some (mk (EApp (hd, args)) (apply_result ty n) E_Pure))

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
    let free = dedup free |> List.sortWith (fun (x:S.bv) (y:S.bv) -> x.index - y.index) in
    let tyvars, valvars = List.partition (is_type_bv st) free in
    let typars = tyvars |> List.map name_of_bv in
    let tyargs = typars |> List.map (fun v -> TVar v) in
    let caps = valvars |> List.map (fun (v:S.bv) ->
                 { b_name = name_of_bv v; b_ty = ty_of_typ st v.sort }) in
    (* One entry per member, all registered before any body is translated: a
       call from one member to another must find the lifted name, and so must
       a self-call. *)
    let entries = lbs |> List.map (fun lb ->
      let bv = Inl?.v lb.lbname in
      let base = (!st.cur).id ^ "__" ^ Ident.string_of_id bv.ppname in
      let ns = (!st.cur).ns in
      let n = (match SMap.try_find st.counts base with None -> 0 | Some n -> n) in
      SMap.add st.counts base (n + 1);
      let nm = { ns = ns; id = base; spec = (if n = 0 then None else Some (show n)) } in
      let xs, _, _ = U.abs_formals lb.lbdef in
      let ret, eff = local_result st lb.lbtyp xs in
      let arg_binders = xs |> List.map (fun (b:S.binder) ->
                          { b_name = name_of_bv b.binder_bv;
                            b_ty   = ty_of_typ st b.binder_bv.sort }) in
      let binders = caps @ arg_binders in
      let ty = List.fold_right (fun (b:binder) (t, e) -> (TArrow (b.b_ty, e, t), E_Pure))
                               binders (ret, eff) |> fst in
      SMap.add st.lifted (name_of_bv bv) (nm, tyargs, caps, ty);
      (lb, nm, binders, ret, eff)) in
    entries |> List.iter (fun (lb, nm, binders, ret, eff) ->
      let _, def_body, _ = U.abs_formals lb.lbdef in
      let d = DLet {
        dl_name    = nm;
        dl_typars  = typars;
        dl_binders = binders;
        dl_ret     = ret;
        dl_eff     = eff;
        dl_body    = expr_of_term st def_body;
        (* Provisional, exactly as for a top-level definition: [Simplify.scc]
           recomputes it from the final call graph. *)
        dl_flags   = [Rec (entries |> List.map (fun (_, nm, _, _, _) -> nm))];
      } in
      (* Not a specialization of anything -- no source lid names it -- so it
         gets a key of its own, which nothing will ever request. *)
      let key = "<local>" ^ mangled_name nm in
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
  let eff, ret = peel (List.length xs - List.length bs)
                      (eff_of_comp st c) (ty_of_typ st (U.comp_result c)) in
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
  if erasable_app st (TcEnv.try_lookup_lid (tcenv st) l) (List.length args)
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
and erasable_app (st:state) (lookup:option ((universes & typ) & Range.range)) (n_args:int)
  : ML bool =
  match lookup with
  | None -> false
  | Some ((_, ty), _) -> erasable_result st ty n_args

and erasable_result (st:state) (ty:typ) (n_args:int) : ML bool =
  let bs, c = U.arrow_formals_comp ty in
  (* Over-application leaves an unknown residue, and under-application leaves
     a closure; only an exactly saturated call has a result we can judge. *)
  List.length bs = n_args &&
  U.is_pure_or_ghost_comp c &&
  TcUtil.must_erase_for_extraction (tcenv st) (U.comp_result c)

(* A primitive is a function in F* but an operator in the IR, so an
   under-applied use has to be eta-expanded rather than passed along. *)
and prim_app (st:state) (l:Ident.lident) (n:int)
             (f : list cty -> list expr -> ML expr) (args:args) : ML expr =
  let decl_ty = match TcEnv.try_lookup_lid (tcenv st) l with
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
                 keep_flagged (Mono.type_binders (tcenv st) ty) args
                 |> List.map fst |> List.map (ty_of_typ st)
               | None -> [] in
  let args = drop_flagged flags args |> List.map fst |> List.map (expr_of_term st) in
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
    | _ -> mk (EApp (e, extra)) (apply_result e.ty (List.length extra))
              (List.fold_left (fun x a -> join_eff x a.eff)
                              (apply_eff e.ty (List.length extra)) extra)

(* Which of a constructor's arguments do not survive, positionally.

   Two separate reasons.  The leading [num_ty_params] arguments are the
   *inductive's* parameters, which every constructor re-binds but which the
   emitted type does not store -- [extract_inductive] drops all of them, so a
   constructor application and a constructor pattern have to drop exactly the
   same ones or they disagree about the arity.  Erasure alone is not the same
   test: a parameter can be a typeclass dictionary, which is not erased where
   it stands but is still not a field.  The remaining arguments are the real
   fields, and those go by erasure as usual. *)
and ctor_dropped_flags (st:state) (l:Ident.lident) : ML (list bool) =
  let n_params = match TcEnv.lookup_sigelt (tcenv st) l with
                 | Some { sigel = Sig_datacon {num_ty_params} } -> num_ty_params
                 | _ -> 0 in
  match TcEnv.try_lookup_lid (tcenv st) l with
  | Some ((_, ty), _) ->
    Mono.erased_binders (tcenv st) ty
    |> List.mapi (fun i erased -> erased || i < n_params)
  | None -> []

and repeat_unit (n:int) : ML (list unit) =
  if n <= 0 then [] else () :: repeat_unit (n - 1)

and app_of_fv' (st:state) (fv:fv) (args:args) : ML expr =
  let l = S.lid_of_fv fv in
  ensure_lid_available st l;
  if is_data_ctor fv
  then
    let nm = request st { sk_lid = l; sk_args = []; sk_subst = []; sk_holes = 0 } in
    let flags = ctor_dropped_flags st l in
    let ufs = match TcEnv.try_lookup_lid (tcenv st) l with
              | Some ((_, ty), _) -> Mono.unit_binders (tcenv st) ty
              | None -> [] in
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
       passed after the [Poly] ones, in the order [specialize] binds them. *)
    let rest = rest @ List.map (fun (v:S.bv) -> expr_of_term st (S.bv_to_name v)) holes in
    match rest with
    | [] -> hd
    | _ ->
      let e = List.fold_left (fun e a -> join_eff e a.eff)
                             (callee_eff st (string_of_key key) (List.length rest)) rest in
      mk (EApp (hd, rest)) (apply_result hd_ty (List.length rest)) e

(* A constructor application's type is the constructor's result type with the
   inductive's parameters instantiated -- which the spine supplies, since the
   parameters come first.  karamel needs it: [ECons] carries the type of the
   value being built, and an [any] there makes its datatype passes fail. *)
and ctor_result_ty (st:state) (l:Ident.lident) (spine:args) : ML cty =
  match TcEnv.try_lookup_lid (tcenv st) l with
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
  let ub = match TcEnv.try_lookup_lid (tcenv st) l with
           | Some ((_, ty), _) -> Mono.unit_binders (tcenv st) ty
           | None -> [] in
  let rec go (cs:list bclass) (uf:list bool) (sp:args) : ML (list bool) =
    match cs, sp with
    | [], _ -> []
    | c :: cs, _ :: sp ->
      let u, uf = match uf with
                  | u :: uf -> (u, uf)
                  | [] -> (false, []) in
      if Poly? c then u :: go cs uf sp else go cs uf sp
    | _, [] -> [] in
  go cs ub spine

(* The type arguments of a call, in the order [extract_letbinding] records them
   in [dl_typars]: source order, restricted to the type binders that survived
   as parameters rather than being specialized away. *)
and call_type_args (st:state) (l:Ident.lident) (cs:list bclass) (spine:args) : ML (list cty) =
  let tflags = match TcEnv.try_lookup_lid (tcenv st) l with
               | Some ((_, ty), _) -> Mono.type_binders (tcenv st) ty
               | None -> [] in
  let rec go (cs:list bclass) (tf:list bool) (sp:args) : ML (list cty) =
    match cs, tf, sp with
    | c :: cs, t :: tf, (a, _) :: sp ->
      if t && not (Mono? c)
      then ty_of_typ st a :: go cs tf sp
      else go cs tf sp
    | _ -> [] in
  go cs tflags spine

(* The callee's signature, instantiated at this call site.  It is available
   because requests are depth-first; a recursive call is the exception, and
   falls back to [TAny]. *)
and callee_sig (st:state) (key:string) (tyargs:list cty) : ML cty =
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
  | _ -> TAny

(* Section 3.2: the two ways a call site can fail to be specializable.
   Returns the key arguments, the terms to substitute into the body, and the
   remaining spine. *)
and split_mono_args (st:state) (l:Ident.lident) (cs:list bclass) (spine:args)
  : ML (list (int & term) & list (int & term) & args & list S.bv) =
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
       rest, holes)

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
      text ("Mark " ^ Ident.string_of_id v.ppname ^ " with [@@monomorphize] in \
            the enclosing definition so that it, too, is known at \
            specialization time.  (A runtime *value* would be passed at \
            runtime instead -- see section 3.2c -- but a type is erased, so \
            there would be nothing to pass.)")
    ]

(* The effect of a call: we know it exactly, because the callee has already
   been extracted by the time we get here (requests are depth-first). *)
(* A *partially* applied callee is a closure, and building a closure is pure
   however impure calling it will be. *)
and callee_eff (st:state) (key:string) (n_args:int) : ML eff =
  match SMap.try_find st.emitted key with
  | Some (DLet l) ->
    if n_args >= List.length l.dl_binders then l.dl_eff else E_Pure
  (* An external's declared arrow type is the whole contract we have with its
     realization, exactly as for a call through a variable -- and it is the
     same contract the ML pipeline and karamel work from.  Treating every
     external as impure instead would put a barrier around [Prims.op_Addition]
     and every other arithmetic primitive, which are all [Tot].  [apply_eff]
     still answers [E_Impure] when the type is not an arrow, so a symbol we
     genuinely know nothing about ([dx_ty = TAny]) stays opaque. *)
  | Some (DExternal x) -> apply_eff x.dx_ty n_args
  | _ -> E_Pure

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
  let se = TcEnv.lookup_sigelt (tcenv st) l |> Option.map fixup_extract_as in
  (* A rule declared by the definition's own attributes wins over the built-in
     table, so that a program can override a rule it does not like. *)
  let rule = match se with
             | Some se ->
               (match Builtins.rule_of_attributes se.sigattrs with
                | Some r -> Some r
                | None -> Builtins.lookup_rule l)
             | None -> Builtins.lookup_rule l in
  match rule with
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
                        (Ident.ns_of_lid l |> List.map Ident.string_of_id)) ->
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
                dx_header = None; dx_flags = [] }
  | Some se ->
    let d = extract_sigelt st l nm margs n_holes se in
    let d = if is_opaque || is_realized then with_no_newtype d else d in
    (* [inline_for_extraction] on a type in a realized module means what it
       says: the alias is not in the hand-written .ml, and the realization
       expects to be named through what it stands for.  [FStarC.PSMap.psmap]
       is that; [FStar.Dyn.dyn], which the realization does define, is not. *)
    let inlined = se.sigquals |> List.existsb (fun q -> q = S.Inline_for_extraction) in
    let d = if is_realized && not inlined then with_realized d else d in
    if is_inlinable se then with_inline d else d

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
  | _ -> se

(* The projectors and discriminators F* derives for an inductive are one field
   read or one tag test each; leaving them as calls would make the output
   unreadable and, in C, slow. *)
(* [inline_for_extraction] in a realized module means the realization does not
   define the symbol and expects to be named through what it stands for.  A
   type abbreviation counts as one whether or not it says so: F* represents it
   as a [Sig_let] whose result is a [Type], and a type is not a value. *)
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
  se.sigquals |> List.existsb (fun q ->
    match q with
    | S.Projector _ | S.Discriminator _ -> true
    | _ -> false)

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
   pinned the representation. *)
and with_realized (d:decl) : ML decl =
  match d with
  | DType t -> DType { t with dt_flags = Realized :: t.dt_flags }
  | d -> d

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
  match TcEnv.try_lookup_lid (tcenv st) l with
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
                   if is_type_binder (tcenv st) b && not (List.mem n anys) then [n] else []) in
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
       then (let d = extract_type_abbrev st nm lb in
             if is_erasable st se || is_prop_sig st lb.lbtyp
             then with_erased_flag d else d)
       else extract_letbinding st l nm lb is_rec margs n_holes
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
                 if is_type_binder (tcenv st) b then [name_of_bv b.binder_bv] else []) in
      DType { dt_name = nm; dt_params = ps; dt_body = TAbstract;
              dt_flags = (if is_erasable st se || is_prop_sig st t
                          then [Erased] else []) }
    else DExternal { dx_name = nm; dx_typars = []; dx_ty = ty_of_typ st t; dx_target = None; dx_header = None; dx_flags = [] }

  | Sig_inductive_typ {params} ->
    let d = extract_inductive st l nm params in
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
  let res = norm_bounded st "a type signature"
                         [TcEnv.AllowUnboundUniverses; TcEnv.EraseUniverses;
                          TcEnv.Beta; TcEnv.Iota;
                          TcEnv.UnfoldUntil delta_constant]
                         (U.comp_result c) in
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
  let res = norm_bounded st "a type signature"
                         [TcEnv.AllowUnboundUniverses; TcEnv.EraseUniverses;
                          TcEnv.Beta; TcEnv.Iota;
                          TcEnv.UnfoldUntil delta_constant]
                         (U.comp_result c) in
  match (SS.compress (U.unrefine res)).n with
  | Tm_fvar fv -> S.fv_eq_lid fv PC.prop_lid
  | _ -> false

and extract_type_abbrev (st:state) (nm:name) (lb:letbinding) : ML decl =
  let bs, body, _ = U.abs_formals lb.lbdef in
  DType {
    dt_name   = nm;
    dt_params = bs |> List.collect (fun b ->
                  if is_type_binder (tcenv st) b then [name_of_bv b.binder_bv] else []);
    dt_body   = TAbbrev (ty_of_typ st body);
    dt_flags  = [];
  }

(* Substitute the [Mono] arguments into the definition and re-abstract over the
   [Poly] ones.  Instead of taking the definition apart we apply it to a
   spine made of the concrete [Mono] arguments and fresh names for the [Poly]
   ones, and let the normalizer do the substitution: that copes uniformly with
   definitions that are eta-short, that have more binders than their type
   shows, or that are not syntactically lambdas at all. *)
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
  let rec go (i:int) (bs:binders) (cs:list bclass) (subst:list subst_elt)
             (spine:args) (poly:binders) (polycs:list bclass)
    : ML (args & binders & list bclass & comp) =
    match bs with
    | [] -> (List.rev spine, List.rev poly, List.rev polycs, SS.subst_comp subst c)
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
  let poly = poly @ hbs in
  let polycs = polycs @ List.map (fun _ -> Poly) hbs in
  let applied = match spine with [] -> def | _ -> U.mk_app def spine in
  (* The chain in the error names the definition, so "a body" is enough. *)
  let body = norm_bounded st "a definition body" custard_norm_steps applied in
  (U.abs poly body None, c, polycs, poly)

and extract_letbinding (st:state) (l:Ident.lident) (nm:name) (lb:letbinding)
                       (is_rec:bool) (margs:list (int & term)) (n_holes:int) : ML decl =
  let cs = binder_classes st l in
  (* Lifted local functions are named after whatever encloses them. *)
  let saved_cur = !st.cur in
  st.cur := nm;
  let def, c, polycs, poly = specialize st lb.lbtyp lb.lbdef cs margs n_holes in
  let bs, body, _ = U.abs_formals def in
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
     effect, which is the one that matters at a call site. *)
  let n_extra =
    flags |> List.mapi (fun i f -> if not f && i >= n_poly then 1 else 0)
          |> List.fold_left (fun a b -> a + b) 0 in
  (* Erased type binders carry no value but do parameterize the signature; the
     karamel backend resolves [TVar]s against this list, so they have to be
     recorded even though they take no runtime argument. *)
  let typars = bs |> List.collect (fun b ->
                 if is_type_binder (tcenv st) b then [name_of_bv b.binder_bv] else []) in
  let bs = drop_flagged flags bs in
  let binders = bs |> List.map (fun b ->
    { b_name = name_of_bv b.binder_bv; b_ty = ty_of_typ st b.binder_bv.sort }) in
  (* The effect is the one of the *codomain*: [lbeff] is the effect of
     evaluating the lambda, which is always Tot. *)
  let rec peel (n:int) (e:eff) (t:cty) : ML (eff & cty) =
    if n <= 0 then (e, t)
    else match t with
         | TArrow (_, e', r) -> peel (n - 1) e' r
         | _ -> (e, t) in
  let eff, ret = peel n_extra (eff_of_comp st c) (ty_of_typ st (U.comp_result c)) in
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
                    if is_type_binder (tcenv st) b then [name_of_bv b.binder_bv] else []) in
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
    (* The remaining binders are the constructor's fields; those without
       runtime content are deleted here, matching what [app_of_fv] does to a
       constructor application. *)
    let bs = drop_flagged (bs |> List.map (Mono.is_erased_binder (tcenv st))) bs in
    (name_of_lid c,
     bs |> List.map (fun b ->
       (name_of_bv b.binder_bv, field_ty st b)))
  in
  DType {
    dt_name   = nm;
    dt_params = ty_params;
    dt_body   = TVariant (ctors |> List.map ctor);
    dt_flags  = [];
  }

(* -------------------------------------------------------------------- *)
(* Driving                                                              *)
(* -------------------------------------------------------------------- *)

let dump_specializations (st:state) : ML unit =
  BU.print_string "Custard specializations:\n";
  SMap.iter st.counts (fun l n ->
    if n > 1 then BU.print2 "  %s -> %s\n" l (show n));
  BU.print1 "  (total: %s)\n" (show (SMap.fold st.counts (fun _ n acc -> acc + n) 0))

let run (st:state) (roots:list Ident.lident) (main:option Ident.lident) : ML program =
  let mark (f:flag) (l:Ident.lident) : ML unit =
    let key = string_of_key { sk_lid = l; sk_args = []; sk_subst = []; sk_holes = 0 } in
    let _ = request st { sk_lid = l; sk_args = []; sk_subst = []; sk_holes = 0 } in
    (* Mark the root so backends know which symbols must survive. *)
    match SMap.try_find st.emitted key with
    | Some (DLet d) ->
      SMap.add st.emitted key (DLet { d with dl_flags = f :: d.dl_flags })
    | _ -> () in
  roots |> List.iter (mark Root);
  (match main with Some l -> mark Entrypoint l | None -> ());
  if Options.custard_dump_specializations () then dump_specializations st;
  List.rev !st.order |> List.collect (fun key ->
    match SMap.try_find st.emitted key with
    | Some d -> [d]
    | None -> [])

let imports (st:state) : ML (list (decl & option type_info)) = List.rev !st.imports

let exported_keys (st:state) : ML (list (string & string)) =
  SMap.fold st.names (fun key nm acc -> (string_of_name nm, key) :: acc) []

let loaded_digests (_:state) : ML (list (string & string)) = Loader.loaded_digests ()
