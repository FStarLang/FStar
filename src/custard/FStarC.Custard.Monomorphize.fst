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

(** Type monomorphization (section 5.0).

    Under [--custard_monomorphize_types], rule 4 of section 3.1 has already
    marked every *function*'s type binders [Mono], so no function is left
    polymorphic.  What survives is the polymorphic *type declarations* they
    mention: [list] is still one declaration with one parameter, and the
    program refers to it as [TApp (list, [int])] here and [TApp (list, [bool])]
    there.  C has no such thing, so this pass gives each distinct
    instantiation a declaration of its own.

    It is an IR-to-IR pass rather than part of the extractor, for three
    reasons.  The extractor's job -- deciding what to compile and at what
    instantiation -- is already delicate, and this needs none of it: by the
    time the IR exists every type is ground, so the set of instantiations is
    simply what is written in the program.  A separate pass can be run or not
    run without the other backends noticing.  And nested instantiations
    ([list (list int)]) fall out of a worklist rather than having to be
    threaded through the demand-driven loop.

    It runs *before* the layout analysis, which is what earns the second half
    of section 5.0: with no type variables left the uniformity rule is vacuous,
    so layouts may be computed per instantiation.

    Constructor names are renamed with their *owner's* suffix rather than one
    of their own, so that a use site can find the right one knowing only the
    type it is building or matching -- which every use site does know. *)
module FStarC.Custard.Monomorphize

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Show
open FStarC.BaseTypes
open FStarC.Const
open FStarC.Custard.Syntax

module SMap   = FStarC.SMap
module String = FStarC.String
module Options = FStarC.Options

(* -------------------------------------------------------------------- *)
(* Keys and hints                                                       *)
(* -------------------------------------------------------------------- *)

(* Types are ground by now, so a printed [cty] is a perfectly good key. *)
let key_of (n:name) (args:list cty) : ML string =
  string_of_name n ^ "<" ^ String.concat "," (args |> List.map show) ^ ">"

(* The readable half of an instantiation's name.  [list__int] beats [list__7],
   and the whole point of Custard's naming is that the output can be read; the
   numeric fallback in [request] is only for shapes with no short spelling. *)
(* Section 30.15.  Bounded, in depth and in width, and both bounds are load
   bearing.  Unbounded, this is a *structural* rendering of a type, and an
   instantiation's name feeds the next one's hint through [n.spec] -- so a
   type that nests doubles the name at every level.  A twelve-deep
   accumulating environment produced a C identifier of 57,361 characters,
   which C99 does not promise to distinguish past 63 and which is quadratic to
   print besides.  It is also quadratic to *build*: the hint is recomputed per
   request over a type whose size is the thing that is growing.

   Truncating can only make two hints collide, and [request]'s [pick] already
   resolves a collision by numbering, so nothing is lost but spelling. *)
let hint_width : int = 48
let hint_depth : int = 4

let rec hint_of_cty (fuel:int) (c:cty) : ML string =
  if fuel <= 0 then "x"
  else
  let sub (c:cty) : ML string = hint_of_cty (fuel - 1) c in
  match c with
  | TVar v -> v
  | TInt (s, w) ->
    (match s with Signed -> "int" | Unsigned -> "uint") ^
    (match w with
     | Int8 -> "8" | Int16 -> "16" | Int32 -> "32"
     | Int64 -> "64" | Sizet -> "size")
  | TFloat Float32 -> "float32"
  | TFloat Float64 -> "float64"
  | TApp (n, []) -> (match n.spec with Some s -> n.id ^ "_" ^ s | None -> n.id)
  | TApp (n, args) -> n.id ^ "_" ^ String.concat "_" (args |> List.map sub)
  | TBuf c -> sub c ^ "_ptr"
  | TRef c -> sub c ^ "_ref"
  | TInline c -> hint_of_cty fuel c
  | TTuple cs -> "tup" ^ String.concat "_" (cs |> List.map sub)
  | TUnit -> "unit"
  | TExn -> "exn"
  | TArrow _ -> "fn"
  | TAny -> "any"

let clip (s:string) : ML string =
  if String.length s <= hint_width then s
  else String.substring s 0 hint_width

(* -------------------------------------------------------------------- *)
(* State                                                                *)
(* -------------------------------------------------------------------- *)

type state = {
  (* Every type declaration, by name: needed to read a constructor's field
     types back when descending into a pattern. *)
  types:  SMap.t dtype;
  (* Type declarations that must stay polymorphic: see [frozen]. *)
  frozen: SMap.t bool;
  (* Instantiation key -> the name its clone got. *)
  names:  SMap.t name;
  (* Suffixes already handed out, so that a hint collision falls back to a
     number rather than silently merging two different instantiations. *)
  taken:  SMap.t bool;
  clones: ref (list dtype);
  (* Instantiations whose body has not been built yet.  Building one can
     demand others, hence a worklist rather than recursion. *)
  todo:   ref (list (name & name & list cty));
}

(* An external is realized by hand-written code in the target language, which
   this pass cannot rewrite: if [FStar.String.concat] is realized at
   ['a list], then [list] has to stay one polymorphic declaration and every
   use of it has to agree.  So a type mentioned in an external's signature is
   frozen, along with everything reachable from it.  In C, where nothing is
   realized polymorphically, this set is empty.

   A [Realized] or [Imported] type declaration is frozen for the same reason,
   and more directly: its representation is fixed outside this program -- by
   the hand-written OCaml, or by the unit that already compiled it -- and it
   is not emitted here, so a clone of it would be a name that no module
   defines.  [FStar.Pervasives.Native]'s [option] and [tupleN] are the ones
   that matter: without this, [option int] asked for a clone
   [FStar_Pervasives_Native.option__int] that the realization has never heard
   of, and every module using one failed to compile.

   Only on the OCaml path.  [Realized] records that a *hand-written OCaml*
   module defines the type (section 8.2); the C backends link none of them and
   emit the declaration themselves, so there freezing would leave a type
   variable behind and C has no representation for one.

   A [Modelled] declaration (section 20) is frozen on every path, and for a
   sharper reason than the others: karamel matches a slice as an *application*
   of its lid, and an application with no arguments is not one, so the type
   has to keep its parameter or the hook cannot fire.  The transitivity earns
   its keep here -- a struct with a slice field must not be cloned
   per-instantiation either, or karamel's lifetime fixpoint would not find the
   [TApp] inside it. *)
let freeze_realized () : ML bool = Options.custard_backend () = "OCaml"
let is_poly (st:state) (n:name) : ML bool =
  if Some? (SMap.try_find st.frozen (string_of_name n)) then false
  else match SMap.try_find st.types (string_of_name n) with
  | Some d -> Cons? d.dt_params
  | None -> false

(* A constructor's name is a function of its owner's, which is what lets a use
   site rename it knowing only the type. *)
let with_spec (owner:name) (n:name) : name = { n with spec = owner.spec }

(* [dt_params] are the declaration's variables in order, so the substitution is
   positional.  A length mismatch would be an extractor bug; keeping what we
   can degrades to the polymorphic behaviour rather than crashing. *)
let rec zip_params (ps:list string) (args:list cty) : list (string & cty) =
  match ps, args with
  | p :: ps, a :: args -> (p, a) :: zip_params ps args
  | _ -> []

(* -------------------------------------------------------------------- *)
(* Requesting an instantiation                                          *)
(* -------------------------------------------------------------------- *)

let request (st:state) (n:name) (args:list cty) : ML name =
  let key = key_of n args in
  match SMap.try_find st.names key with
  | Some nm -> nm
  | None ->
    let hint = String.concat "_" (args |> List.map (hint_of_cty hint_depth)) in
    let base = clip ((match n.spec with Some s -> s ^ "_" | None -> "") ^ hint) in
    let rec pick (i:int) : ML string =
      let cand = if i = 0 then base else base ^ "_" ^ show i in
      let k = string_of_name ({ n with spec = None }) ^ "__" ^ cand in
      if Some? (SMap.try_find st.taken k) then pick (i + 1)
      else (SMap.add st.taken k true; cand) in
    let nm = { n with spec = Some (pick 0) } in
    (* Register before building the body: a recursive type -- [list], whose
       [Cons] mentions [list a] -- must find this name rather than loop. *)
    SMap.add st.names key nm;
    st.todo := (n, nm, args) :: !st.todo;
    nm

(* A type abbreviation is not a representation, so it is not an instantiation
   either: [bytes = list uint32] has to be looked through both to find the
   instantiation a use site means and to keep [nat] and [int] from asking for
   two different clones of the same thing.  The layout pass unfolds
   abbreviations anyway, right after this one, so nothing is lost by doing it
   here.  Fuel guards against a malformed cycle rather than a real program. *)
let rec unfold_cty (st:state) (fuel:int) (c:cty) : ML cty =
  if fuel <= 0 then c
  else match c with
  | TApp (n, args) ->
    (match SMap.try_find st.types (string_of_name n) with
     | Some ({ dt_body = TAbbrev b; dt_params = ps }) ->
       (* An eta-contracted abbreviation -- [type t = flat_set], which binds
          nothing and stands for a type constructor -- takes more arguments
          than it has parameters, and the surplus belongs to whatever the body
          names.  It has to be attached before unfolding again, or the body
          would be unfolded with its own parameter still free (see the same
          case in {!FStarC.Custard.Layout.resolve}). *)
       let np = List.length ps in
       (* An abbreviation applied to *fewer* arguments than it has parameters
          cannot be unfolded: the body would keep the missing parameters as
          free variables, which is worse than the abbreviation it replaced.
          Only [TApp] can carry the remaining arguments, so a partial
          application stays as written. *)
       if List.length args < np then c else
       let used, extra =
         if List.length args > np then List.splitAt np args else (args, []) in
       let b = subst_cty (zip_params ps used) b in
       let b = match extra, b with
               | [], _ -> b
               | _, TApp (m, a) -> TApp (m, a @ extra)
               | _ -> b in
       unfold_cty st (fuel - 1) b
     | _ -> c)
  | _ -> c

(* Replace every instantiated [TApp] by a reference to its clone.  The
   arguments are rewritten first, so [list (list int)] asks for [list__int]
   before asking for the outer one. *)
let rec mono_cty (st:state) (c:cty) : ML cty =
  (* The unfolded form is what is *returned*, not merely what is matched on:
     an abbreviation that stands for something other than a [TApp] -- [sid_t =
     U16.t] in the DICE example -- would otherwise survive, and a use site
     that wrote [option sid_t] would ask for a different clone than one that
     wrote [option U16.t] even though the two are the same type.  With
     [--custard_monomorphize_types] those are two C structs with identical
     fields and no conversion between them. *)
  let c = unfold_cty st 100 c in
  match c with
  | TApp (n, args) ->
    let args = args |> List.map (mono_cty st) in
    if is_poly st n then TApp (request st n args, []) else TApp (n, args)
  | TArrow (a, e, b) -> TArrow (mono_cty st a, e, mono_cty st b)
  | TBuf c -> TBuf (mono_cty st c)
  | TRef c -> TRef (mono_cty st c)
  | TInline c -> TInline (mono_cty st c)
  | TTuple cs -> TTuple (cs |> List.map (mono_cty st))
  | TVar _ | TInt _ | TFloat _ | TUnit | TExn | TAny -> c

(* The instantiation a use site is building or matching.  [None] means the
   type was not polymorphic, so its constructors keep their names. *)
let resolve_owner (st:state) (t:cty) : ML (option (name & list cty)) =
  match unfold_cty st 100 t with
  | TApp (n, args) when is_poly st n -> Some (n, args)
  | _ -> None

(* The declaration a type names, and the arguments it is applied at, whether or
   not it will be cloned.  Renaming a constructor and reading its field types
   back are two different questions, and only the first of them is about
   cloning: a *frozen* [tuple2] keeps its name but its fields are still at the
   arguments the use site wrote, and answering [] for them leaves a subpattern
   matched at a bare [TVar] -- which resolves nothing, so a constructor nested
   inside it silently keeps its polymorphic name while its type is cloned. *)
let shape_of (st:state) (t:cty) : ML (option (name & list cty)) =
  match unfold_cty st 100 t with
  | TApp (n, args) -> Some (n, args)
  | _ -> None

(* [resolve_owner] hands back the arguments as they were *written*, since a
   constructor's field types have to be substituted with those.  The clone,
   though, is keyed on the rewritten arguments -- that is what [mono_cty] uses
   -- so a use site has to rewrite them before asking. *)
let request_inst (st:state) (n:name) (args:list cty) : ML name =
  request st n (args |> List.map (mono_cty st))

(* The field types of constructor [cn] of [owner] at [args] -- the types the
   subpatterns of a [PCtor] are matched at.  Read off the *original*
   polymorphic declaration, so no clone body has to exist yet. *)
let ctor_fields (st:state) (owner:name) (args:list cty) (cn:name) : ML (list cty) =
  match SMap.try_find st.types (string_of_name owner) with
  | Some ({ dt_body = TVariant cs; dt_params = ps }) ->
    let sub = zip_params ps args in
    (match cs |> List.tryFind (fun (c, _) -> string_of_name c = string_of_name cn) with
     (* [TInline] is a note to [Simplify] about how the field is stored, not
        part of its type; a subpattern is matched against the type. *)
     | Some (_, fs) -> fs |> List.map (fun (_, c) ->
                         subst_cty sub (match c with TInline c -> c | c -> c))
     | None -> [])
  | _ -> []

(* The same, for a record: the types its fields are matched at, by name. *)
let record_fields (st:state) (owner:name) (args:list cty) : ML (list (string & cty)) =
  match SMap.try_find st.types (string_of_name owner) with
  | Some ({ dt_body = TRecord fs; dt_params = ps }) ->
    let sub = zip_params ps args in
    fs |> List.map (fun (f, c) ->
      (f, subst_cty sub (match c with TInline c -> c | c -> c)))
  | _ -> []

(* -------------------------------------------------------------------- *)
(* Rewriting the program                                                *)
(* -------------------------------------------------------------------- *)

(* The pre-rewrite type of every variable in scope.  A [PCtor] has to be
   renamed against the instantiation its scrutinee has, and the IR's only
   other candidate -- the scrutinee node's [ty] field -- is best-effort
   metadata that is often [TAny].  Binder types, by contrast, are exactly what
   this pass is rewriting, so they are known precisely. *)
type env = list (string & cty)

let lookup (env:env) (x:string) : ML (option cty) =
  match env |> List.tryFind (fun (y, _) -> y = x) with
  | Some (_, c) -> Some c
  | None -> None

(* Patterns are rewritten *top down*, against the type the scrutinee had before
   rewriting: that type says which instantiation the constructor belongs to,
   and its field types say the same for the subpatterns.  Done this way it
   needs only the original declarations, so it does not matter whether the
   clone has been built yet.

   A subpattern whose type could not be worked out is rewritten against [TAny],
   which leaves any constructor inside it alone.  That can only happen if the
   declaration table disagrees with the term, which would be an extractor bug;
   the symptom is then a dangling name in the output rather than a wrong
   one.

   The bindings a pattern introduces are returned along with it, so that a
   [match] inside a branch can be resolved the same way. *)
let rec mono_pat (st:state) (t:cty) (p:pat) : ML (pat & env) =
  let t = unfold_cty st 100 t in
  match p with
  | PCtor (cn, ps) ->
    let fields =
      match shape_of st t with
      | Some (n, args) -> ctor_fields st n args cn
      | None -> [] in
    let cn' =
      match resolve_owner st t with
      | Some (owner, args) -> with_spec (request_inst st owner args) cn
      | None -> cn in
    let ps', env = mono_pats st fields ps in
    (PCtor (cn', ps'), env)
  | PRecord (tn, fs) ->
    let fields =
      match shape_of st t with
      | Some (n, args) -> record_fields st n args
      | None -> [] in
    let tn' =
      match resolve_owner st t with
      | Some (owner, args) -> request_inst st owner args
      | None -> tn in
    let fs', env = List.fold_left (fun (acc, env) (f, q) ->
      let ft = (match fields |> List.tryFind (fun (g, _) -> g = f) with
                | Some (_, ft) -> ft
                | None -> TAny) in
      let q', env' = mono_pat st ft q in
      (acc @ [(f, q')], env @ env')) ([], []) fs in
    (PRecord (tn', fs'), env)
  | PTuple ps ->
    let ps', env = mono_pats st (match t with TTuple cs -> cs | _ -> []) ps in
    (PTuple ps', env)
  | POr ps ->
    (* Every branch of an [or] binds the same variables, so one pass suffices. *)
    let ps', envs = ps |> List.map (mono_pat st t) |> List.unzip in
    (POr ps', (match envs with e :: _ -> e | [] -> []))
  | PVar x -> (p, [(x, t)])
  | PWild | PConst _ -> (p, [])

and mono_pats (st:state) (ts:list cty) (ps:list pat) : ML (list pat & env) =
  match ts, ps with
  | t :: ts, p :: ps ->
    let p', e1 = mono_pat st t p in
    let ps', e2 = mono_pats st ts ps in
    (p' :: ps', e1 @ e2)
  | [], p :: ps ->
    let p', e1 = mono_pat st TAny p in
    let ps', e2 = mono_pats st [] ps in
    (p' :: ps', e1 @ e2)
  | _, [] -> ([], [])

let rec mono_expr (st:state) (env:env) (x:expr) : ML expr =
  (* A node's type is read *before* it is rewritten, since the pre-rewrite form
     is the one that still says which instantiation a constructor belongs to.
     For a variable the environment is authoritative; [ty] is the fallback. *)
  let type_of (e:expr) : ML cty =
    match e.e with
    | EVar v -> (match lookup env v with Some c -> c | None -> e.ty)
    | _ -> e.ty in
  let owner_of (t:cty) : ML (option name) =
    match resolve_owner st t with
    | Some (o, args) -> Some (request_inst st o args)
    | None -> None in
  let rename (t:cty) (cn:name) : ML name =
    match owner_of t with Some o -> with_spec o cn | None -> cn in
  let go = mono_expr st env in
  let e' =
    match x.e with
    | EConst _ | EVar _ | EAny | EAbort _ -> x.e
    | EQual (n, args) -> EQual (n, args |> List.map (mono_cty st))
    | ELet (v, t, e1, e2) ->
      ELet (v, mono_cty st t, go e1, mono_expr st ((v, t) :: env) e2)
    | EApp (h, es) -> EApp (go h, es |> List.map go)
    | EFun (bs, b) ->
      let env = (bs |> List.map (fun (b:binder) -> (b.b_name, b.b_ty))) @ env in
      EFun (bs |> List.map (fun (b:binder) -> { b with b_ty = mono_cty st b.b_ty }),
            mono_expr st env b)
    | EMatch (sc, brs) ->
      let t = type_of sc in
      EMatch (go sc, brs |> List.map (mono_branch st env t))
    | ETry (e, brs) -> ETry (go e, brs |> List.map (mono_branch st env TAny))
    | EIf (c, a, b) -> EIf (go c, go a, go b)
    | ESeq (a, b) -> ESeq (go a, go b)
    | ECtor (cn, es) -> ECtor (rename x.ty cn, es |> List.map go)
    | ERaise e1 -> ERaise (go e1)
    | ETuple es -> ETuple (es |> List.map go)
    | ERecord (n, fs) ->
      let n' = match owner_of x.ty with Some o -> o | None -> n in
      ERecord (n', fs |> List.map (fun (f, e) -> (f, go e)))
    | EProj (e, cn, f) -> EProj (go e, rename (type_of e) cn, f)
    | EDiscrim (e, cn) -> EDiscrim (go e, rename (type_of e) cn)
    | ECast (e, c) -> ECast (go e, mono_cty st c)
    | ECoerce (e, c) -> ECoerce (go e, mono_cty st c)
    | EOp (o, es) -> EOp (o, es |> List.map go)
    | EWhile (c, b) -> EWhile (go c, go b)
  in
  { x with e = e'; ty = mono_cty st x.ty }

and mono_branch (st:state) (env:env) (t:cty) (br:branch) : ML branch =
  let p, g, b = br in
  let p', bound = mono_pat st t p in
  let env = bound @ env in
  (p',
   (match g with Some g -> Some (mono_expr st env g) | None -> None),
   mono_expr st env b)

(* -------------------------------------------------------------------- *)
(* Building the clones                                                  *)
(* -------------------------------------------------------------------- *)

let rec drain (st:state) : ML unit =
  match !st.todo with
  | [] -> ()
  | (orig, nm, args) :: rest ->
    st.todo := rest;
    (match SMap.try_find st.types (string_of_name orig) with
     | None -> ()
     | Some d ->
       let sub = zip_params d.dt_params args in
       let f (c:cty) : ML cty = mono_cty st (subst_cty sub c) in
       let body =
         match d.dt_body with
         | TAbbrev c -> TAbbrev (f c)
         | TRecord fs -> TRecord (fs |> List.map (fun (x, c) -> (x, f c)))
         | TVariant cs ->
           TVariant (cs |> List.map (fun (cn, fs) ->
                       (with_spec nm cn, fs |> List.map (fun (x, c) -> (x, f c)))))
         | TAbstract -> TAbstract in
       st.clones := { d with dt_name = nm; dt_params = []; dt_body = body }
                    :: !st.clones);
    drain st

(* -------------------------------------------------------------------- *)
(* Entry point                                                          *)
(* -------------------------------------------------------------------- *)

let run (prog:program) : ML program =
  let st = { types  = SMap.create 100;
             frozen = SMap.create 10;
             names  = SMap.create 100;
             taken  = SMap.create 100;
             clones = mk_ref [];
             todo   = mk_ref [] } in
  prog |> List.iter (fun d ->
    match d with
    | DType t ->
      SMap.add st.types (string_of_name t.dt_name) t;
      SMap.add st.taken (string_of_name t.dt_name) true
    | _ -> ());
  (* Freezing is transitive: a frozen [list] mentions [option] in no way here,
     but if it did, that [option] could not be cloned either. *)
  let rec freeze (fuel:int) (c:cty) : ML unit =
    if fuel <= 0 then () else
    match c with
    | TApp (n, args) ->
      let k = string_of_name n in
      args |> List.iter (freeze (fuel - 1));
      if None? (SMap.try_find st.frozen k) then begin
        SMap.add st.frozen k true;
        match SMap.try_find st.types k with
        | Some d ->
          (match d.dt_body with
           | TAbbrev c -> freeze (fuel - 1) c
           | TRecord fs -> fs |> List.iter (fun (_, c) -> freeze (fuel - 1) c)
           | TVariant cs ->
             cs |> List.iter (fun (_, fs) ->
                     fs |> List.iter (fun (_, c) -> freeze (fuel - 1) c))
           | TAbstract -> ())
        | None -> ()
      end
    | TArrow (a, _, b) -> freeze (fuel - 1) a; freeze (fuel - 1) b
    | TBuf c | TRef c | TInline c -> freeze (fuel - 1) c
    | TTuple cs -> cs |> List.iter (freeze (fuel - 1))
    | TVar _ | TInt _ | TFloat _ | TUnit | TExn | TAny -> () in
  prog |> List.iter (fun d ->
    match d with
    | DExternal x -> freeze 100 x.dx_ty
    | DExn e -> e.de_args |> List.iter (freeze 100)
    | DType t when t.dt_flags |> List.existsb (function
                     | Modelled -> true | _ -> false) ->
      freeze 100 (TApp (t.dt_name, []))
    | DType t when freeze_realized ()
                && t.dt_flags |> List.existsb (function
                     | Realized | Imported _ -> true | _ -> false) ->
      freeze 100 (TApp (t.dt_name, []))
    | _ -> ());
  (* The polymorphic declarations are replaced by their instantiations, so they
     are dropped here and everything else is rewritten in place.  Emission
     order does not matter: [Simplify.scc] sorts the whole program
     topologically at the end of phase 4, which is after this runs. *)
  let rest = prog |> List.collect (fun d ->
    match d with
    | DType t when Cons? t.dt_params && is_poly st t.dt_name -> []
    | DType t when Cons? t.dt_params ->
      (* Frozen: kept as it is, and its parameters with it. *)
      [DType t]
    | DType t ->
      let body = match t.dt_body with
                 | TAbbrev c -> TAbbrev (mono_cty st c)
                 | TRecord fs -> TRecord (fs |> List.map (fun (x, c) -> (x, mono_cty st c)))
                 | TVariant cs ->
                   TVariant (cs |> List.map (fun (cn, fs) ->
                               (cn, fs |> List.map (fun (x, c) -> (x, mono_cty st c)))))
                 | TAbstract -> TAbstract in
      [DType { t with dt_body = body }]
    | DLet l ->
      [DLet { l with
              dl_typars  = [];
              dl_binders = l.dl_binders |> List.map (fun (b:binder) ->
                             { b with b_ty = mono_cty st b.b_ty });
              dl_ret     = mono_cty st l.dl_ret;
              dl_body    = mono_expr st
                             (l.dl_binders |> List.map (fun (b:binder) ->
                                (b.b_name, b.b_ty)))
                             l.dl_body }]
    | DExternal x -> [DExternal { x with dx_ty = mono_cty st x.dx_ty }]
    | DExn e -> [DExn { e with de_args = e.de_args |> List.map (mono_cty st) }]) in
  drain st;
  rest @ (List.rev !st.clones |> List.map (fun d -> DType d))
