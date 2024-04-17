(*
   Copyright 2008-2024 Nikhil Swamy and Microsoft Research

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

module FStar.TypeChecker.Quals
open FStar
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Errors
open FStar.Errors.Msg
open FStar.Pprint
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Syntax
open FStar.Class.Show
open FStar.Class.PP

module SS = FStar.Syntax.Subst
module S  = FStar.Syntax.Syntax
module BU = FStar.Compiler.Util
module U  = FStar.Syntax.Util
module N  = FStar.TypeChecker.Normalize
module C  = FStar.Parser.Const

let check_sigelt_quals_pre (env:FStar.TypeChecker.Env.env) se =
    let visibility = function Private -> true | _ -> false in
    let reducibility = function
        | Irreducible
        | Unfold_for_unification_and_vcgen | Visible_default
        | Inline_for_extraction -> true
        | _ -> false in
    let assumption = function Assumption | New -> true | _ -> false in
    let reification = function Reifiable | Reflectable _ -> true | _ -> false in
    let inferred = function
      | Discriminator _
      | Projector _
      | RecordType _
      | RecordConstructor _
      | ExceptionConstructor
      | HasMaskedEffect
      | Effect -> true
      | _ -> false in
    let has_eq = function Noeq | Unopteq -> true | _ -> false in
    let quals_combo_ok quals q =
        match q with
        | Assumption ->
          quals
          |> List.for_all (fun x -> x=q
                              || x=Logic
                              || inferred x
                              || visibility x
                              || assumption x
                              || (env.is_iface && x=Inline_for_extraction)
                              || x=NoExtract)

        | New -> //no definition provided
          quals
          |> List.for_all (fun x -> x=q || inferred x || visibility x || assumption x)

        | Inline_for_extraction ->
          quals |> List.for_all (fun x -> x=q || x=Logic || visibility x || reducibility x
                                              || reification x || inferred x || has_eq x
                                              || (env.is_iface && x=Assumption)
                                              || x=NoExtract)

        | Unfold_for_unification_and_vcgen
        | Visible_default
        | Irreducible
        | Noeq
        | Unopteq ->
          quals
          |> List.for_all (fun x -> x=q || x=Logic || x=Inline_for_extraction || x=NoExtract || has_eq x || inferred x || visibility x || reification x)

        | TotalEffect ->
          quals
          |> List.for_all (fun x -> x=q || inferred x || visibility x || reification x)

        | Logic ->
          quals
          |> List.for_all (fun x -> x=q || x=Assumption || inferred x || visibility x || reducibility x)

        | Reifiable
        | Reflectable _ ->
          quals
          |> List.for_all (fun x -> reification x || inferred x || visibility x || x=TotalEffect || x=Visible_default)

        | Private ->
          true //only about visibility; always legal in combination with others

        | _ -> //inferred
          true
    in
    let check_no_subtyping_attribute se =
      if U.has_attribute se.sigattrs C.no_subtping_attr_lid &&
         (match se.sigel with
          | Sig_let _ -> false
          | _ -> true)
      then raise_error_doc
             (Errors.Fatal_InconsistentQualifierAnnotation, [
              text "Illegal attribute: the `no_subtyping` attribute is allowed only on let-bindings."])
             se.sigrng in
    check_no_subtyping_attribute se;
    let quals = U.quals_of_sigelt se |> List.filter (fun x -> not (x = Logic)) in  //drop logic since it is deprecated
    if quals |> BU.for_some (function OnlyName -> true | _ -> false) |> not
    then
      let r = U.range_of_sigelt se in
      let no_dup_quals = BU.remove_dups (fun x y -> x=y) quals in
      let err' msg =
          raise_error (Errors.Fatal_QulifierListNotPermitted, (BU.format2
                          "The qualifier list \"[%s]\" is not permissible for this element%s"
                          (Print.quals_to_string quals) msg)) r in
      let err msg = err' (": " ^ msg) in
      let err' () = err' "" in
      if List.length quals <> List.length no_dup_quals
      then err "duplicate qualifiers";
      if not (quals |> List.for_all (quals_combo_ok quals))
      then err "ill-formed combination";
      match se.sigel with
      | Sig_let {lbs=(is_rec, _)} -> //let rec
        if is_rec && quals |> List.contains Unfold_for_unification_and_vcgen
        then err "recursive definitions cannot be marked inline";
        if quals |> BU.for_some (fun x -> assumption x || has_eq x)
        then err "definitions cannot be assumed or marked with equality qualifiers"
      | Sig_bundle _ ->
        if not (quals |> BU.for_all (fun x ->
              x=Inline_for_extraction
              || x=NoExtract
              || inferred x
              || visibility x
              || has_eq x))
        then err' ();
        if quals |> List.existsb (function Unopteq -> true | _ -> false) &&
           U.has_attribute se.sigattrs FStar.Parser.Const.erasable_attr
        then err "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
      | Sig_declare_typ _ ->
        if quals |> BU.for_some has_eq
        then err' ()
      | Sig_assume _ ->
        if not (quals |> BU.for_all (fun x -> visibility x || x=Assumption || x=InternalAssumption))
        then err' ()
      | Sig_new_effect _ ->
        if not (quals |> BU.for_all (fun x ->
              x=TotalEffect
              || inferred x
              || visibility x
              || reification x))
        then err' ()
      | Sig_effect_abbrev _ ->
        if not (quals |> BU.for_all (fun x -> inferred x || visibility x))
        then err' ()
      | _ -> ()

let check_erasable env quals r se =
  let lids = U.lids_of_sigelt se in
  let val_exists =
    lids |> BU.for_some (fun l -> Option.isSome (Env.try_lookup_val_decl env l))
  in
  let val_has_erasable_attr =
    lids |> BU.for_some (fun l ->
      let attrs_opt = Env.lookup_attrs_of_lid env l in
      Option.isSome attrs_opt
      && U.has_attribute (Option.get attrs_opt) FStar.Parser.Const.erasable_attr)
  in
  let se_has_erasable_attr = U.has_attribute se.sigattrs FStar.Parser.Const.erasable_attr in
  if ((val_exists && val_has_erasable_attr) && not se_has_erasable_attr)
  then raise_error_doc (Errors.Fatal_QulifierListNotPermitted, [
           text "Mismatch of attributes between declaration and definition.";
           text "Declaration is marked `erasable` but the definition is not.";
         ]) r;
  if ((val_exists && not val_has_erasable_attr) && se_has_erasable_attr)
  then raise_error_doc (Errors.Fatal_QulifierListNotPermitted, [
           text "Mismatch of attributes between declaration and definition.";
           text "Definition is marked `erasable` but the declaration is not.";
         ]) r;
  if se_has_erasable_attr
  then begin
    match se.sigel with
    | Sig_bundle _ ->
      if not (quals |> BU.for_some (function Noeq -> true | _ -> false))
      then raise_error_doc (Errors.Fatal_QulifierListNotPermitted, [
              text "Incompatible attributes and qualifiers: \
               erasable types do not support decidable equality and must be marked `noeq`."
             ]) r
    | Sig_declare_typ _ ->
      ()
    | Sig_fail _ ->
      () (* just ignore it, the member ses have the attribute too *)

    | Sig_let {lbs=(false, [lb])} ->
      let _, body, _ = U.abs_formals lb.lbdef in
      if not (N.non_info_norm env body)
      then raise_error_doc
             (Errors.Fatal_QulifierListNotPermitted, [
                  text "Illegal attribute: \
                   the `erasable` attribute is only permitted on inductive type definitions \
                   and abbreviations for non-informative types.";
                  text "The term" ^/^ pp body ^/^ text "is considered informative.";
             ]) body.pos

    | Sig_new_effect ({mname=eff_name}) ->  //AR: allow erasable on total effects
      if not (List.contains TotalEffect quals)
      then raise_error_doc (Errors.Fatal_QulifierListNotPermitted, [
               text "Effect" ^/^ pp eff_name ^/^ text "is marked erasable but only total effects are allowed to be erasable."
             ]) r

    | _ ->
      raise_error_doc (Errors.Fatal_QulifierListNotPermitted, [
          text "Illegal attribute: \
          the `erasable` attribute is only permitted on inductive type definitions \
          and abbreviations for non-informative types.";
        ]) r
  end

let check_sigelt_quals_post env se =
  let quals = se.sigquals in
  let r = se.sigrng in
  check_erasable env quals r se
