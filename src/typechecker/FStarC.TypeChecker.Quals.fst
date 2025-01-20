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

module FStarC.TypeChecker.Quals
open FStar open FStarC
open FStarC
open FStarC.Effect
open FStarC.Errors
open FStarC.Errors.Msg
open FStarC.Pprint
open FStarC.Syntax.Syntax
open FStarC.Ident
open FStarC.Syntax
open FStarC.Class.Show
open FStarC.Class.PP

module SS = FStarC.Syntax.Subst
module S  = FStarC.Syntax.Syntax
module BU = FStarC.Util
module U  = FStarC.Syntax.Util
module N  = FStarC.TypeChecker.Normalize
module C  = FStarC.Parser.Const
module TcUtil = FStarC.TypeChecker.Util

let check_sigelt_quals_pre (env:FStarC.TypeChecker.Env.env) se =
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
      then raise_error se
             Errors.Fatal_InconsistentQualifierAnnotation [
              text "Illegal attribute: the `no_subtyping` attribute is allowed only on let-bindings."]
    in
    check_no_subtyping_attribute se;
    let quals = U.quals_of_sigelt se |> List.filter (fun x -> not (x = Logic)) in  //drop logic since it is deprecated
    if quals |> BU.for_some (function OnlyName -> true | _ -> false) |> not
    then
      let r = U.range_of_sigelt se in
      let no_dup_quals = BU.remove_dups (fun x y -> x=y) quals in
      let err msg = raise_error r Errors.Fatal_QulifierListNotPermitted ([
                      text "The qualifier list" ^/^ doc_of_string (show quals) ^/^ text "is not permissible for this element"
                    ] @ msg)
      in
      if List.length quals <> List.length no_dup_quals
      then err [text "Duplicate qualifiers."];
      if not (quals |> List.for_all (quals_combo_ok quals))
      then err [text "Ill-formed combination."];
      match se.sigel with
      | Sig_let {lbs=(is_rec, _)} -> //let rec
        if is_rec && quals |> List.contains Unfold_for_unification_and_vcgen
        then err [text "Recursive definitions cannot be marked inline."];
        if quals |> BU.for_some (fun x -> assumption x || has_eq x)
        then err [text "Definitions cannot be assumed or marked with equality qualifiers."]
      | Sig_bundle _ ->
        if not (quals |> BU.for_all (fun x ->
              x=Inline_for_extraction
              || x=NoExtract
              || inferred x
              || visibility x
              || has_eq x))
        then err [];
        if quals |> List.existsb (function Unopteq -> true | _ -> false) &&
           U.has_attribute se.sigattrs FStarC.Parser.Const.erasable_attr
        then err [text "The `unopteq` qualifier is not allowed on erasable inductives since they don't have decidable equality."]
      | Sig_declare_typ _ ->
        if quals |> BU.for_some has_eq
        then err []
      | Sig_assume _ ->
        if not (quals |> BU.for_all (fun x -> visibility x || x=Assumption || x=InternalAssumption))
        then err []
      | Sig_new_effect _ ->
        if not (quals |> BU.for_all (fun x ->
              x=TotalEffect
              || inferred x
              || visibility x
              || reification x))
        then err []
      | Sig_effect_abbrev _ ->
        if not (quals |> BU.for_all (fun x -> inferred x || visibility x))
        then err []
      | _ -> ()

let check_erasable env quals (r:Range.range) se =
  let lids = U.lids_of_sigelt se in
  let val_exists =
    lids |> BU.for_some (fun l -> Option.isSome (Env.try_lookup_val_decl env l))
  in
  let val_has_erasable_attr =
    lids |> BU.for_some (fun l ->
      let attrs_opt = Env.lookup_attrs_of_lid env l in
      Option.isSome attrs_opt
      && U.has_attribute (Option.get attrs_opt) FStarC.Parser.Const.erasable_attr)
  in
  let se_has_erasable_attr = U.has_attribute se.sigattrs FStarC.Parser.Const.erasable_attr in
  if ((val_exists && val_has_erasable_attr) && not se_has_erasable_attr)
  then raise_error r Errors.Fatal_QulifierListNotPermitted [
           text "Mismatch of attributes between declaration and definition.";
           text "Declaration is marked `erasable` but the definition is not.";
         ];
  if ((val_exists && not val_has_erasable_attr) && se_has_erasable_attr)
  then raise_error r Errors.Fatal_QulifierListNotPermitted [
           text "Mismatch of attributes between declaration and definition.";
           text "Definition is marked `erasable` but the declaration is not.";
         ];
  if se_has_erasable_attr
  then begin
    match se.sigel with
    | Sig_bundle _ ->
      if not (quals |> BU.for_some (function Noeq -> true | _ -> false))
      then raise_error r Errors.Fatal_QulifierListNotPermitted [
              text "Incompatible attributes and qualifiers: \
               erasable types do not support decidable equality and must be marked `noeq`."
             ]
    | Sig_declare_typ _ ->
      ()
    | Sig_fail _ ->
      () (* just ignore it, the member ses have the attribute too *)

    | Sig_let {lbs=(false, [lb])} ->
      let _, body, _ = U.abs_formals lb.lbdef in
      if not (N.non_info_norm env body)
      then raise_error body Errors.Fatal_QulifierListNotPermitted [
                  text "Illegal attribute: \
                   the `erasable` attribute is only permitted on inductive type definitions \
                   and abbreviations for non-informative types.";
                  text "The term" ^/^ pp body ^/^ text "is considered informative.";
             ]

    | Sig_new_effect ({mname=eff_name}) ->  //AR: allow erasable on total effects
      if not (List.contains TotalEffect quals)
      then raise_error r Errors.Fatal_QulifierListNotPermitted [
               text "Effect" ^/^ pp eff_name ^/^ text "is marked erasable but only total effects are allowed to be erasable."
             ]

    | _ ->
      raise_error r Errors.Fatal_QulifierListNotPermitted [
          text "Illegal attribute: \
          the `erasable` attribute is only permitted on inductive type definitions \
          and abbreviations for non-informative types.";
        ]
  end

(*
 *  Given `val t : Type` in an interface
 *  and   `let t = e`    in the corresponding implementation
 *  The val declaration should contains the `must_erase_for_extraction` attribute
 *  if and only if `e` is a type that's non-informative (e..g., unit, t -> unit, etc.)
 *)
let check_must_erase_attribute env se =
  if Options.ide() then () else
  match se.sigel with
  | Sig_let {lbs; lids=l} ->
    begin match DsEnv.iface_decls (Env.dsenv env) (Env.current_module env) with
     | None ->
       ()

     | Some iface_decls ->
       snd lbs |> List.iter (fun lb ->
           let lbname = BU.right lb.lbname in
           let has_iface_val =
               iface_decls |> BU.for_some (Parser.AST.decl_is_val (ident_of_lid lbname.fv_name.v))
           in
           if has_iface_val
           then
               let must_erase = TcUtil.must_erase_for_extraction env lb.lbdef in
               let has_attr = Env.fv_has_attr env lbname C.must_erase_for_extraction_attr in
               if must_erase && not has_attr
               then log_issue lbname Error_MustEraseMissing [
                        text (BU.format1 "Values of type `%s` will be erased during extraction, \
                               but its interface hides this fact." (show lbname));
                        text (BU.format1 "Add the `must_erase_for_extraction` \
                               attribute to the `val %s` declaration for this symbol in the interface" (show lbname));
                      ]
               else if has_attr && not must_erase
               then log_issue lbname Error_MustEraseMissing [
                        text (BU.format1 "Values of type `%s` cannot be erased during extraction, \
                               but the `must_erase_for_extraction` attribute claims that it can."
                               (show lbname));
                        text "Please remove the attribute.";
                      ])
  end
  | _ -> ()

let check_typeclass_instance_attribute env (rng:Range.range) se =
  let is_tc_instance =
      se.sigattrs |> BU.for_some
        (fun t ->
          match t.n with
          | Tm_fvar fv -> S.fv_eq_lid fv FStarC.Parser.Const.tcinstance_lid
          | _ -> false)
  in
  let check_instance_typ (ty:typ) : unit =
    let _, res = U.arrow_formals_comp ty in
    if not (U.is_total_comp res) then
      log_issue rng FStarC.Errors.Error_UnexpectedTypeclassInstance [
          text "Instances are expected to be total.";
          text "This instance has effect" ^^ pp (U.comp_effect_name res);
      ];

    let t = U.comp_result res in
    let head, _ = U.head_and_args t in
    let err () =
      FStarC.Errors.log_issue rng FStarC.Errors.Error_UnexpectedTypeclassInstance [
          text "Instances must define instances of `class` types.";
          text "Type" ^/^ pp t ^/^ text "is not a class.";
        ]
    in
    match (U.un_uinst head).n with
    | Tm_fvar fv ->
      if not (Env.fv_has_attr env fv FStarC.Parser.Const.tcclass_lid) then
        err ()
    | _ ->
      err ()
  in
  if is_tc_instance then
    match se.sigel with
    | Sig_let {lbs=(false, [lb])} ->
      check_instance_typ lb.lbtyp

    | Sig_let _ ->
      FStarC.Errors.log_issue rng FStarC.Errors.Error_UnexpectedTypeclassInstance [
          text "An `instance` definition is expected to be non-recursive and of a type that is a `class`."
        ]

    | Sig_declare_typ {t} ->
      check_instance_typ t

    | _ ->
      FStarC.Errors.log_issue rng FStarC.Errors.Error_UnexpectedTypeclassInstance [
          text "The `instance` attribute is only allowed on `let` and `val` declarations.";	
          text "It is not allowed for" ^/^ squotes (arbitrary_string <| Print.sigelt_to_string_short se);
        ]

let check_sigelt_quals_post env se =
  let quals = se.sigquals in
  let r = se.sigrng in
  check_erasable env quals r se;
  check_must_erase_attribute env se;
  check_typeclass_instance_attribute env r se;
  ()
