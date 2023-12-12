module FStar.TypeChecker.Primops

(* This module just contains the list of all builtin primitive steps
with their implementations. *)

open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar
open FStar.Compiler
open FStar.String
open FStar.Const
open FStar.Char
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.Errors
open FStar.Class.Monad
open FStar.Class.Show

module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module BU = FStar.Compiler.Util
module FC = FStar.Const
module PC = FStar.Parser.Const
module U  = FStar.Syntax.Util
module I  = FStar.Ident
module EMB = FStar.Syntax.Embeddings
module Z = FStar.BigInt
module NBE = FStar.TypeChecker.NBETerm

open FStar.TypeChecker.Primops.Base

(*******************************************************************)
(* Semantics for primitive operators (+, -, >, &&, ...)            *)
(*******************************************************************)

let arg_as_int (a:arg) : option Z.t = fst a |> try_unembed_simple

let arg_as_list {|e:EMB.embedding 'a|} (a:arg)
: option (list 'a)
  = fst a |> try_unembed_simple

(* Most primitive steps don't use the NBE cbs, so they can use this wrapper. *)
let as_primitive_step is_strong (l, arity, u_arity, f, f_nbe) =
  Primops.Base.as_primitive_step_nbecbs is_strong (l, arity, u_arity, f, (fun cb univs args -> f_nbe univs args))

let mixed_binary_op
  (as_a : arg -> option 'a)
  (as_b : arg -> option 'b)
  (embed_c : Range.range -> 'c -> term)
  (f : Range.range -> universes -> 'a -> 'b -> option 'c)
  (psc : psc)
  (norm_cb : EMB.norm_cb)
  (univs : universes)
  (args : args)
  : option term
  = match args with
    | [a;b] ->
       begin
       match as_a a, as_b b with
       | Some a, Some b ->
         (match f psc.psc_range univs a b with
          | Some c -> Some (embed_c psc.psc_range c)
          | _ -> None)
       | _ -> None
       end
    | _ -> None

let mixed_ternary_op
  (as_a : arg -> option 'a)
  (as_b : arg -> option 'b)
  (as_c : arg -> option 'c)
  (embed_d : Range.range -> 'd -> term)
  (f : Range.range -> universes -> 'a -> 'b -> 'c -> option 'd)
  (psc : psc)
  (norm_cb : EMB.norm_cb)
  (univs : universes)
  (args : args)
  : option term
  = match args with
    | [a;b;c] ->
       begin
       match as_a a, as_b b, as_c c with
       | Some a, Some b, Some c ->
         (match f psc.psc_range univs a b c with
          | Some d -> Some (embed_d psc.psc_range d)
          | _ -> None)
       | _ -> None
       end
    | _ -> None

(* and_op and or_op are special cased because they are short-circuting,
  * can run without unembedding its second argument. *)
let and_op : psc -> EMB.norm_cb -> universes -> args -> option term
  = fun psc _norm_cb _us args ->
    match args with
    | [(a1, None); (a2, None)] ->
        begin match try_unembed_simple a1 with
        | Some false ->
          Some (embed_simple psc.psc_range false)
        | Some true ->
          Some a2
        | _ -> None
        end
    | _ -> failwith "Unexpected number of arguments"

let or_op : psc -> EMB.norm_cb -> universes -> args -> option term
  = fun psc _norm_cb _us args ->
    match args with
    | [(a1, None); (a2, None)] ->
        begin match try_unembed_simple a1 with
        | Some true ->
          Some (embed_simple psc.psc_range true)
        | Some false ->
          Some a2
        | _ -> None
        end
    | _ -> failwith "Unexpected number of arguments"


let division_modulus_op (f : Z.t -> Z.t -> Z.t) (x y : Z.t) : option Z.t =
  if Z.to_int_fs y <> 0
  then Some (f x y)
  else None

(* Simple primops that are just implemented by some concrete function
over embeddable types. *)
let simple_ops : list primitive_step = [
  (* Basic *)
  mk1 0 PC.string_of_int_lid (fun z -> string_of_int (Z.to_int_fs z));
  mk1 0 PC.int_of_string_lid (fun s -> fmap Z.of_int_fs (BU.safe_int_of_string s));
  mk1 0 PC.string_of_bool_lid string_of_bool;
  mk1 0 PC.bool_of_string_lid (function "true" -> Some true | "false" -> Some false | _ -> None);

  (* Integer opts *)
  mk1 0 PC.op_Minus Z.minus_big_int;
  mk2 0 PC.op_Addition Z.add_big_int;
  mk2 0 PC.op_Subtraction Z.sub_big_int;
  mk2 0 PC.op_Multiply Z.mult_big_int;
  mk2 0 PC.op_LT  Z.lt_big_int;
  mk2 0 PC.op_LTE Z.le_big_int;
  mk2 0 PC.op_GT  Z.gt_big_int;
  mk2 0 PC.op_GTE Z.ge_big_int;

  (* Use ' variant to allow for non-reduction. Impl is the same on each normalizer. *)
  mk2' 0 PC.op_Division (division_modulus_op Z.div_big_int) (division_modulus_op Z.div_big_int);
  mk2' 0 PC.op_Modulus  (division_modulus_op Z.mod_big_int) (division_modulus_op Z.div_big_int);

  (* Bool opts. NB: && and || are special-cased since they are
  short-circuiting, and can run even if their second arg does not
  try_unembed_simple. Otherwise the strict variants are defined as below. *)
  mk1 0 PC.op_Negation not;
  // mk2 0 PC.op_And (&&);
  // mk2 0 PC.op_Or  ( || );

  (* Operations from FStar.String *)
  mk2 0 PC.string_concat_lid String.concat;
  mk2 0 PC.string_split_lid String.split;
  mk2 0 PC.prims_strcat_lid (^);
  mk2 0 PC.string_compare_lid (fun s1 s2 -> Z.of_int_fs (String.compare s1 s2));
  mk1 0 PC.string_string_of_list_lid string_of_list;
  mk2 0 PC.string_make_lid (fun x y -> String.make (Z.to_int_fs x) y);
  mk1 0 PC.string_list_of_string_lid list_of_string;
  mk1 0 PC.string_lowercase_lid String.lowercase;
  mk1 0 PC.string_uppercase_lid String.uppercase;
  mk2 0 PC.string_index_lid String.index;
  mk2 0 PC.string_index_of_lid String.index_of;
  mk3 0 PC.string_sub_lid (fun s o l -> String.substring s (Z.to_int_fs o) (Z.to_int_fs l));

  (* Range ops *)
  mk5 0 PC.mk_range_lid (fun fn from_l from_c to_l to_c ->
      let open FStar.Compiler.Range in
      mk_range fn (mk_pos (Z.to_int_fs from_l) (Z.to_int_fs from_c))
                  (mk_pos (Z.to_int_fs to_l) (Z.to_int_fs to_c))
  );
]

let bogus_cbs = {
    NBE.iapp = (fun h _args -> h);
    NBE.translate = (fun _ -> failwith "bogus_cbs translate");
}

let issue_ops : list primitive_step =
  let mk_lid l = PC.p2l ["FStar"; "Issue"; l] in [
    mk1 0 (mk_lid "message_of_issue") Mkissue?.issue_msg;
    mk1 0 (mk_lid "level_of_issue") (fun i -> Errors.string_of_issue_level i.issue_level);
    mk1 0 (mk_lid "number_of_issue") (fun i -> fmap Z.of_int_fs i.issue_number);
    mk1 0 (mk_lid "range_of_issue") Mkissue?.issue_range;
    mk1 0 (mk_lid "context_of_issue") Mkissue?.issue_ctx;
    mk1 0 (mk_lid "render_issue") Errors.format_issue;
    mk5 0 (mk_lid "mk_issue_doc") (fun level msg range number context ->
          { issue_level = Errors.issue_level_of_string level;
            issue_range = range;
            issue_number = fmap Z.to_int_fs number;
            issue_msg = msg;
            issue_ctx = context}
    );
  ]

let seal_steps =
  List.map (fun p -> { as_primitive_step_nbecbs true p with renorm_after = true}) [
    (PC.map_seal_lid, 4, 2,
      (fun psc univs cbs args ->
        match args with
        | [(ta, _); (tb, _); (s, _); (f, _)] ->
          begin
          let open EMB in
          let try_unembed (#a:Type) (e:embedding a) (x:term) : option a =
              try_unembed x id_norm_cb
          in
          match try_unembed e_any ta,
                try_unembed e_any tb,
                try_unembed (e_sealed e_any) s,
                try_unembed e_any f with
          | Some ta, Some tb, Some s, Some f ->
            let r = U.mk_app f [S.as_arg s] in
            let emb = set_type ta e_any in
            Some (embed_simple #_ #(e_sealed emb) psc.psc_range r)
          | _ -> None
          end
        | _ -> None),
      (fun cb univs args ->
        match args with
        | [(ta, _); (tb, _); (s, _); (f, _)] ->
          begin
          let open FStar.TypeChecker.NBETerm in
          let try_unembed (#a:Type) (e:embedding a) (x:NBETerm.t) : option a =
              unembed e bogus_cbs x
          in
          match try_unembed e_any ta,
                try_unembed e_any tb,
                try_unembed (e_sealed e_any) s,
                try_unembed e_any f with
          | Some ta, Some tb, Some s, Some f ->
            let r = cb.iapp f [as_arg s] in
            let emb = set_type ta e_any in
            Some (embed (e_sealed emb) cb r)
          | _ -> None
          end
        | _ -> None
        ));
    (PC.bind_seal_lid, 4, 2,
      (fun psc univs cbs args ->
        match args with
        | [(ta, _); (tb, _); (s, _); (f, _)] ->
          begin
          let open EMB in
          let try_unembed (#a:Type) (e:embedding a) (x:term) : option a =
              try_unembed x id_norm_cb
          in
          match try_unembed e_any ta,
                try_unembed e_any tb,
                try_unembed (e_sealed e_any) s,
                try_unembed e_any f with
          | Some ta, Some tb, Some s, Some f ->
            let r = U.mk_app f [S.as_arg s] in
            Some (embed_simple #_ #e_any psc.psc_range r)
          | _ -> None
          end
        | _ -> None),
      (fun cb univs args ->
        match args with
        | [(ta, _); (tb, _); (s, _); (f, _)] ->
          begin
          let open FStar.TypeChecker.NBETerm in
          let try_unembed (#a:Type) (e:embedding a) (x:NBETerm.t) : option a =
              unembed e bogus_cbs x
          in
          match try_unembed e_any ta,
                try_unembed e_any tb,
                try_unembed (e_sealed e_any) s,
                try_unembed e_any f with
          | Some ta, Some tb, Some s, Some f ->
            let r = cb.iapp f [as_arg s] in
            let emb = set_type ta e_any in
            Some (embed emb cb r)
          | _ -> None
          end
        | _ -> None
        ));
  ]

    let array_ops : list primitive_step =
      let of_list_op =
        let emb_typ t = ET_app(PC.immutable_array_t_lid |> Ident.string_of_lid, [t]) in
        let un_lazy universes t l r =
          S.mk_Tm_app
            (S.mk_Tm_uinst (U.fvar_const PC.immutable_array_of_list_lid) universes)
            [S.iarg t; S.as_arg l]
            r
        in
        (  PC.immutable_array_of_list_lid, 2, 1,
           mixed_binary_op
              (fun (elt_t, _) -> Some elt_t) //the first arg of of_list is the element type
              (fun (l, q) -> //2nd arg: try_unembed_simple as a list term
                match arg_as_list #_ #FStar.Syntax.Embeddings.e_any (l, q) with
                | Some lst -> Some (l, lst)
                | _ -> None)
              (fun r (universes, elt_t, (l, blob)) -> 
                //embed the result back as a Tm_lazy with the `ImmutableArray.t term` as the blob
                //The kind records the type of the blob as IA.t "any"
                //and the interesting thing here is that the thunk represents the blob back as pure F* term
                //IA.of_list u#universes elt_t l.
                //This unreduced representation can be used in a context where the blob doesn't make sense,
                //e.g., in the SMT encoding, we represent the blob computed by of_list l
                //just as the unreduced term `of_list l`
                S.mk (Tm_lazy { blob;
                                lkind=Lazy_embedding (emb_typ EMB.(emb_typ_of _ #e_any ()), Thunk.mk (fun _ -> un_lazy universes elt_t l r));
                                ltyp=S.mk_Tm_app (S.mk_Tm_uinst (U.fvar_const PC.immutable_array_t_lid) universes) [S.as_arg elt_t] r;
                                rng=r }) r)
              (fun r universes elt_t (l, lst) ->
                //The actual primitive step computing the IA.t blob
                 let blob = FStar.ImmutableArray.Base.of_list #term lst in
                 Some (universes, elt_t, (l, FStar.Compiler.Dyn.mkdyn blob))),
           NBETerm.mixed_binary_op
             (fun (elt_t, _) -> Some elt_t)
             (fun (l, q) ->
               match NBETerm.arg_as_list NBETerm.e_any (l, q) with
               | None -> None
               | Some lst -> Some (l, lst))
             (fun (universes, elt_t, (l, blob)) ->
               //The embedding is similar to the non-NBE case
               //But, this time the thunk is the NBE.t representation of `of_list l`
               NBETerm.mk_t <|
               NBETerm.Lazy (Inr (blob, emb_typ EMB.(emb_typ_of _ #e_any ())),
                             Thunk.mk (fun _ ->
                               NBETerm.mk_t <| NBETerm.FV (S.lid_as_fv PC.immutable_array_of_list_lid None,
                                                          universes,
                                                          [NBETerm.as_arg l]))))
             (fun  universes elt_t (l, lst) ->
                let blob = FStar.ImmutableArray.Base.of_list #NBETerm.t lst in
                Some (universes, elt_t, (l, FStar.Compiler.Dyn.mkdyn blob))))
      in
      let arg1_as_elt_t (x:arg) : option term = Some (fst x) in
      let arg2_as_blob (x:arg) : option FStar.Compiler.Dyn.dyn =
          //try_unembed_simple an arg as a IA.t blob if the emb_typ
          //of the lkind tells us it has the right type
          match (SS.compress (fst x)).n with
          | Tm_lazy {blob=blob; lkind=Lazy_embedding (ET_app(head, _), _)}
            when head=Ident.string_of_lid PC.immutable_array_t_lid -> Some blob
          | _ -> None
      in
      let arg2_as_blob_nbe (x:NBETerm.arg) : option FStar.Compiler.Dyn.dyn =
          //try_unembed_simple an arg as a IA.t blob if the emb_typ
          //tells us it has the right type      
          let open FStar.TypeChecker.NBETerm in
          match (fst x).nbe_t with
          | Lazy (Inr (blob, ET_app(head, _)), _)
            when head=Ident.string_of_lid PC.immutable_array_t_lid -> Some blob
          | _ -> None
      in
      let length_op =
        let embed_int (r:Range.range) (i:Z.t) : term = embed_simple r i in
        let run_op (blob:FStar.Compiler.Dyn.dyn) : option Z.t =
            Some (BU.array_length #term (FStar.Compiler.Dyn.undyn blob))
        in
        ( PC.immutable_array_length_lid, 2, 1,
          mixed_binary_op arg1_as_elt_t //1st arg of length is the type
                          arg2_as_blob //2nd arg is the IA.t term blob
                          embed_int //the result is just an int, so embed it back
                          (fun _r _universes _ blob -> run_op blob),
          //NBE case is similar
          NBETerm.mixed_binary_op
             (fun (elt_t, _) -> Some elt_t)
             arg2_as_blob_nbe
             (fun (i:Z.t) -> NBETerm.embed NBETerm.e_int bogus_cbs i)
             (fun _universes _ blob -> run_op blob) )
      in
      let index_op =
          (PC.immutable_array_index_lid, 3, 1,
           mixed_ternary_op arg1_as_elt_t //1st arg of index is the type
                            arg2_as_blob //2nd arg is the `IA.t term` blob
                            arg_as_int //3rd arg is an int
                            (fun r tm -> tm) //the result is just a term, so the embedding is the identity
                            (fun r _universes _t blob i -> Some (BU.array_index #term (FStar.Compiler.Dyn.undyn blob) i)),
          NBETerm.mixed_ternary_op
             (fun (elt_t, _) -> Some elt_t)
             arg2_as_blob_nbe //2nd arg is an `IA.t NBEterm.t` blob
             NBETerm.arg_as_int 
             (fun tm -> tm) //In this case, the result is a NBE.t, so embedding is the identity
             (fun _universes _t blob i  -> Some (BU.array_index #NBETerm.t (FStar.Compiler.Dyn.undyn blob) i)))
      in
      List.map (as_primitive_step true)
      [of_list_op; length_op; index_op]

let short_circuit_ops : list primitive_step =
  List.map (as_primitive_step true)
   [(PC.op_And,
         2,
         0,
         and_op,
         (fun _us -> NBETerm.and_op));
     (PC.op_Or,
         2,
         0,
         or_op,
         (fun _us -> NBETerm.or_op));
    ]

let built_in_primitive_steps_list : list primitive_step =
    simple_ops
    @ short_circuit_ops
    @ issue_ops
    @ array_ops
    @ seal_steps
    @ Primops.Erased.ops
    @ Primops.Docs.ops
    @ Primops.MachineInts.ops
    @ Primops.Eq.dec_eq_ops

let equality_ops_list : list primitive_step =
  Primops.Eq.prop_eq_ops