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

(*******************************************************************)
(* Semantics for primitive operators (+, -, >, &&, ...)            *)
(*******************************************************************)

let null_psc = { psc_range = Range.dummyRange ; psc_subst = fun () -> [] }
let psc_range psc = psc.psc_range
let psc_subst psc = psc.psc_subst ()

let embed_simple {| EMB.embedding 'a |} (r:Range.range) (x:'a) : term =
    EMB.embed x r None EMB.id_norm_cb

let try_unembed_simple {| EMB.embedding 'a |} (x:term) : option 'a =
    EMB.try_unembed x EMB.id_norm_cb

let arg_as_int    (a:arg) : option Z.t = fst a |> try_unembed_simple
let arg_as_char   (a:arg) : option char = fst a |> try_unembed_simple

let arg_as_list {|e:EMB.embedding 'a|} (a:arg)
: option (list 'a)
  = fst a |> try_unembed_simple

let arg_as_bounded_int ((a, _) :arg) : option (fv * Z.t * option S.meta_source_info) =
    let (a, m) =
        (match (SS.compress a).n with
         | Tm_meta {tm=t; meta=Meta_desugared m} -> (t, Some m)
         | _ -> (a, None)) in
    let a = U.unmeta_safe a in
    let hd, args = U.head_and_args_full a in
    let a = U.unlazy_emb a in
    match (SS.compress hd).n, args with
    | Tm_fvar fv1, [(arg, _)]
        when BU.ends_with (Ident.string_of_lid fv1.fv_name.v) "int_to_t" ->
        let arg = U.unlazy_emb arg in
        begin match (SS.compress arg).n with
        | Tm_constant (FC.Const_int (i, None)) ->
            Some (fv1, Z.big_int_of_string i, m)
        | _ ->
            None
        end
    | _ -> None

let lift_unary (f : 'a -> 'b) (aopts : list (option 'a)) : option 'b
    = match aopts with
      | [Some a] -> Some (f a)
      | _ -> None

let lift_binary (f : 'a -> 'a -> 'b) (aopts : list (option 'a)) : option 'b
    = match aopts with
      | [Some a0; Some a1] -> Some (f a0 a1)
      | _ -> None

let unary_op
    (as_a : arg -> option 'a)
    (f : Range.range -> 'a -> term)
    (psc : psc)
    (norm_cb : EMB.norm_cb)
    (_univs : universes)
    (args : args)
  : option term
  = lift_unary (f psc.psc_range) (List.map as_a args)

let binary_op
    (as_a : arg -> option 'a)
    (f : Range.range -> 'a -> 'a -> term)
    (psc : psc)
    (norm_cb : EMB.norm_cb)
    (_univs : universes)
    (args : args)
  : option term
  = lift_binary (f psc.psc_range) (List.map as_a args)
  
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

(* Most primitive steps don't use the NBE cbs, so they can use this wrapper. *)
let as_primitive_step is_strong (l, arity, u_arity, f, f_nbe) =
  as_primitive_step_nbecbs is_strong (l, arity, u_arity, f, (fun cb univs args -> f_nbe univs args))

let solve (#a:Type) {| ev : a |} : Tot a = ev

let mk1 #a #r
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding a |}
  {| EMB.embedding r |} {| NBE.embedding r |}
  (f : a -> r)
  : primitive_step =
  let interp : interp_t =
    fun psc cb us args ->
      match args with
      | [(a, _)] ->
        let! a = try_unembed_simple a in
        return (embed_simple psc.psc_range (f a))
      | _ -> None
  in
  let nbe_interp : nbe_interp_t =
    fun cbs us args ->
      match args with
      | [(a, _)] ->
        let! r = f <$> NBE.unembed solve cbs a in
        return (NBE.embed solve cbs r)
      | _ ->
        None
  in
  as_primitive_step_nbecbs true (name, 1, u_arity, interp, nbe_interp)

let mk2 #a #b #r
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding a |}
  {| EMB.embedding b |} {| NBE.embedding b |}
  {| EMB.embedding r |} {| NBE.embedding r |}
  (f : a -> b -> r)
  : primitive_step =
  let interp : interp_t =
    fun psc cb us args ->
      match args with
      | [(a, _); (b, _)] ->
        let! r = f <$> try_unembed_simple a <*> try_unembed_simple b in
        return (embed_simple psc.psc_range r)
      | _ -> None
  in
  let nbe_interp : nbe_interp_t =
    fun cbs us args ->
      match args with
      | [(a, _); (b, _)] ->
        let! r = f <$> NBE.unembed solve cbs a <*> NBE.unembed solve cbs b in
        return (NBE.embed solve cbs r)
      | _ ->
        None
  in
  as_primitive_step_nbecbs true (name, 2, u_arity, interp, nbe_interp)

(* Duplication for op_Division / op_Modulus which can prevent reduction. The `f`
already returns something in the option monad, so we add an extra join. *)
let mk2' #a #b #r
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding a |}
  {| EMB.embedding b |} {| NBE.embedding b |}
  {| EMB.embedding r |} {| NBE.embedding r |}
  (f : a -> b -> option r)
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
        let! r = f <$> NBE.unembed solve cbs a <*> NBE.unembed solve cbs b in
        let! r = r in
        return (NBE.embed solve cbs r)
      | _ ->
        None
  in
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
  let interp : interp_t =
    fun psc cb us args ->
      match args with
      | [(a, _); (b, _); (c, _)] ->
        let! r = f <$> try_unembed_simple a <*> try_unembed_simple b <*> try_unembed_simple c in
        return (embed_simple psc.psc_range r)
      | _ -> None
  in
  let nbe_interp : nbe_interp_t =
    fun cbs us args ->
      match args with
      | [(a, _); (b, _); (c, _)] ->
        let! r = f <$> NBE.unembed solve cbs a <*> NBE.unembed solve cbs b <*> NBE.unembed solve cbs c in
        return (NBE.embed solve cbs r)
      | _ ->
        None
  in
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
  let interp : interp_t =
    fun psc cb us args ->
      match args with
      | [(a, _); (b, _); (c, _); (d, _); (e, _)] ->
        let! r = f <$> try_unembed_simple a <*> try_unembed_simple b <*> try_unembed_simple c <*> try_unembed_simple d in
        return (embed_simple psc.psc_range r)
      | _ -> None
  in
  let nbe_interp : nbe_interp_t =
    fun cbs us args ->
      match args with
      | [(a, _); (b, _); (c, _); (d, _)] ->
        let! r = f <$> NBE.unembed solve cbs a <*> NBE.unembed solve cbs b <*> NBE.unembed solve cbs c <*> NBE.unembed solve cbs d in
        return (NBE.embed solve cbs r)
      | _ ->
        None
  in
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
  let interp : interp_t =
    fun psc cb us args ->
      match args with
      | [(a, _); (b, _); (c, _); (d, _); (e, _)] ->
        let! r = f <$> try_unembed_simple a <*> try_unembed_simple b <*> try_unembed_simple c <*> try_unembed_simple d <*> try_unembed_simple e in
        return (embed_simple psc.psc_range r)
      | _ -> None
  in
  let nbe_interp : nbe_interp_t =
    fun cbs us args ->
      match args with
      | [(a, _); (b, _); (c, _); (d, _); (e, _)] ->
        let! r = f <$> NBE.unembed solve cbs a <*> NBE.unembed solve cbs b <*> NBE.unembed solve cbs c <*> NBE.unembed solve cbs d <*> NBE.unembed solve cbs e in
        return (NBE.embed solve cbs r)
      | _ ->
        None
  in
  as_primitive_step_nbecbs true (name, 5, u_arity, interp, nbe_interp)

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

let decidable_eq (neg:bool) (psc:psc) _norm_cb _us (args:args)
    : option term =
    let r = psc.psc_range in
    let tru = mk (Tm_constant (FC.Const_bool true)) r in
    let fal = mk (Tm_constant (FC.Const_bool false)) r in
    match args with
    | [(_typ, _); (a1, _); (a2, _)] ->
        (match U.eq_tm a1 a2 with
        | U.Equal -> Some (if neg then fal else tru)
        | U.NotEqual -> Some (if neg then tru else fal)
        | _ -> None)
    | _ ->
        failwith "Unexpected number of arguments"

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
let simple_ops = [
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

  mk2' 0 PC.op_Division (division_modulus_op Z.div_big_int);
  mk2' 0 PC.op_Modulus  (division_modulus_op Z.mod_big_int);

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

let doc_ops =
  let mk_lid l = PC.p2l ["FStar"; "Stubs"; "Pprint"; l] in
    (* FIXME: we only implement the absolute minimum. The rest of the operations
    are availabe to plugins. *)
    let open FStar.Pprint in
    [
      mk1 0 (mk_lid "arbitrary_string") arbitrary_string;
      mk1 0 (mk_lid "render") render;
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

let built_in_primitive_steps_list : list primitive_step =
    let int_as_bounded r int_to_t n =
      let c = embed_simple r n in
      let int_to_t = S.fv_to_tm int_to_t in
      S.mk_Tm_app int_to_t [S.as_arg c] r
    in
    let with_meta_ds r t (m:option meta_source_info) =
      match m with
      | None -> t
      | Some m -> S.mk (Tm_meta {tm=t; meta=Meta_desugared m}) r
    in

    let basic_ops
      //because our support for F# style type-applications is very limited
      : list (Ident.lid * int * int * 
              (psc -> EMB.norm_cb -> universes -> args -> option term) *
              (universes -> NBETerm.args -> option NBETerm.t))
       //name of primitive
          //arity
          //universe arity
          //interp for normalizer
          //interp for NBE
      = [(let u32_int_to_t =
            ["FStar"; "UInt32"; "uint_to_t"]
            |> PC.p2l
            |> (fun l -> S.lid_as_fv l None) in
          PC.char_u32_of_char,
             1,
             0,
             unary_op
               arg_as_char
               (fun r c -> int_as_bounded r u32_int_to_t (c |> BU.int_of_char |> Z.of_int_fs)),
             NBETerm.unary_op
               NBETerm.arg_as_char
               (fun c -> NBETerm.int_as_bounded u32_int_to_t (c |> BU.int_of_char |> Z.of_int_fs)));
         (PC.op_And,
             2,
             0,
             and_op,
             (fun _ -> NBETerm.and_op));
         (PC.op_Or,
             2,
             0,
             or_op,
             (fun _ -> NBETerm.or_op));
         (PC.op_Eq,
             3,
             0,
             decidable_eq false,
             (fun _ -> NBETerm.decidable_eq false));
         (PC.op_notEq,
             3,
             0,
             decidable_eq true,
             (fun _ -> NBETerm.decidable_eq true));
        ]
    in
    let bounded_arith_ops
        =
        (* FIXME: using a newtype with custom embeddings should make this whole
        section very straightforward, as for simple_ops above. *)
        let bounded_signed_int_types =
           [ "Int8", 8; "Int16", 16; "Int32", 32; "Int64", 64 ]
        in
        let bounded_unsigned_int_types =
           [ "UInt8", 8; "UInt16", 16; "UInt32", 32; "UInt64", 64; "UInt128", 128; "SizeT", 64]
        in
        let add_sub_mul_v_comparisons =
          (bounded_signed_int_types @ bounded_unsigned_int_types)
          |> List.collect (fun (m, _) ->
            [(PC.p2l ["FStar"; m; "add"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x, m) (_, y, _) ->
                     with_meta_ds r
                       (int_as_bounded r int_to_t (Z.add_big_int x y)) m) ,
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x, m) (_, y, _) ->
                     NBETerm.with_meta_ds
                       (NBETerm.int_as_bounded int_to_t (Z.add_big_int x y)) m));
             (PC.p2l ["FStar"; m; "sub"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x, m) (_, y, _) ->
                     with_meta_ds r
                       (int_as_bounded r int_to_t (Z.sub_big_int x y)) m),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x, m) (_, y, _) ->
                     NBETerm.with_meta_ds
                       (NBETerm.int_as_bounded int_to_t (Z.sub_big_int x y)) m));
             (PC.p2l ["FStar"; m; "mul"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x, m) (_, y, _) ->
                     with_meta_ds r
                       (int_as_bounded r int_to_t (Z.mult_big_int x y)) m),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x, m) (_, y, _) ->
                     NBETerm.with_meta_ds
                       (NBETerm.int_as_bounded int_to_t (Z.mult_big_int x y)) m));
              (PC.p2l ["FStar"; m; "v"],
                  1,
                  0,
                  unary_op
                    arg_as_bounded_int
                    (fun r (int_to_t, x, m) ->
                      with_meta_ds r (embed_simple r x) m),
                  NBETerm.unary_op
                    NBETerm.arg_as_bounded_int
                    (fun (int_to_t, x, m) ->
                     NBETerm.with_meta_ds
                       (NBETerm.embed NBETerm.e_int bogus_cbs x) m));
             (PC.p2l ["FStar"; m; "gt"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x, m) (_, y, _) ->
                     with_meta_ds r
                       (embed_simple r (Z.gt_big_int x y)) m),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x, m) (_, y, _) ->
                     NBETerm.with_meta_ds
                       (NBETerm.embed NBETerm.e_bool bogus_cbs (Z.gt_big_int x y)) m));
             (PC.p2l ["FStar"; m; "gte"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x, m) (_, y, _) ->
                     with_meta_ds r
                       (embed_simple r (Z.ge_big_int x y)) m),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x, m) (_, y, _) ->
                     NBETerm.with_meta_ds
                       (NBETerm.embed NBETerm.e_bool bogus_cbs (Z.ge_big_int x y)) m));
             (PC.p2l ["FStar"; m; "lt"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x, m) (_, y, _) ->
                     with_meta_ds r
                       (embed_simple r (Z.lt_big_int x y)) m),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x, m) (_, y, _) ->
                     NBETerm.with_meta_ds
                       (NBETerm.embed NBETerm.e_bool bogus_cbs (Z.lt_big_int x y)) m));
             (PC.p2l ["FStar"; m; "lte"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x, m) (_, y, _) ->
                     with_meta_ds r
                       (embed_simple r (Z.le_big_int x y)) m),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x, m) (_, y, _) ->
                     NBETerm.with_meta_ds
                       (NBETerm.embed NBETerm.e_bool bogus_cbs (Z.le_big_int x y)) m));
                       ])
        in
        let unsigned_modulo_add_sub_mul_div_rem =
          bounded_unsigned_int_types
          |> List.collect (fun (m, sz) ->
            let modulus = Z.shift_left_big_int Z.one (Z.of_int_fs sz) in
            let mod x = Z.mod_big_int x modulus in
            //UInt128 does not have a mul_mod
           (if sz = 128
            then []
            else [(PC.p2l ["FStar"; m; "mul_mod"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x, m) (_, y, _) ->
                     with_meta_ds r
                       (int_as_bounded r int_to_t (mod (Z.mult_big_int x y))) m),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x, m) (_, y, _) ->
                     NBETerm.with_meta_ds
                       (NBETerm.int_as_bounded int_to_t (mod (Z.mult_big_int x y))) m))])@
            [(PC.p2l ["FStar"; m; "add_mod"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x, m) (_, y, _) ->
                     with_meta_ds r
                       (int_as_bounded r int_to_t (mod (Z.add_big_int x y))) m),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x, m) (_, y, _) ->
                     NBETerm.with_meta_ds
                       (NBETerm.int_as_bounded int_to_t (mod (Z.add_big_int x y))) m));
             (PC.p2l ["FStar"; m; "sub_mod"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x, m) (_, y, _) ->
                     with_meta_ds r
                       (int_as_bounded r int_to_t (mod (Z.sub_big_int x y))) m),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x, m) (_, y, _) ->
                     NBETerm.with_meta_ds
                       (NBETerm.int_as_bounded int_to_t (mod (Z.sub_big_int x y))) m));
            (PC.p2l ["FStar"; m; "div"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x, m) (_, y, _) ->
                     with_meta_ds r
                       (int_as_bounded r int_to_t (Z.div_big_int x y)) m),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x, m) (_, y, _) ->
                     NBETerm.with_meta_ds
                       (NBETerm.int_as_bounded int_to_t (Z.div_big_int x y)) m));
             (PC.p2l ["FStar"; m; "rem"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x, m) (_, y, _) ->
                     with_meta_ds r
                       (int_as_bounded r int_to_t (Z.mod_big_int x y)) m),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x, m) (_, y, _) ->
                     NBETerm.with_meta_ds
                     (NBETerm.int_as_bounded int_to_t (Z.mod_big_int x y)) m))
            ])
        in
        let mask m =
          match m with
          | "UInt8" -> Z.of_hex "ff"
          | "UInt16" -> Z.of_hex "ffff"
          | "UInt32" -> Z.of_hex "ffffffff"
          | "UInt64" -> Z.of_hex "ffffffffffffffff"
          | "UInt128" -> Z.of_hex "ffffffffffffffffffffffffffffffff"
          | _ -> failwith (BU.format1 "Impossible: bad string on mask: %s\n" m)
        in
        let bitwise =
          bounded_unsigned_int_types
          |> List.collect (fun (m, _) ->
            [
              PC.p2l ["FStar"; m; "logor"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x, m) (_, y, _) ->
                      with_meta_ds r
                        (int_as_bounded r int_to_t (Z.logor_big_int x y)) m),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x, m) (_, y, _) ->
                      NBETerm.with_meta_ds
                        (NBETerm.int_as_bounded int_to_t (Z.logor_big_int x y)) m);
              PC.p2l ["FStar"; m; "logand"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x, m) (_, y, _) ->
                      with_meta_ds r
                        (int_as_bounded r int_to_t (Z.logand_big_int x y)) m),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x, m) (_, y, _) ->
                      NBETerm.with_meta_ds
                        (NBETerm.int_as_bounded int_to_t (Z.logand_big_int x y)) m);
              PC.p2l ["FStar"; m; "logxor"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x, m) (_, y, _) ->
                     with_meta_ds r
                       (int_as_bounded r int_to_t (Z.logxor_big_int x y)) m),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x, m) (_, y, _) ->
                       NBETerm.with_meta_ds
                         (NBETerm.int_as_bounded int_to_t (Z.logxor_big_int x y)) m);
              PC.p2l ["FStar"; m; "lognot"],
                 1,
                 0,
                 unary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x, d) ->
                    with_meta_ds r
                      (int_as_bounded r int_to_t
                        (Z.logand_big_int (Z.lognot_big_int x) (mask m))) d),
                 NBETerm.unary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x, d) ->
                    NBETerm.with_meta_ds
                      (NBETerm.int_as_bounded int_to_t
                        (Z.logand_big_int (Z.lognot_big_int x) (mask m))) d);
              PC.p2l ["FStar"; m; "shift_left"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x, d) (_, y, _) ->
                    with_meta_ds r
                    (int_as_bounded r int_to_t
                      (Z.logand_big_int (Z.shift_left_big_int x y) (mask m))) d),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x, d) (_, y, _) ->
                    NBETerm.with_meta_ds
                    (NBETerm.int_as_bounded int_to_t
                      (Z.logand_big_int (Z.shift_left_big_int x y) (mask m))) d);
              PC.p2l ["FStar"; m; "shift_right"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x, d) (_, y, _) ->
                    with_meta_ds r
                    (int_as_bounded r int_to_t (Z.shift_right_big_int x y)) d),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x, d) (_, y, _) ->
                    NBETerm.with_meta_ds
                    (NBETerm.int_as_bounded int_to_t (Z.shift_right_big_int x y)) d);
            ])
        in
       add_sub_mul_v_comparisons
       @ unsigned_modulo_add_sub_mul_div_rem
       @ bitwise
    in
    let reveal_hide =
      (* unconditionally reduce reveal #t' (hide #t x) to x *)
            PC.reveal,
            2,
            1,
            mixed_binary_op
            (fun x -> Some x)
            (fun (x, _) ->
              let head, args = U.head_and_args x  in
              if U.is_fvar PC.hide head
              then match args with
                   | [_t; (body, _)] -> Some body
                   | _ -> None
              else None)
            (fun r body -> body)
            (fun r _us _t body -> Some body),
            NBETerm.mixed_binary_op
            (fun x -> Some x)
            (fun (x, _) ->
              match NBETerm.nbe_t_of_t x with
              | NBETerm.FV (fv, _, [(_t, _); (body, _)])
                when fv_eq_lid fv PC.hide ->
                Some body
              | _ -> None)
            (fun body -> body)
            (fun _us _t body -> Some body)
    in
    let array_ops =
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
      [of_list_op; length_op; index_op]
    in
    let strong_steps =
      List.map (as_primitive_step true)
               (basic_ops@bounded_arith_ops@[reveal_hide]@array_ops)
    in
    simple_ops @ issue_ops @ doc_ops @ strong_steps @ seal_steps

let equality_ops_list : list primitive_step =
    let interp_prop_eq2 (psc:psc) _norm_cb _univs (args:args) : option term =
        let r = psc.psc_range in
        match args with
        | [(_typ, _); (a1, _); (a2, _)]  ->         //eq2
            (match U.eq_tm a1 a2 with
            | U.Equal -> Some ({U.t_true with pos=r})
            | U.NotEqual -> Some ({U.t_false with pos=r})
            | _ -> None)

        | _ ->
            failwith "Unexpected number of arguments"
    in
    let propositional_equality =
        {name = PC.eq2_lid;
         arity = 3;
         univ_arity = 1;
         auto_reflect=None;
         strong_reduction_ok=true;
         requires_binder_substitution=false;
         renorm_after=false;
         interpretation = interp_prop_eq2;
         interpretation_nbe = fun _cb _univs -> NBETerm.interp_prop_eq2}
    in
    [propositional_equality]