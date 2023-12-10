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
let arg_as_bool   (a:arg) : option bool = fst a |> try_unembed_simple
let arg_as_char   (a:arg) : option char = fst a |> try_unembed_simple
let arg_as_string (a:arg) : option string = fst a |> try_unembed_simple

let arg_as_list {|e:EMB.embedding 'a|} (a:arg)
: option (list 'a)
  = fst a |> try_unembed_simple

let arg_as_doc (a:arg) : option Pprint.document = fst a |> try_unembed_simple

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

let mk1 (f : 'a -> 'b)
        {| EMB.embedding 'a |} {| EMB.embedding 'b |}
: interp_t =
  fun psc cbs us args ->
    match args with
    | [(a1, _)] ->
      let! x = try_unembed_simple a1 in
      let r : 'b = f x in
      return (embed_simple psc.psc_range r)

let mk2 (f : 'a -> 'b -> 'c)
        {| EMB.embedding 'a |} {| EMB.embedding 'b |} {| EMB.embedding 'c |}
: interp_t =
  fun psc cbs us args ->
    match args with
    | [(a1, _); (a2, _)] ->
      let! x = try_unembed_simple a1 in
      let! y = try_unembed_simple a2 in
      let r : 'c = f x y in
      return (embed_simple psc.psc_range r)



(* Most primitive steps don't use the NBE cbs, so they can use this wrapper. *)
let as_primitive_step is_strong (l, arity, u_arity, f, f_nbe) =
  as_primitive_step_nbecbs is_strong (l, arity, u_arity, f, (fun cb univs args -> f_nbe univs args))

let unary_int_op (f:Z.t -> Z.t) =
    unary_op arg_as_int (fun r x -> embed_simple r (f x))

let binary_int_op (f:Z.t -> Z.t -> Z.t) =
    binary_op arg_as_int (fun r x y -> embed_simple r (f x y))

let unary_bool_op (f:bool -> bool) =
    unary_op arg_as_bool (fun r x -> embed_simple r (f x))

let binary_bool_op (f:bool -> bool -> bool) =
    binary_op arg_as_bool (fun r x y -> embed_simple r (f x y))

let binary_string_op (f : string -> string -> string) =
    binary_op arg_as_string (fun r x y -> embed_simple r (f x y))

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

let built_in_primitive_steps_list : list primitive_step =
    let list_of_string' rng (s:string) : term =
        let name l = mk (Tm_fvar (lid_as_fv l None)) rng in
        let char_t = name PC.char_lid in
        let charterm c = mk (Tm_constant (Const_char c)) rng in
        U.mk_list char_t rng <| List.map charterm (list_of_string s)
    in
    let string_of_list' (rng:Range.range) (l:list char) : term =
        let s = string_of_list l in
        U.exp_string s
    in
    let string_compare' rng (s1:string) (s2:string) : term =
        let r = String.compare s1 s2 in
        embed_simple rng (Z.big_int_of_string (BU.string_of_int r))
    in
    let string_concat' psc _n _us args : option term =
        match args with
        | [a1; a2] ->
            begin match arg_as_string a1 with
            | Some s1 ->
                begin match arg_as_list a2 with
                | Some s2 ->
                    let r = String.concat s1 s2 in
                    Some (embed_simple psc.psc_range r)
                | _ -> None
                end
            | _ -> None
            end
        | _ -> None
    in
    let string_split' psc _norm_cb _us args : option term =
        match args with
        | [a1; a2] ->
            begin match arg_as_list a1 with
            | Some s1 ->
                begin match arg_as_string a2 with
                | Some s2 ->
                    let r = String.split s1 s2 in
                    Some (embed_simple psc.psc_range r)
                | _ -> None
                end
            | _ -> None
            end
        | _ -> None
    in
    let string_substring' psc _norm_cb _us args : option term =
        match args with
        | [a1; a2; a3] ->
            begin match arg_as_string a1, arg_as_int a2, arg_as_int a3 with
            | Some s1, Some n1, Some n2 ->
                let n1 = Z.to_int_fs n1 in
                let n2 = Z.to_int_fs n2 in
                (* Might raise an OOB exception, but not if the precondition is proven *)
                begin
                try let r = String.substring s1 n1 n2 in
                    Some (embed_simple psc.psc_range r)
                with | _ -> None
                end
            | _ -> None
            end
        | _ -> None
    in
    let string_of_int rng (i:Z.t) : term =
        embed_simple rng (Z.string_of_big_int i)
    in
    let string_of_bool rng (b:bool) : term =
        embed_simple rng (if b then "true" else "false")
    in
    let int_of_string rng (s:string) : term =
      let r = BU.safe_int_of_string s in
      embed_simple rng r
    in
    let bool_of_string rng (s:string) : term =
      let r =
        match s with
        | "true" -> Some true
        | "false" -> Some false
        | _ -> None
      in
      embed_simple rng r
    in
    let lowercase rng (s:string) : term =
        embed_simple rng (String.lowercase s)
    in
    let uppercase rng (s:string) : term =
        embed_simple rng (String.uppercase s)
    in
    let string_index psc _norm_cb _us args : option term =
        match args with
        | [a1; a2] ->
            begin match arg_as_string a1, arg_as_int a2 with
            | Some s, Some i ->
              begin
              try let r = String.index s i in
                  Some (embed_simple psc.psc_range r)
              with | _ -> None
              end
            | _  -> None
            end
        | _ -> None
    in
    let string_index_of psc _norm_cb _us args : option term =
        match args with
        | [a1; a2] ->
            begin match arg_as_string a1, arg_as_char a2 with
            | Some s, Some c ->
              begin
              try let r = String.index_of s c in
                  Some (embed_simple psc.psc_range r)
              with | _ -> None
              end
            | _ -> None
            end
        | _ -> None
    in
    let mk_range (psc:psc) _norm_cb _us args : option term =
      match args with
      | [fn; from_line; from_col; to_line; to_col] -> begin
        match arg_as_string fn,
              arg_as_int from_line,
              arg_as_int from_col,
              arg_as_int to_line,
              arg_as_int to_col with
        | Some fn, Some from_l, Some from_c, Some to_l, Some to_c ->
          let r = FStar.Compiler.Range.mk_range fn
                              (FStar.Compiler.Range.mk_pos (Z.to_int_fs from_l) (Z.to_int_fs from_c))
                              (FStar.Compiler.Range.mk_pos (Z.to_int_fs to_l) (Z.to_int_fs to_c)) in
          Some (embed_simple psc.psc_range r)
        | _ -> None
        end
      | _ -> None
    in
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
    in
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
    in
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
    in

    (* division and modulus are special cased since we must avoid zero denominators *)
    let division_modulus_op op : psc -> EMB.norm_cb -> universes -> args -> option term
      = fun psc _norm_cb _us args ->
        match args with
        | [(a1, None); (a2, None)] ->
            begin match try_unembed_simple a1,
                        try_unembed_simple a2 with
            | Some m, Some n ->
              if Z.to_int_fs n <> 0
              then Some (embed_simple psc.psc_range (op m n))
              else None

            | _ -> None
            end
        | _ -> failwith "Unexpected number of arguments"
    in

    let bogus_cbs = {
        NBE.iapp = (fun h _args -> h);
        NBE.translate = (fun _ -> failwith "bogus_cbs translate");
    }
    in
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
      =
        [(PC.op_Minus,
             1,
             0,
             unary_int_op (fun x -> Z.minus_big_int x),
             NBETerm.unary_int_op (fun x -> Z.minus_big_int x));
         (PC.op_Addition,
             2,
             0,
             binary_int_op (fun x y -> Z.add_big_int x y),
             NBETerm.binary_int_op (fun x y -> Z.add_big_int x y));
         (PC.op_Subtraction,
             2,
             0,
             binary_int_op (fun x y -> Z.sub_big_int x y),
             NBETerm.binary_int_op (fun x y -> Z.sub_big_int x y));
         (PC.op_Multiply,
             2,
             0,
             binary_int_op (fun x y -> Z.mult_big_int x y),
             NBETerm.binary_int_op (fun x y -> Z.mult_big_int x y));
         (PC.op_Division,
             2,
             0,
             division_modulus_op Z.div_big_int,
             (fun _us -> NBETerm.division_modulus_op Z.div_big_int));
         (PC.op_LT,
             2,
             0,
             binary_op arg_as_int (fun r x y -> embed_simple r (Z.lt_big_int x y)),
             NBETerm.binary_op NBETerm.arg_as_int (fun x y -> NBETerm.embed NBETerm.e_bool bogus_cbs (Z.lt_big_int x y)));
         (PC.op_LTE,
             2,
             0,
             binary_op arg_as_int (fun r x y -> embed_simple r (Z.le_big_int x y)),
             NBETerm.binary_op NBETerm.arg_as_int (fun  x y -> NBETerm.embed NBETerm.e_bool bogus_cbs (Z.le_big_int x y)));
         (PC.op_GT,
             2,
             0,
             binary_op arg_as_int (fun r x y -> embed_simple r (Z.gt_big_int x y)),
             NBETerm.binary_op NBETerm.arg_as_int (fun x y -> NBETerm.embed NBETerm.e_bool bogus_cbs (Z.gt_big_int x y)));
         (PC.op_GTE,
             2,
             0,
             binary_op arg_as_int (fun r x y -> embed_simple r (Z.ge_big_int x y)),
             NBETerm.binary_op NBETerm.arg_as_int (fun x y -> NBETerm.embed NBETerm.e_bool bogus_cbs (Z.ge_big_int x y)));
         (PC.op_Modulus,
             2,
             0,
             division_modulus_op Z.mod_big_int,
             (fun _us -> NBETerm.division_modulus_op Z.mod_big_int));
         (PC.op_Negation,
             1,
             0,
             unary_bool_op (fun x -> not x),
             NBETerm.unary_bool_op (fun x -> not x));
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
         (let u32_int_to_t =
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
         (PC.string_of_int_lid,
             1,
             0,
             unary_op arg_as_int string_of_int,
             NBETerm.unary_op NBETerm.arg_as_int NBETerm.string_of_int);
         (PC.string_of_bool_lid,
             1,
             0,
             unary_op arg_as_bool string_of_bool,
             NBETerm.unary_op NBETerm.arg_as_bool NBETerm.string_of_bool);

         (PC.bool_of_string_lid,
             1,
             0,
             unary_op arg_as_string bool_of_string,
             NBETerm.unary_op NBETerm.arg_as_string NBETerm.bool_of_string);
         (PC.int_of_string_lid,
             1,
             0,
             unary_op arg_as_string int_of_string,
             NBETerm.unary_op NBETerm.arg_as_string NBETerm.int_of_string);
(* Operations from FStar.String *)
         (PC.string_list_of_string_lid,
             1,
             0,
             unary_op arg_as_string list_of_string',
             NBETerm.unary_op NBETerm.arg_as_string NBETerm.list_of_string');
         (PC.string_string_of_list_lid,
             1,
             0,
             unary_op arg_as_list string_of_list',
             NBETerm.unary_op (NBETerm.arg_as_list NBETerm.e_char) NBETerm.string_of_list');
         (PC.string_make_lid,
             2,
             0,
             mixed_binary_op
                   (fun (x:arg) -> arg_as_int x <: option Z.t)
                   (fun (x:arg) -> arg_as_char x <: option char)
                   (fun (r:Range.range) (s:string) -> embed_simple r s)
                   (fun (r:Range.range) _us (x:BigInt.t) (y:char) -> Some (String.make (BigInt.to_int_fs x) y)),
             NBETerm.mixed_binary_op
                   NBETerm.arg_as_int
                   NBETerm.arg_as_char
                   (NBETerm.embed NBETerm.e_string bogus_cbs)
                   (fun _us (x:BigInt.t) (y:char) -> Some (String.make (BigInt.to_int_fs x) y)));
         (PC.string_split_lid,
             2,
             0,
             string_split',
             (fun _ -> NBETerm.string_split'));
         (PC.prims_strcat_lid,
             2,
             0,
             binary_string_op (fun x y -> x ^ y),
             NBETerm.binary_string_op (fun x y -> x ^ y));
         (PC.string_concat_lid,
             2,
             0,
             string_concat',
             (fun _ -> NBETerm.string_concat'));
         (PC.string_compare_lid,
             2,
             0,
             binary_op arg_as_string string_compare',
             NBETerm.binary_op NBETerm.arg_as_string NBETerm.string_compare');
         (PC.string_lowercase_lid,
             1,
             0,
             unary_op arg_as_string lowercase,
             NBETerm.unary_op NBETerm.arg_as_string NBETerm.string_lowercase);
         (PC.string_uppercase_lid,
             1,
             0,
             unary_op arg_as_string uppercase,
             NBETerm.unary_op NBETerm.arg_as_string NBETerm.string_uppercase);
         (PC.string_index_lid,
             2,
             0,
             string_index,
             (fun _ -> NBETerm.string_index));
         (PC.string_index_of_lid,
             2,
             0,
             string_index_of,
             (fun _ -> NBETerm.string_index_of));
         (PC.string_sub_lid,
             3,
             0,
             string_substring',
             (fun _ -> NBETerm.string_substring'));
(* END FStar.String functions *)
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
         (PC.p2l ["FStar"; "Range"; "mk_range"],
             5,
             0,
             mk_range,
             (fun _ -> NBE.mk_range));
        ]
    in
    (* GM: Just remove strong_reduction_ok? There's currently no operator which requires that
     * and it also seems unlikely since those that cannot work with open term might
     * just fail to unembed their arguments. *)
    let weak_ops =
            [
            ]
    in
    let bounded_arith_ops
        =
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
              (fun (l, q) -> //2nd arg: unembed as a list term
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
          //unembed an arg as a IA.t blob if the emb_typ
          //of the lkind tells us it has the right type
          match (SS.compress (fst x)).n with
          | Tm_lazy {blob=blob; lkind=Lazy_embedding (ET_app(head, _), _)}
            when head=Ident.string_of_lid PC.immutable_array_t_lid -> Some blob
          | _ -> None
      in
      let arg2_as_blob_nbe (x:NBETerm.arg) : option FStar.Compiler.Dyn.dyn =
          //unembed an arg as a IA.t blob if the emb_typ
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
    let issue_ops =
        let mk_lid l = PC.p2l ["FStar"; "Issue"; l] in
        let arg_as_issue (x:arg) : option Errors.issue =
            EMB.(try_unembed (fst x) id_norm_cb)
        in
        let option_int_as_option_z oi = 
          match oi with
          | None -> None
          | Some i -> (Some (Z.of_int_fs i))
        in
        let option_z_as_option_int zi = 
          match zi with
          | None -> None
          | Some i -> (Some (Z.to_int_fs i))
        in
        let nbe_arg_as_issue (x:NBETerm.arg) : option Errors.issue =
          FStar.TypeChecker.NBETerm.(unembed e_issue bogus_cbs (fst x))
        in
        let nbe_str s = FStar.TypeChecker.NBETerm.(embed e_string bogus_cbs s) in
        let nbe_int s = FStar.TypeChecker.NBETerm.(embed e_int bogus_cbs s) in
        let nbe_option_int oi =
          let em = FStar.TypeChecker.NBETerm.(embed (e_option e_int) bogus_cbs) in 
          em (option_int_as_option_z oi)
        in
        [
        (mk_lid "message_of_issue", 1, 0,
         unary_op arg_as_issue
                  (fun _r issue -> EMB.(embed_simple Range.dummyRange issue.issue_msg)),
         NBETerm.unary_op
                  nbe_arg_as_issue
                  (fun issue -> FStar.TypeChecker.NBETerm.(embed (e_list e_document) bogus_cbs issue.issue_msg)));
        (mk_lid "level_of_issue", 1, 0,
         unary_op arg_as_issue
                  (fun _r issue -> U.exp_string (Errors.string_of_issue_level issue.issue_level)),
         NBETerm.unary_op
                  nbe_arg_as_issue
                  (fun issue -> nbe_str (Errors.string_of_issue_level issue.issue_level)));
        (mk_lid "number_of_issue", 1, 0,
         unary_op arg_as_issue
                  (fun _r issue -> EMB.(embed_simple Range.dummyRange 
                                                      (option_int_as_option_z issue.issue_number))),
         NBETerm.unary_op
                  nbe_arg_as_issue
                  (fun issue -> nbe_option_int issue.issue_number));
        (mk_lid "range_of_issue", 1, 0,
         unary_op arg_as_issue
                  (fun _r issue -> EMB.(embed_simple Range.dummyRange 
                                                      issue.issue_range)),
         NBETerm.unary_op
                  nbe_arg_as_issue
                  (fun issue -> FStar.TypeChecker.NBETerm.(embed (e_option e_range) bogus_cbs
                                                      issue.issue_range)));
        (mk_lid "context_of_issue", 1, 0,
         unary_op arg_as_issue
                  (fun _r issue -> EMB.(embed_simple Range.dummyRange 
                                                      issue.issue_ctx)),
         NBETerm.unary_op
                  nbe_arg_as_issue
                  (fun issue -> FStar.TypeChecker.NBETerm.(embed (e_list e_string) bogus_cbs
                                                      issue.issue_ctx)));

        (mk_lid "render_issue", 1, 0,
         unary_op arg_as_issue
                  (fun _r issue -> U.exp_string (Errors.format_issue issue)),
         NBETerm.unary_op
                  nbe_arg_as_issue
                  (fun issue -> nbe_str (Errors.format_issue issue)));

        (mk_lid "mk_issue_doc", 5, 0,
          (fun psc univs cbs args -> 
            match args with
            | [(level, _); (msg, _); (range, _); (number, _); (context, _)] ->
              begin
              let open EMB in
              let try_unembed (#a:Type) (e:embedding a) (x:term) : option a =
                  try_unembed x id_norm_cb
              in
              match try_unembed e_string level,
                    try_unembed (e_list e_document) msg,
                    try_unembed (e_option e_range) range,
                    try_unembed (e_option e_int) number,
                    try_unembed (e_list e_string) context with
              | Some level, Some msg, Some range, Some number, Some context ->
                let issue = {issue_level = Errors.issue_level_of_string level;
                             issue_range = range;
                             issue_number = option_z_as_option_int number;
                             issue_msg = msg;
                             issue_ctx = context} in
                Some (embed_simple psc.psc_range issue)
              | _ -> None
              end
            | _ -> None),
          (fun univs args -> 
            match args with
            | [(level, _); (msg, _); (range, _); (number, _); (context, _)] ->
              begin
              let open FStar.TypeChecker.NBETerm in 
              let try_unembed (#a:Type) (e:embedding a) (x:NBETerm.t) : option a =
                  unembed e bogus_cbs x
              in
              match try_unembed e_string level,
                    try_unembed (e_list e_document) msg,
                    try_unembed (e_option e_range) range,
                    try_unembed (e_option e_int) number,
                    try_unembed (e_list e_string) context with
              | Some level, Some msg, Some range, Some number, Some context ->
                let issue = {issue_level = Errors.issue_level_of_string level;
                             issue_range = range;
                             issue_number = option_z_as_option_int number;
                             issue_msg = msg;
                             issue_ctx = context} in
                Some (NBETerm.embed e_issue bogus_cbs issue)
              | _ -> None
              end
            | _ -> None))
        ]
    in
    let doc_ops =
        let mk_lid l = PC.p2l ["FStar"; "Stubs"; "Pprint"; l] in
        (* FIXME: we only implement the absolute minimum. The rest of the operations
        are availabe to plugins. *)
        [
        (mk_lid "arbitrary_string", 1, 0,
         unary_op arg_as_string
                  (fun r str ->
                  embed_simple r (FStar.Pprint.arbitrary_string str)),
         NBETerm.unary_op NBETerm.arg_as_string
                  (fun str -> NBETerm.embed NBETerm.e_document bogus_cbs (FStar.Pprint.arbitrary_string str)));

        (mk_lid "render", 1, 0,
         unary_op arg_as_doc
                  (fun r doc ->
                  embed_simple r (FStar.Pprint.render doc)),
         NBETerm.unary_op NBETerm.arg_as_doc
                  (fun doc -> NBETerm.embed NBETerm.e_string bogus_cbs (FStar.Pprint.render doc)));
        ]

    in
    let seal_steps =
      [
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
    in
    let strong_steps =
      List.map (as_primitive_step true)
               (basic_ops@bounded_arith_ops@[reveal_hide]@array_ops@issue_ops@doc_ops)
      @
      List.map (fun p -> { as_primitive_step_nbecbs true p with renorm_after = true})
               seal_steps
    in
    let weak_steps = List.map (as_primitive_step false) weak_ops in
    strong_steps @ weak_steps

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
