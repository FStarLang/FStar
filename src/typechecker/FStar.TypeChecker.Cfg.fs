#light "off"
module FStar.TypeChecker.Cfg
open FStar.ST
open FStar.All
open FStar
open FStar.String
open FStar.Const
open FStar.Char
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.TypeChecker
open FStar.TypeChecker.Env

module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module BU = FStar.Util
module FC = FStar.Const
module PC = FStar.Parser.Const
module U  = FStar.Syntax.Util
module I  = FStar.Ident
module EMB = FStar.Syntax.Embeddings
module Z = FStar.BigInt
module NBE = FStar.TypeChecker.NBETerm

type fsteps = {
     beta : bool;
     iota : bool;
     zeta : bool;
     weak : bool;
     hnf  : bool;
     primops : bool;
     do_not_unfold_pure_lets : bool;
     unfold_until : option<S.delta_depth>;
     unfold_only : option<list<I.lid>>;
     unfold_fully : option<list<I.lid>>;
     unfold_attr : option<list<attribute>>;
     unfold_tac : bool;
     pure_subterms_within_computations : bool;
     simplify : bool;
     erase_universes : bool;
     allow_unbound_universes : bool;
     reify_ : bool; // fun fact: calling it 'reify' won't bootstrap :)
     compress_uvars : bool;
     no_full_norm : bool;
     check_no_uvars : bool;
     unmeta : bool;
     unascribe : bool;
     in_full_norm_request: bool;
     weakly_reduce_scrutinee:bool;
     nbe_step:bool;
}

let steps_to_string f =
  let format_opt (f:'a -> string) (o:option<'a>) =
    match o with
    | None -> "None"
    | Some x -> "Some ("^ f x ^ ")"
  in
  let b = BU.string_of_bool in
  BU.format
  "{\n\
    beta = %s;\n\
    iota = %s;\n\
    zeta = %s;\n\
    weak = %s;\n\
    hnf  = %s;\n\
    primops = %s;\n\
    do_not_unfold_pure_lets = %s;\n\
    unfold_until = %s;\n\
    unfold_only = %s;\n\
    unfold_fully = %s;\n\
    unfold_attr = %s;\n\
    unfold_tac = %s;\n\
    pure_subterms_within_computations = %s;\n\
    simplify = %s;\n\
    erase_universes = %s;\n\
    allow_unbound_universes = %s;\n\
    reify_ = %s;\n\
    compress_uvars = %s;\n\
    no_full_norm = %s;\n\
    check_no_uvars = %s;\n\
    unmeta = %s;\n\
    unascribe = %s;\n\
    in_full_norm_request = %s;\n\
    weakly_reduce_scrutinee = %s;\n\
  }"
  [ f.beta |> b;
    f.iota |> b;
    f.zeta |> b;
    f.weak |> b;
    f.hnf  |> b;
    f.primops |> b;
    f.do_not_unfold_pure_lets |> b;
    f.unfold_until |> format_opt Print.delta_depth_to_string;
    f.unfold_only |> format_opt (fun x -> List.map Ident.string_of_lid x |> String.concat ", ");
    f.unfold_fully |> format_opt (fun x -> List.map Ident.string_of_lid x |> String.concat ", ");
    f.unfold_attr |> format_opt (fun xs -> List.map Print.term_to_string xs |> String.concat ", ");
    f.unfold_tac |> b;
    f.pure_subterms_within_computations |> b;
    f.simplify |> b;
    f.erase_universes |> b;
    f.allow_unbound_universes |> b;
    f.reify_ |> b;
    f.compress_uvars |> b;
    f.no_full_norm |> b;
    f.check_no_uvars |> b;
    f.unmeta |> b;
    f.unascribe |> b;
    f.in_full_norm_request |> b;
    f.weakly_reduce_scrutinee |> b]

let default_steps : fsteps = {
    beta = true;
    iota = true;
    zeta = true;
    weak = false;
    hnf  = false;
    primops = false;
    do_not_unfold_pure_lets = false;
    unfold_until = None;
    unfold_only = None;
    unfold_fully = None;
    unfold_attr = None;
    unfold_tac = false;
    pure_subterms_within_computations = false;
    simplify = false;
    erase_universes = false;
    allow_unbound_universes = false;
    reify_ = false;
    compress_uvars = false;
    no_full_norm = false;
    check_no_uvars = false;
    unmeta = false;
    unascribe = false;
    in_full_norm_request = false;
    weakly_reduce_scrutinee = true;
    nbe_step = false;
}

let fstep_add_one s fs =
    let add_opt x = function
        | None -> Some [x]
        | Some xs -> Some (x::xs)
    in
    match s with
    | Beta -> { fs with beta = true }
    | Iota -> { fs with iota = true }
    | Zeta -> { fs with zeta = true }
    | Exclude Beta -> { fs with beta = false }
    | Exclude Iota -> { fs with iota = false }
    | Exclude Zeta -> { fs with zeta = false }
    | Exclude _ -> failwith "Bad exclude"
    | Weak -> { fs with weak = true }
    | HNF -> { fs with hnf = true }
    | Primops -> { fs with primops = true }
    | Eager_unfolding -> fs // eager_unfolding is not a step
    | Inlining -> fs // not a step // ZP : Adding qualification because of name clash
    | DoNotUnfoldPureLets ->  { fs with do_not_unfold_pure_lets = true }
    | UnfoldUntil d -> { fs with unfold_until = Some d }
    | UnfoldOnly  lids -> { fs with unfold_only  = Some lids }
    | UnfoldFully lids -> { fs with unfold_fully = Some lids }
    | UnfoldAttr attr -> { fs with unfold_attr = add_opt attr fs.unfold_attr }
    | UnfoldTac ->  { fs with unfold_tac = true }
    | PureSubtermsWithinComputations ->  { fs with pure_subterms_within_computations = true }
    | Simplify ->  { fs with simplify = true }
    | EraseUniverses ->  { fs with erase_universes = true }
    | AllowUnboundUniverses ->  { fs with allow_unbound_universes = true }
    | Reify ->  { fs with reify_ = true }
    | CompressUvars ->  { fs with compress_uvars = true }
    | NoFullNorm ->  { fs with no_full_norm = true }
    | CheckNoUvars ->  { fs with check_no_uvars = true }
    | Unmeta ->  { fs with unmeta = true }
    | Unascribe ->  { fs with unascribe = true }
    | NBE -> {fs with nbe_step = true }

let to_fsteps (s : list<step>) : fsteps =
    List.fold_right fstep_add_one s default_steps

type psc = {
     psc_range:FStar.Range.range;
     psc_subst: unit -> subst_t // potentially expensive, so thunked
}

let null_psc = { psc_range = Range.dummyRange ; psc_subst = fun () -> [] }
let psc_range psc = psc.psc_range
let psc_subst psc = psc.psc_subst ()

type debug_switches = {
    gen              : bool;
    top              : bool;
    cfg              : bool;
    primop           : bool;
    unfolding        : bool;
    b380             : bool;
    wpe              : bool;
    norm_delayed     : bool;
    print_normalized : bool;
}

type primitive_step = {
     name:Ident.lid;
     arity:int;
     univ_arity:int;
     auto_reflect:option<int>;
     strong_reduction_ok:bool;
     requires_binder_substitution:bool;
     interpretation:(psc -> EMB.norm_cb -> args -> option<term>);
     interpretation_nbe:(NBETerm.args -> option<NBETerm.t>)
}

type cfg = {
     steps: fsteps;
     tcenv: Env.env;
     debug: debug_switches;
     delta_level: list<Env.delta_level>;  // Controls how much unfolding of definitions should be performed
     primitive_steps:BU.psmap<primitive_step>;
     strong : bool;                       // under a binder
     memoize_lazy : bool;
     normalize_pure_lets: bool;
     reifying : bool;
}

let cfg_to_string cfg =
    String.concat "\n"
        ["{";
         BU.format1 "  steps = %s" (steps_to_string cfg.steps);
         "}" ]

let cfg_env cfg = cfg.tcenv

let add_steps (m : BU.psmap<primitive_step>) (l : list<primitive_step>) : BU.psmap<primitive_step> =
    List.fold_right (fun p m -> BU.psmap_add m (I.text_of_lid p.name) p) l m

let prim_from_list (l : list<primitive_step>) : BU.psmap<primitive_step> =
    add_steps (BU.psmap_empty ()) l

let find_prim_step cfg fv =
    BU.psmap_try_find cfg.primitive_steps (I.text_of_lid fv.fv_name.v)

let is_prim_step cfg fv =
    BU.is_some (BU.psmap_try_find cfg.primitive_steps (I.text_of_lid fv.fv_name.v))



let log cfg f =
    if cfg.debug.gen then f () else ()

let log_top cfg f =
    if cfg.debug.top then f () else ()

let log_cfg cfg f =
    if cfg.debug.cfg then f () else ()

let log_primops cfg f =
    if cfg.debug.primop then f () else ()

let log_unfolding cfg f =
    if cfg.debug.unfolding then f () else ()

let log_nbe cfg f =
    if Env.debug cfg.tcenv <| Options.Other "NBE"
    then f()


(*******************************************************************)
(* Semantics for primitive operators (+, -, >, &&, ...)            *)
(*******************************************************************)
let embed_simple (emb:EMB.embedding<'a>) (r:Range.range) (x:'a) : term =
    EMB.embed emb x r None EMB.id_norm_cb
let try_unembed_simple (emb:EMB.embedding<'a>) (x:term) : option<'a> =
    EMB.unembed emb x false EMB.id_norm_cb
let mk t r = mk t None r
let built_in_primitive_steps : BU.psmap<primitive_step> =
    let arg_as_int    (a:arg) = fst a |> try_unembed_simple EMB.e_int in
    let arg_as_bool   (a:arg) = fst a |> try_unembed_simple EMB.e_bool in
    let arg_as_char   (a:arg) = fst a |> try_unembed_simple EMB.e_char in
    let arg_as_string (a:arg) = fst a |> try_unembed_simple EMB.e_string in
    let arg_as_list   (e:EMB.embedding<'a>) a = fst a |> try_unembed_simple (EMB.e_list e) in
    let arg_as_bounded_int (a, _) : option<(fv * Z.t)> =
        match (SS.compress a).n with
        | Tm_app ({n=Tm_fvar fv1}, [({n=Tm_constant (FC.Const_int (i, None))}, _)])
            when BU.ends_with (Ident.text_of_lid fv1.fv_name.v) "int_to_t" ->
          Some (fv1, Z.big_int_of_string i)
        | _ -> None
    in
    let lift_unary
        : ('a -> 'b) -> list<option<'a>> ->option<'b>
        = fun f aopts ->
            match aopts with
            | [Some a] -> Some (f a)
            | _ -> None
    in
    let lift_binary
        : ('a -> 'a -> 'b) -> list<option<'a>> -> option<'b>
        = fun f aopts ->
            match aopts with
            | [Some a0; Some a1] -> Some (f a0 a1)
            | _ -> None
    in
    let unary_op
         :  (arg -> option<'a>)
         -> (Range.range -> 'a -> term)
         -> psc
         -> EMB.norm_cb
         -> args
         -> option<term>
         = fun as_a f res norm_cb args -> lift_unary (f res.psc_range) (List.map as_a args)
    in
    let binary_op
         :  (arg -> option<'a>)
         -> (Range.range -> 'a -> 'a -> term)
         -> psc
         -> EMB.norm_cb
         -> args
         -> option<term>
         = fun as_a f res n args -> lift_binary (f res.psc_range) (List.map as_a args)
    in
    let as_primitive_step is_strong (l, arity, u_arity, f, f_nbe) = {
        name=l;
        arity=arity;
        univ_arity=u_arity;
        auto_reflect=None;
        strong_reduction_ok=is_strong;
        requires_binder_substitution=false;
        interpretation=f;
        interpretation_nbe=f_nbe
    } in
    let unary_int_op (f:Z.t -> Z.t) =
        unary_op arg_as_int (fun r x -> embed_simple EMB.e_int r (f x))
    in
    let binary_int_op (f:Z.t -> Z.t -> Z.t) =
        binary_op arg_as_int (fun r x y -> embed_simple EMB.e_int r (f x y))
    in
    let unary_bool_op (f:bool -> bool) =
        unary_op arg_as_bool (fun r x -> embed_simple EMB.e_bool r (f x))
    in
    let binary_bool_op (f:bool -> bool -> bool) =
        binary_op arg_as_bool (fun r x y -> embed_simple EMB.e_bool r (f x y))
    in
    let binary_string_op (f : string -> string -> string) =
        binary_op arg_as_string (fun r x y -> embed_simple EMB.e_string r (f x y))
    in
    let mixed_binary_op
           :  (arg -> option<'a>)
           -> (arg -> option<'b>)
           -> (Range.range -> 'c -> term)
           -> (Range.range -> 'a -> 'b -> 'c)
           -> psc
           -> EMB.norm_cb
           -> args
           -> option<term>
           = fun as_a as_b embed_c f res _norm_cb args ->
                 match args with
                 | [a;b] ->
                    begin
                    match as_a a, as_b b with
                    | Some a, Some b -> Some (embed_c res.psc_range (f res.psc_range a b))
                    | _ -> None
                    end
                 | _ -> None
    in
    let list_of_string' rng (s:string) : term =
        let name l = mk (Tm_fvar (lid_as_fv l delta_constant None)) rng in
        let char_t = name PC.char_lid in
        let charterm c = mk (Tm_constant (Const_char c)) rng in
        U.mk_list char_t rng <| List.map charterm (list_of_string s)
    in
    let string_of_list' rng (l:list<char>) : term =
        let s = string_of_list l in
        U.exp_string s
    in
    let string_compare' rng (s1:string) (s2:string) : term =
        let r = String.compare s1 s2 in
        embed_simple EMB.e_int rng (Z.big_int_of_string (BU.string_of_int r))
    in
    let string_concat' psc _n args : option<term> =
        match args with
        | [a1; a2] ->
            begin match arg_as_string a1 with
            | Some s1 ->
                begin match arg_as_list EMB.e_string a2 with
                | Some s2 ->
                    let r = String.concat s1 s2 in
                    Some (embed_simple EMB.e_string psc.psc_range r)
                | _ -> None
                end
            | _ -> None
            end
        | _ -> None
    in
    let string_split' psc _norm_cb args : option<term> =
        match args with
        | [a1; a2] ->
            begin match arg_as_list EMB.e_char a1 with
            | Some s1 ->
                begin match arg_as_string a2 with
                | Some s2 ->
                    let r = String.split s1 s2 in
                    Some (embed_simple (EMB.e_list EMB.e_string) psc.psc_range r)
                | _ -> None
                end
            | _ -> None
            end
        | _ -> None
    in
    let string_substring' psc _norm_cb args : option<term> =
        match args with
        | [a1; a2; a3] ->
            begin match arg_as_string a1, arg_as_int a2, arg_as_int a3 with
            | Some s1, Some n1, Some n2 ->
                let n1 = Z.to_int_fs n1 in
                let n2 = Z.to_int_fs n2 in
                (* Might raise an OOB exception *)
                begin
                try let r = String.substring s1 n1 n2 in
                    Some (embed_simple EMB.e_string psc.psc_range r)
                with | _ -> None
                end
            | _ -> None
            end
        | _ -> None
    in
    let string_of_int rng (i:Z.t) : term =
        embed_simple EMB.e_string rng (Z.string_of_big_int i)
    in
    let string_of_bool rng (b:bool) : term =
        embed_simple EMB.e_string rng (if b then "true" else "false")
    in
    let mk_range (psc:psc) _norm_cb args : option<term> =
      match args with
      | [fn; from_line; from_col; to_line; to_col] -> begin
        match arg_as_string fn,
              arg_as_int from_line,
              arg_as_int from_col,
              arg_as_int to_line,
              arg_as_int to_col with
        | Some fn, Some from_l, Some from_c, Some to_l, Some to_c ->
          let r = FStar.Range.mk_range fn
                              (FStar.Range.mk_pos (Z.to_int_fs from_l) (Z.to_int_fs from_c))
                              (FStar.Range.mk_pos (Z.to_int_fs to_l) (Z.to_int_fs to_c)) in
          Some (embed_simple EMB.e_range psc.psc_range r)
        | _ -> None
        end
      | _ -> None
    in
    let decidable_eq (neg:bool) (psc:psc) _norm_cb (args:args)
        : option<term> =
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
    (* Really an identity, but only when the thing is an embedded range *)
    let prims_to_fstar_range_step psc _norm_cb args : option<term> =
        match args with
        | [(a1, _)] ->
            begin match try_unembed_simple EMB.e_range a1 with
            | Some r -> Some (embed_simple EMB.e_range psc.psc_range r)
            | None -> None
            end
        | _ -> failwith "Unexpected number of arguments"
    in
    let basic_ops 
      //this type annotation has to be on a single line for it to parse
      //because our support for F# style type-applications is very limited
      : list<(Ident.lid * int * int * (psc -> EMB.norm_cb -> args -> option<term>) * (NBETerm.args -> option<NBETerm.t>))>
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
             binary_int_op (fun x y -> Z.div_big_int x y),
             NBETerm.binary_int_op (fun x y -> Z.div_big_int x y));
         (PC.op_LT,
             2,
             0,
             binary_op arg_as_int (fun r x y -> embed_simple EMB.e_bool r (Z.lt_big_int x y)),
             NBETerm.binary_op NBETerm.arg_as_int (fun x y -> NBETerm.embed NBETerm.e_bool (Z.lt_big_int x y)));
         (PC.op_LTE,
             2,
             0,
             binary_op arg_as_int (fun r x y -> embed_simple EMB.e_bool r (Z.le_big_int x y)),
             NBETerm.binary_op NBETerm.arg_as_int (fun  x y -> NBETerm.embed NBETerm.e_bool (Z.le_big_int x y)));
         (PC.op_GT,
             2,
             0,
             binary_op arg_as_int (fun r x y -> embed_simple EMB.e_bool r (Z.gt_big_int x y)),
             NBETerm.binary_op NBETerm.arg_as_int (fun x y -> NBETerm.embed NBETerm.e_bool (Z.gt_big_int x y)));
         (PC.op_GTE,
             2,
             0,
             binary_op arg_as_int (fun r x y -> embed_simple EMB.e_bool r (Z.ge_big_int x y)),
             NBETerm.binary_op NBETerm.arg_as_int (fun x y -> NBETerm.embed NBETerm.e_bool (Z.ge_big_int x y)));
         (PC.op_Modulus,
             2,
             0,
             binary_int_op (fun x y -> Z.mod_big_int x y),
             NBETerm.binary_int_op (fun x y -> Z.mod_big_int x y));
         (PC.op_Negation,
             1,
             0,
             unary_bool_op (fun x -> not x),
             NBETerm.unary_bool_op (fun x -> not x));
         (PC.op_And,
             2,
             0,
             binary_bool_op (fun x y -> x && y),
             NBETerm.binary_bool_op (fun x y -> x && y));
         (PC.op_Or,
             2,
             0,
             binary_bool_op (fun x y -> x || y),
             NBETerm.binary_bool_op (fun x y -> x || y));
         (PC.strcat_lid,
             2,
             0,
             binary_string_op (fun x y -> x ^ y),
             NBETerm.binary_string_op (fun x y -> x ^ y));
         (PC.strcat_lid',
             2,
             0,
             binary_string_op (fun x y -> x ^ y),
             NBETerm.binary_string_op (fun x y -> x ^ y));
         (PC.str_make_lid,
             2,
             0,
             mixed_binary_op
                   arg_as_int
                   arg_as_char
                   (embed_simple EMB.e_string)
                   (fun r (x:BigInt.t) (y:char) -> FStar.String.make (BigInt.to_int_fs x) y),
             NBETerm.mixed_binary_op
                   NBETerm.arg_as_int
                   NBETerm.arg_as_char
                   (NBETerm.embed NBETerm.e_string)
                   (fun (x:BigInt.t) (y:char) -> FStar.String.make (BigInt.to_int_fs x) y));
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
         (PC.string_compare,
             2,
             0,
             binary_op arg_as_string string_compare',
             NBETerm.binary_op NBETerm.arg_as_string NBETerm.string_compare');
         (PC.op_Eq,
             3,
             1,
             decidable_eq false,
             NBETerm.decidable_eq false);
         (PC.op_notEq,
             3,
             1,
             decidable_eq true,
             NBETerm.decidable_eq true);
         (PC.p2l ["FStar"; "String"; "list_of_string"],
             1,
             0,
             unary_op arg_as_string list_of_string',
             NBETerm.unary_op NBETerm.arg_as_string NBETerm.list_of_string');
         (PC.p2l ["FStar"; "String"; "string_of_list"],
             1,
             0,
             unary_op (arg_as_list EMB.e_char) string_of_list',
             NBETerm.unary_op (NBETerm.arg_as_list NBETerm.e_char) NBETerm.string_of_list');
         (PC.p2l ["FStar"; "String"; "split"],
             2,
             0,
             string_split',
             NBETerm.string_split');
         (PC.p2l ["FStar"; "String"; "substring"],
             3,
             0,
             string_substring',
             NBETerm.string_substring');
         (PC.p2l ["FStar"; "String"; "concat"],
             2,
             0,
             string_concat',
             NBETerm.string_concat');
         (PC.p2l ["Prims"; "mk_range"],
             5,
             0,
             mk_range,
             NBE.mk_range);
         (PC.p2l ["FStar"; "Range"; "prims_to_fstar_range"],
             1, 
             0, 
             prims_to_fstar_range_step, 
             NBE.prims_to_fstar_range_step);
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
           [ "Int8"; "Int16"; "Int32"; "Int64" ]
        in
        let bounded_unsigned_int_types =
           [ "UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]
        in
        let int_as_bounded r int_to_t n =
            let c = embed_simple EMB.e_int r n in
            let int_to_t = S.fv_to_tm int_to_t in
            S.mk_Tm_app int_to_t [S.as_arg c] None r
        in
        let add_sub_mul_v =
          (bounded_signed_int_types @ bounded_unsigned_int_types)
          |> List.collect (fun m ->
            [(PC.p2l ["FStar"; m; "add"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x) (_, y) -> int_as_bounded r int_to_t (Z.add_big_int x y)),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x) (_, y) -> NBETerm.int_as_bounded int_to_t (Z.add_big_int x y)));
             (PC.p2l ["FStar"; m; "sub"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x) (_, y) -> int_as_bounded r int_to_t (Z.sub_big_int x y)),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x) (_, y) -> NBETerm.int_as_bounded int_to_t (Z.sub_big_int x y)));
             (PC.p2l ["FStar"; m; "mul"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x) (_, y) -> int_as_bounded r int_to_t (Z.mult_big_int x y)),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x) (_, y) -> NBETerm.int_as_bounded int_to_t (Z.mult_big_int x y)));
              (PC.p2l ["FStar"; m; "v"],
                  1,
                  0,
                  unary_op
                    arg_as_bounded_int
                    (fun r (int_to_t, x) -> embed_simple EMB.e_int r x),
                  NBETerm.unary_op
                    NBETerm.arg_as_bounded_int
                    (fun (int_to_t, x) -> NBETerm.embed NBETerm.e_int x))])
        in
        let div_mod_unsigned =
          bounded_unsigned_int_types
          |> List.collect (fun m ->
            [(PC.p2l ["FStar"; m; "div"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x) (_, y) -> int_as_bounded r int_to_t (Z.div_big_int x y)),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x) (_, y) -> NBETerm.int_as_bounded int_to_t (Z.div_big_int x y)));
             (PC.p2l ["FStar"; m; "rem"],
                 2,
                 0,
                 binary_op
                   arg_as_bounded_int
                   (fun r (int_to_t, x) (_, y) -> int_as_bounded r int_to_t (Z.mod_big_int x y)),
                 NBETerm.binary_op
                   NBETerm.arg_as_bounded_int
                   (fun (int_to_t, x) (_, y) -> NBETerm.int_as_bounded int_to_t (Z.mod_big_int x y)))
            ])
        in
       add_sub_mul_v
       @ div_mod_unsigned
    in
    let strong_steps = List.map (as_primitive_step true)  (basic_ops@bounded_arith_ops) in
    let weak_steps   = List.map (as_primitive_step false) weak_ops in
    prim_from_list <| (strong_steps @ weak_steps)

let equality_ops : BU.psmap<primitive_step> =
    let interp_prop (psc:psc) _norm_cb (args:args) : option<term> =
        let r = psc.psc_range in
        match args with
        | [(_typ, _); (a1, _); (a2, _)]    //eq2
        | [(_typ, _); _; (a1, _); (a2, _)] ->    //eq3
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
         interpretation = interp_prop;
         interpretation_nbe = NBETerm.interp_prop}
    in
    let hetero_propositional_equality =
        {name = PC.eq3_lid;
         arity = 4;
         univ_arity = 2;
         auto_reflect=None;
         strong_reduction_ok=true;
         requires_binder_substitution=false;
         interpretation = interp_prop;
         interpretation_nbe = NBETerm.interp_prop}
    in

    prim_from_list [propositional_equality; hetero_propositional_equality]



let plugins =
  let plugins = BU.mk_ref [] in
  let register (p:primitive_step) =
      plugins := p :: !plugins
  in
  let retrieve () = !plugins
  in
  register, retrieve

let register_plugin p = fst plugins p
let retrieve_plugins () = snd plugins ()


let config' psteps s e =
    let d = s |> List.collect (function
        | UnfoldUntil k -> [Env.Unfold k]
        | Eager_unfolding -> [Env.Eager_unfolding_only]
        | Inlining -> [Env.InliningDelta]
        | _ -> []) in
    let d = match d with
        | [] -> [Env.NoDelta]
        | _ -> d in
    {tcenv=e;
     debug = { gen = Env.debug e (Options.Other "Norm")
             ; top = Env.debug e (Options.Other "NormTop")
             ; cfg = Env.debug e (Options.Other "NormCfg")
             ; primop = Env.debug e (Options.Other "Primops")
             ; unfolding = Env.debug e (Options.Other "Unfolding")
             ; b380 = Env.debug e (Options.Other "380")
             ; wpe  = Env.debug e (Options.Other "WPE")
             ; norm_delayed = Env.debug e (Options.Other "NormDelayed")
             ; print_normalized = Env.debug e (Options.Other "print_normalized_terms") };
     steps=to_fsteps s;
     delta_level=d;
     primitive_steps= add_steps built_in_primitive_steps (retrieve_plugins () @ psteps);
     strong=false;
     memoize_lazy=true;
     normalize_pure_lets=
       (Options.normalize_pure_terms_for_extraction()
        || not (s |> BU.for_some (eq_step PureSubtermsWithinComputations)));
     reifying=false}

let config s e = config' [] s e
