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
     zeta_full : bool;
     weak : bool;
     hnf  : bool;
     primops : bool;
     do_not_unfold_pure_lets : bool;
     unfold_until : option<S.delta_depth>;
     unfold_only  : option<list<I.lid>>;
     unfold_fully : option<list<I.lid>>;
     unfold_attr  : option<list<I.lid>>;
     unfold_qual  : option<list<string>>;
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
     for_extraction:bool
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
    zeta_full = %s;\n\
    weak = %s;\n\
    hnf  = %s;\n\
    primops = %s;\n\
    do_not_unfold_pure_lets = %s;\n\
    unfold_until = %s;\n\
    unfold_only = %s;\n\
    unfold_fully = %s;\n\
    unfold_attr = %s;\n\
    unfold_qual = %s;\n\
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
    for_extraction = %s;\n\
  }"
  [ f.beta |> b;
    f.iota |> b;
    f.zeta |> b;
    f.zeta_full |> b;
    f.weak |> b;
    f.hnf  |> b;
    f.primops |> b;
    f.do_not_unfold_pure_lets |> b;
    f.unfold_until |> format_opt Print.delta_depth_to_string;
    f.unfold_only |> format_opt (fun x -> List.map Ident.string_of_lid x |> String.concat ", ");
    f.unfold_fully |> format_opt (fun x -> List.map Ident.string_of_lid x |> String.concat ", ");
    f.unfold_attr |> format_opt (fun x -> List.map Ident.string_of_lid x |> String.concat ", ");
    f.unfold_qual |> format_opt (String.concat ", ");
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
    f.weakly_reduce_scrutinee |> b;
    f.for_extraction |> b;
   ]

let default_steps : fsteps = {
    beta = true;
    iota = true;
    zeta = true;
    zeta_full = false;
    weak = false;
    hnf  = false;
    primops = false;
    do_not_unfold_pure_lets = false;
    unfold_until = None;
    unfold_only = None;
    unfold_fully = None;
    unfold_attr = None;
    unfold_qual = None;
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
    for_extraction = false
}

let fstep_add_one s fs =
    match s with
    | Beta -> { fs with beta = true }
    | Iota -> { fs with iota = true }
    | Zeta -> { fs with zeta = true }
    | ZetaFull -> { fs with zeta_full = true }
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
    | UnfoldAttr  lids -> { fs with unfold_attr  = Some lids }
    | UnfoldQual  strs ->
      let fs = { fs with unfold_qual  = Some strs } in
      if List.contains "pure_subterms_within_computations" strs
      then {fs with pure_subterms_within_computations = true}
      else fs
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
    | ForExtraction -> {fs with for_extraction = true }

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
    debug_nbe        : bool;
}

let no_debug_switches = {
    gen              = false;
    top              = false;
    cfg              = false;
    primop           = false;
    unfolding        = false;
    b380             = false;
    wpe              = false;
    norm_delayed     = false;
    print_normalized = false;
    debug_nbe        = false;
}

type primitive_step = {
     name:Ident.lid;
     arity:int;
     univ_arity:int;
     auto_reflect:option<int>;
     strong_reduction_ok:bool;
     requires_binder_substitution:bool;
     interpretation:(psc -> EMB.norm_cb -> args -> option<term>);
     interpretation_nbe:(NBETerm.nbe_cbs -> NBETerm.args -> option<NBETerm.t>)
}

(* Primitive step sets. They are represented as a persistent string map *)
type prim_step_set = BU.psmap<primitive_step>

let empty_prim_steps () : prim_step_set =
    BU.psmap_empty ()

let add_step (s : primitive_step) (ss : prim_step_set) =
    BU.psmap_add ss (I.string_of_lid s.name) s

let merge_steps (s1 : prim_step_set) (s2 : prim_step_set) : prim_step_set =
    BU.psmap_merge s1 s2

let add_steps (m : prim_step_set) (l : list<primitive_step>) : prim_step_set =
    List.fold_right add_step l m

let prim_from_list (l : list<primitive_step>) : prim_step_set =
    add_steps (empty_prim_steps ()) l
(* / Primitive step sets *)

type cfg = {
     steps: fsteps;
     tcenv: Env.env;
     debug: debug_switches;
     delta_level: list<Env.delta_level>;  // Controls how much unfolding of definitions should be performed
     primitive_steps:prim_step_set;
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

let find_prim_step cfg fv =
    BU.psmap_try_find cfg.primitive_steps (I.string_of_lid fv.fv_name.v)

let is_prim_step cfg fv =
    BU.is_some (BU.psmap_try_find cfg.primitive_steps (I.string_of_lid fv.fv_name.v))

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
    if cfg.debug.debug_nbe then f ()


(*******************************************************************)
(* Semantics for primitive operators (+, -, >, &&, ...)            *)
(*******************************************************************)
let embed_simple (emb:EMB.embedding<'a>) (r:Range.range) (x:'a) : term =
    EMB.embed emb x r None EMB.id_norm_cb
let try_unembed_simple (emb:EMB.embedding<'a>) (x:term) : option<'a> =
    EMB.unembed emb x false EMB.id_norm_cb
let built_in_primitive_steps : prim_step_set =
    let arg_as_int    (a:arg) = fst a |> try_unembed_simple EMB.e_int in
    let arg_as_bool   (a:arg) = fst a |> try_unembed_simple EMB.e_bool in
    let arg_as_char   (a:arg) = fst a |> try_unembed_simple EMB.e_char in
    let arg_as_string (a:arg) = fst a |> try_unembed_simple EMB.e_string in
    let arg_as_list   (e:EMB.embedding<'a>) a = fst a |> try_unembed_simple (EMB.e_list e) in
    let arg_as_bounded_int (a, _) : option<(fv * Z.t * option<S.meta_source_info>)> =
        let (a, m) =
            (match (SS.compress a).n with
             | Tm_meta(t, Meta_desugared m) -> (t, Some m)
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
        interpretation_nbe=fun _cb -> f_nbe
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
                (* Might raise an OOB exception, but not if the precondition is proven *)
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
    let lowercase rng (s:string) : term =
        embed_simple EMB.e_string rng (String.lowercase s)
    in
    let uppercase rng (s:string) : term =
        embed_simple EMB.e_string rng (String.uppercase s)
    in
    let string_index psc _norm_cb args : option<term> =
        match args with
        | [a1; a2] ->
            begin match arg_as_string a1, arg_as_int a2 with
            | Some s, Some i ->
              begin
              try let r = String.index s i in
                  Some (embed_simple EMB.e_char psc.psc_range r)
              with | _ -> None
              end
            | _  -> None
            end
        | _ -> None
    in
    let string_index_of psc _norm_cb args : option<term> =
        match args with
        | [a1; a2] ->
            begin match arg_as_string a1, arg_as_char a2 with
            | Some s, Some c ->
              begin
              try let r = String.index_of s c in
                  Some (embed_simple EMB.e_int psc.psc_range r)
              with | _ -> None
              end
            | _ -> None
            end
        | _ -> None
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
    (* and_op and or_op are special cased because they are short-circuting,
     * can run without unembedding its second argument. *)
    let and_op : psc -> EMB.norm_cb -> args -> option<term>
      = fun psc _norm_cb args ->
        match args with
        | [(a1, None); (a2, None)] ->
            begin match try_unembed_simple EMB.e_bool a1 with
            | Some false ->
              Some (embed_simple EMB.e_bool psc.psc_range false)
            | Some true ->
              Some a2
            | _ -> None
            end
        | _ -> failwith "Unexpected number of arguments"
    in
    let or_op : psc -> EMB.norm_cb -> args -> option<term>
      = fun psc _norm_cb args ->
        match args with
        | [(a1, None); (a2, None)] ->
            begin match try_unembed_simple EMB.e_bool a1 with
            | Some true ->
              Some (embed_simple EMB.e_bool psc.psc_range true)
            | Some false ->
              Some a2
            | _ -> None
            end
        | _ -> failwith "Unexpected number of arguments"
    in

    (* division is special cased since we must avoid zero denominators *)
    let division_op : psc -> EMB.norm_cb -> args -> option<term>
      = fun psc _norm_cb args ->
        match args with
        | [(a1, None); (a2, None)] ->
            begin match try_unembed_simple EMB.e_int a1,
                        try_unembed_simple EMB.e_int a2 with
            | Some m, Some n ->
              if Z.to_int_fs n <> 0
              then Some (embed_simple EMB.e_int psc.psc_range (Z.div_big_int m n))
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
      let c = embed_simple EMB.e_int r n in
      let int_to_t = S.fv_to_tm int_to_t in
      S.mk_Tm_app int_to_t [S.as_arg c] r
    in
    let with_meta_ds r t (m:option<meta_source_info>) =
      match m with
      | None -> t
      | Some m -> S.mk (Tm_meta(t, Meta_desugared m)) r
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
             division_op,
             NBETerm.division_op);
         (PC.op_LT,
             2,
             0,
             binary_op arg_as_int (fun r x y -> embed_simple EMB.e_bool r (Z.lt_big_int x y)),
             NBETerm.binary_op NBETerm.arg_as_int (fun x y -> NBETerm.embed NBETerm.e_bool bogus_cbs (Z.lt_big_int x y)));
         (PC.op_LTE,
             2,
             0,
             binary_op arg_as_int (fun r x y -> embed_simple EMB.e_bool r (Z.le_big_int x y)),
             NBETerm.binary_op NBETerm.arg_as_int (fun  x y -> NBETerm.embed NBETerm.e_bool bogus_cbs (Z.le_big_int x y)));
         (PC.op_GT,
             2,
             0,
             binary_op arg_as_int (fun r x y -> embed_simple EMB.e_bool r (Z.gt_big_int x y)),
             NBETerm.binary_op NBETerm.arg_as_int (fun x y -> NBETerm.embed NBETerm.e_bool bogus_cbs (Z.gt_big_int x y)));
         (PC.op_GTE,
             2,
             0,
             binary_op arg_as_int (fun r x y -> embed_simple EMB.e_bool r (Z.ge_big_int x y)),
             NBETerm.binary_op NBETerm.arg_as_int (fun x y -> NBETerm.embed NBETerm.e_bool bogus_cbs (Z.ge_big_int x y)));
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
             and_op,
             NBETerm.and_op);
         (PC.op_Or,
             2,
             0,
             or_op,
             NBETerm.or_op);
         (let u32_int_to_t =
            ["FStar"; "UInt32"; "uint_to_t"]
            |> PC.p2l
            |> (fun l -> S.lid_as_fv l (S.Delta_constant_at_level 0) None) in
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
(* Operations from FStar.String *)
         (PC.string_list_of_string_lid,
             1,
             0,
             unary_op arg_as_string list_of_string',
             NBETerm.unary_op NBETerm.arg_as_string NBETerm.list_of_string');
         (PC.string_string_of_list_lid,
             1,
             0,
             unary_op (arg_as_list EMB.e_char) string_of_list',
             NBETerm.unary_op (NBETerm.arg_as_list NBETerm.e_char) NBETerm.string_of_list');
         (PC.string_make_lid,
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
                   (NBETerm.embed NBETerm.e_string bogus_cbs)
                   (fun (x:BigInt.t) (y:char) -> FStar.String.make (BigInt.to_int_fs x) y));
         (PC.string_split_lid,
             2,
             0,
             string_split',
             NBETerm.string_split');
         (PC.prims_strcat_lid,
             2,
             0,
             binary_string_op (fun x y -> x ^ y),
             NBETerm.binary_string_op (fun x y -> x ^ y));
         (PC.string_concat_lid,
             2,
             0,
             string_concat',
             NBETerm.string_concat');
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
             NBETerm.string_index);
         (PC.string_index_of_lid,
             2,
             0,
             string_index_of,
             NBETerm.string_index_of);
         (PC.string_sub_lid,
             3,
             0,
             string_substring',
             NBETerm.string_substring');
(* END FStar.String functions *)
         (PC.op_Eq,
             3,
             0,
             decidable_eq false,
             NBETerm.decidable_eq false);
         (PC.op_notEq,
             3,
             0,
             decidable_eq true,
             NBETerm.decidable_eq true);
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
        let add_sub_mul_v =
          (bounded_signed_int_types @ bounded_unsigned_int_types)
          |> List.collect (fun m ->
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
                      with_meta_ds r (embed_simple EMB.e_int r x) m),
                  NBETerm.unary_op
                    NBETerm.arg_as_bounded_int
                    (fun (int_to_t, x, m) ->
                     NBETerm.with_meta_ds
                       (NBETerm.embed NBETerm.e_int bogus_cbs x) m))])
        in
        let div_mod_unsigned =
          bounded_unsigned_int_types
          |> List.collect (fun m ->
            [(PC.p2l ["FStar"; m; "div"],
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
          |> List.collect (fun m ->
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
       add_sub_mul_v
       @ div_mod_unsigned
       @ bitwise
    in
    let strong_steps = List.map (as_primitive_step true)  (basic_ops@bounded_arith_ops) in
    let weak_steps   = List.map (as_primitive_step false) weak_ops in
    prim_from_list <| (strong_steps @ weak_steps)

let equality_ops : prim_step_set =
    let interp_prop_eq2 (psc:psc) _norm_cb (args:args) : option<term> =
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
    let interp_prop_eq3 (psc:psc) _norm_cb (args:args) : option<term> =
        let r = psc.psc_range in
        match args with
        | [(t1, _); (t2, _); (a1, _); (a2, _)] ->    //eq3
            (match U.eq_inj (U.eq_tm t1 t2) (U.eq_tm a1 a2) with
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
         interpretation = interp_prop_eq2;
         interpretation_nbe = fun _cb -> NBETerm.interp_prop_eq2}
    in
    let hetero_propositional_equality =
        {name = PC.eq3_lid;
         arity = 4;
         univ_arity = 2;
         auto_reflect=None;
         strong_reduction_ok=true;
         requires_binder_substitution=false;
         interpretation = interp_prop_eq3;
         interpretation_nbe = fun _cb -> NBETerm.interp_prop_eq3}
    in

    prim_from_list [propositional_equality; hetero_propositional_equality]

(* Profiling the time each different primitive step consumes *)
let primop_time_map : BU.smap<int> = BU.smap_create 50

let primop_time_reset () =
    BU.smap_clear primop_time_map

let primop_time_count (nm : string) (ms : int) : unit =
    match BU.smap_try_find primop_time_map nm with
    | None     -> BU.smap_add primop_time_map nm ms
    | Some ms0 -> BU.smap_add primop_time_map nm (ms0 + ms)

let fixto n s =
    if String.length s < n
    then (make (n - String.length s) ' ') ^ s
    else s

let primop_time_report () : string =
    let pairs = BU.smap_fold primop_time_map (fun nm ms rest -> (nm, ms)::rest) [] in
    let pairs = BU.sort_with (fun (_, t1) (_, t2) -> t1 - t2) pairs in
    List.fold_right (fun (nm, ms) rest -> (BU.format2 "%sms --- %s\n" (fixto 10 (BU.string_of_int ms)) nm) ^ rest) pairs ""

let extendable_primops_dirty : ref<bool> = BU.mk_ref true

type register_prim_step_t = primitive_step -> unit
type retrieve_prim_step_t = unit -> prim_step_set
let mk_extendable_primop_set ()
  : register_prim_step_t
  * retrieve_prim_step_t =
  let steps = BU.mk_ref (empty_prim_steps ()) in
  let register (p:primitive_step) =
      extendable_primops_dirty := true;
      steps := add_step p !steps
  in
  let retrieve () = !steps
  in
  register, retrieve

let plugins = mk_extendable_primop_set ()
let extra_steps = mk_extendable_primop_set ()

let register_plugin (p:primitive_step) = fst plugins p
let retrieve_plugins () =
    if Options.no_plugins ()
    then empty_prim_steps ()
    else snd plugins ()

let register_extra_step  p  = fst extra_steps p
let retrieve_extra_steps () = snd extra_steps ()

let cached_steps : unit -> prim_step_set =
    let memo : ref<prim_step_set> = BU.mk_ref (empty_prim_steps ()) in
    fun () ->
      if !extendable_primops_dirty
      then
        let steps =
          merge_steps built_in_primitive_steps
            (merge_steps (retrieve_plugins ())
                (retrieve_extra_steps ()))
        in
        memo := steps;
        extendable_primops_dirty := false;
        steps
      else
      !memo

let add_nbe s = // ZP : Turns nbe flag on, to be used as the default norm strategy
    if Options.use_nbe ()
    then { s with nbe_step = true }
    else s


let config' psteps s e =
    let d = s |> List.collect (function
        | UnfoldUntil k -> [Env.Unfold k]
        | Eager_unfolding -> [Env.Eager_unfolding_only]
        | UnfoldQual l when List.contains "unfold" l ->
          [Env.Eager_unfolding_only]
        | Inlining -> [Env.InliningDelta]
        | UnfoldQual l when List.contains "inline_for_extraction" l ->
          [Env.InliningDelta]
        | _ -> []) |> List.unique in
    let d = match d with
        | [] -> [Env.NoDelta]
        | _ -> d in
    let steps = to_fsteps s |> add_nbe in
    let psteps = add_steps (cached_steps ()) psteps in
    {tcenv = e;
     debug = if Options.debug_any () then
            { gen = Env.debug e (Options.Other "Norm")
             ; top = Env.debug e (Options.Other "NormTop")
             ; cfg = Env.debug e (Options.Other "NormCfg")
             ; primop = Env.debug e (Options.Other "Primops")
             ; unfolding = Env.debug e (Options.Other "Unfolding")
             ; b380 = Env.debug e (Options.Other "380")
             ; wpe = Env.debug e (Options.Other "WPE")
             ; norm_delayed = Env.debug e (Options.Other "NormDelayed")
             ; print_normalized = Env.debug e (Options.Other "print_normalized_terms")
             ; debug_nbe = Env.debug e (Options.Other "NBE")}
            else no_debug_switches
      ;
     steps = steps;
     delta_level = d;
     primitive_steps = psteps;
     strong = false;
     memoize_lazy = true;
     normalize_pure_lets = (not steps.pure_subterms_within_computations) || Options.normalize_pure_terms_for_extraction();
     reifying = false}

let config s e = config' [] s e

let should_reduce_local_let cfg lb =
  if cfg.steps.do_not_unfold_pure_lets
  then false //we're not allowed to do any local delta steps
  else if cfg.steps.pure_subterms_within_computations &&
          U.has_attribute lb.lbattrs PC.inline_let_attr
  then true //1. we're extracting, and it's marked @inline_let
  else
    let n = Env.norm_eff_name cfg.tcenv lb.lbeff in
    if U.is_pure_effect n &&
       (cfg.normalize_pure_lets
        || U.has_attribute lb.lbattrs PC.inline_let_attr)
    then true //Or, 2. it's pure and we either not extracting, or it's marked @inline_let
    else U.is_ghost_effect n && //Or, 3. it's ghost and we're not extracting
         not (cfg.steps.pure_subterms_within_computations)
