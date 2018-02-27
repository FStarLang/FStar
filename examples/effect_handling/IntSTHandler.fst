module IntSTHandler

open IntST

open FStar.Heap
open FStar.ST

open FStar.List
open FStar.Printf

assume type a
assume val test_return_value : a

let prog_type = unit

let prog : st prog_type = 
  //IntST.return test_return_value
  //IntST.get ()
  //s <-- IntST.get ();
  IntST.put 42

(* *********************************************** *)

let handle_return (r:ref int) (#a:Type) (v:a) : ST a (requires (fun _ -> True)) 
                                                     (ensures  (fun h0 x h1 -> (x,sel h1 r) == IntST.return v (sel h0 r))) = 
  v

let handle_get (r:ref int) : ST int (requires (fun _ -> True)) 
                                       (ensures  (fun h0 x h1 -> (x,sel h1 r) == IntST.get () (sel h0 r))) = 
  read r

let handle_put (r:ref int) (i:int) : ST unit (requires (fun _ -> True))
                                             (ensures  (fun h0 x h1 -> (x,sel h1 r) == IntST.put i (sel h0 r))) =
  write r i

(* *********************************************** *)

open FStar.Tactics

let rec collect_app_ref' (ref:term) (args:list (a:argv{a << ref})) (t:term{t == ref \/ t << ref}) 
  : Tot (t:term{t == ref \/ t << ref} * list (a:argv{a << ref})) (decreases t) =
  match inspect t with
  | Tv_App l r ->
      collect_app_ref' ref (r::args) l
  | _ -> (t, args)

val collect_app_ref : ref:term -> t:term{t == ref \/ t << ref} -> (t:term{t == ref \/ t << ref}) * list (a:argv{a << ref})
let collect_app_ref ref = collect_app_ref' ref []

val args_wo_ref : #ref:term -> list (a:argv{a << ref}) -> list argv
let rec args_wo_ref #ref args =
  match args with 
  | [] -> []
  | a::args -> a :: args_wo_ref args

let rec handle_st_typed (a:Type) (f:st a) (r:ref int) : tactic (unit -> ST a (requires (fun _ -> True)) 
                                                                             (ensures  (fun h0 x h1 -> (x,sel h1 r) == f (sel h0 r)))) =
  t <-- quote f;

  t_return  <-- quote IntST.return;
  t_bind    <-- quote IntST.bind;
  t_get     <-- quote IntST.get;
  t_put     <-- quote IntST.put;

  match inspect t with
  | Tv_App _ _ ->
      let (t_fun,args) = collect_app_ref t t in

      if (term_eq t_fun t_return && length args = 2) 
        then (t_fun <-- quote handle_return;
              t_ref <-- quote r;
              let args = [t_ref,Q_Explicit;
                          FStar.List.Tot.Base.index args 0;
                          FStar.List.Tot.Base.index args 1] in              
              ty <-- quote Prims.unit;
              let t_out = pack (Tv_Abs (fresh_binder ty) (mk_app t_fun args)) in
              unquote t_out)

      else if (term_eq t_fun t_bind && length args = 4) 
        then (//a1 <-- unquote #Type (fst (FStar.List.Tot.Base.index args 0));
              //f1 <-- unquote #a1 (fst (FStar.List.Tot.Base.index args 2));
              //t1 <-- handle_st_typed a1 f1 r;
              fail "bind case not yet implemented")

      else if (term_eq t_fun t_get && length args = 1) 
        then (t_fun <-- quote handle_get;
              t_ref <-- quote r;
              let args = [t_ref,Q_Explicit] in              
              ty <-- quote Prims.unit;
              let t_out = pack (Tv_Abs (fresh_binder ty) (mk_app t_fun args)) in
              unquote t_out)

      else if (term_eq t_fun t_put && length args = 1) 
        then (t_fun <-- quote handle_put;
              t_ref <-- quote r;
              let args = [t_ref,Q_Explicit;
                          FStar.List.Tot.Base.index args 0] in              
              ty <-- quote Prims.unit;
              let t_out = pack (Tv_Abs (fresh_binder ty) (mk_app t_fun args)) in
              unquote t_out)

      else fail "application case not implemented"

  | _ -> fail "case not implemented"

let synth_prog_typed (r:ref int) : unit -> ST prog_type (requires (fun _ -> True)) 
                                                        (ensures  (fun h0 x h1 -> (x,sel h1 r) == prog (sel h0 r))) 
  = synth_by_tactic
    (
      t <-- quote prog;      
      t <-- norm_term [delta_only ["IntSTHandler.prog"]] t;
      t <-- unquote #(st prog_type) t;
      t <-- handle_st_typed prog_type t r;
      t <-- quote t;
      print (term_to_string t);;
      exact (return t)
    )



(* ********************************************************** *)


(* untyped handling experiment *)

(*let rec handle_st (t:term) (r:term) : tactic term = 
  t_return  <-- quote IntST.return;
  t_bind    <-- quote IntST.bind;
  t_get     <-- quote IntST.get;
  t_put     <-- quote IntST.put;

  match inspect t with
  | Tv_App _ _ ->
      let (t_fun,args) = collect_app_ref t t in

      // Handle IntST.return with handle_return (i.e., with ST's return)
      if (term_eq t_fun t_return && length args = 2) 
        then (t_fun <-- quote handle_return;
              let args = [r,Q_Explicit;
                          FStar.List.Tot.Base.index args 0;
                          FStar.List.Tot.Base.index args 1] in
              return (mk_app t_fun args))

      // Handle IntST.bind
      else if (term_eq t_fun t_bind && length args = 4) 
        then (let t0 = fst (FStar.List.Tot.Base.index args 2) in
              t0 <-- handle_st t0 r;
              let t1 = fst (FStar.List.Tot.Base.index args 3) in
              match inspect t1 with 
              | Tv_Abs b t1 -> t1 <-- handle_st t1 r;
                               return (pack (Tv_Let b t0 t1))
              | _ -> fail "body of bind is not a lambda")

      // Handle IntST.get_st with handle_get (i.e., with ST's read)
      else if (term_eq t_fun t_get && length args = 1) 
        then (t_fun <-- quote handle_get; 
              let args = [r,Q_Explicit] in
              return (mk_app t_fun args))

      // Handle IntST.put_st with handle_put (i.e., with ST's write)
      else if (term_eq t_fun t_put && length args = 1) 
        then (t_fun <-- quote handle_put; 
              let args = [r,Q_Explicit;
                          FStar.List.Tot.Base.index args 0] in
              return (mk_app t_fun args))

      else fail "not implemented application case"
  | _ -> fail "not implemented case"

let synth_prog (r:ref int) : unit -> ST prog_type (requires (fun _ -> True)) 
                                                  (ensures  (fun h0 x h1 -> (x,sel h1 r) == prog (sel h0 r))) 
  = synth_by_tactic
    (
      t <-- quote prog;      
      r <-- quote r;

      t <-- norm_term [delta_only ["IntSTHandler.prog"]] t;

      t  <-- handle_st t r;
      ty <-- quote Prims.unit;
      let f = pack (Tv_Abs (fresh_binder ty) t) in

      exact (return f)
    )
*)



