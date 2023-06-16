open Prims
type 'uuuuu t = Obj.t
let (as_subst : Pulse_Typing_Env.env -> Obj.t -> Pulse_Syntax_Naming.subst) =
  fun g -> fun uu___ -> Prims.magic ()
let (as_map :
  Pulse_Typing_Env.env ->
    Obj.t -> (Pulse_Syntax_Base.var, Pulse_Syntax_Base.term) FStar_Map.t)
  = fun g -> fun uu___ -> Prims.magic ()
type ('g, 's, 'm) relates_to = unit
let (dom :
  Pulse_Typing_Env.env -> Obj.t -> Pulse_Syntax_Base.var FStar_Set.set) =
  fun g -> fun s -> FStar_Map.domain (as_map g s)
let (lookup :
  Pulse_Typing_Env.env ->
    Obj.t -> Pulse_Syntax_Base.var -> Pulse_Syntax_Base.term)
  = fun g -> fun s -> fun x -> FStar_Map.sel (as_map g s) x
type ('g, 's1, 's2) equal = unit
let (empty : Pulse_Typing_Env.env -> Obj.t) = fun uu___ -> Prims.magic ()
let (singleton :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.var -> Pulse_Syntax_Base.term -> Obj.t)
  = fun uu___ -> Prims.magic ()
let (push : Pulse_Typing_Env.env -> Obj.t -> Obj.t -> Obj.t) =
  fun g -> fun uu___ -> fun uu___1 -> Prims.magic ()
type ('g, 's1, 's2) subst_extends = unit
let (subst_term :
  Pulse_Typing_Env.env ->
    Obj.t -> Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun g ->
    fun s -> fun t1 -> Pulse_Syntax_Naming.subst_term t1 (as_subst g s)
let (subst_st_term :
  Pulse_Typing_Env.env ->
    Obj.t -> Pulse_Syntax_Base.st_term -> Pulse_Syntax_Base.st_term)
  =
  fun g ->
    fun s -> fun t1 -> Pulse_Syntax_Naming.subst_st_term t1 (as_subst g s)
let (subst_comp :
  Pulse_Typing_Env.env ->
    Obj.t -> Pulse_Syntax_Base.comp -> Pulse_Syntax_Base.comp)
  =
  fun g -> fun s -> fun c -> Pulse_Syntax_Naming.subst_comp c (as_subst g s)
let (diff : Pulse_Typing_Env.env -> Obj.t -> Obj.t -> Obj.t) =
  fun g -> fun uu___ -> fun uu___1 -> Prims.magic ()