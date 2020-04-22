#!/bin/bash

set -eu

max=$1

function make_tactic_interp_def () {
    local n=$1

    echo "let mk_tactic_interpretation_$n"
    echo -n "    (t : 't1"
    for i in $(seq 2 $n); do echo -n " -> 't$i"; done
    echo " -> tac<'r>)"
    for i in $(seq 1 $n); do
    echo "    (e$i:embedding<'t$i>)"
    done
    echo "    (er:embedding<'r>)"
    echo "    (psc:Cfg.psc)"
    echo "    (ncb:norm_cb)"
    echo "    (args:args)"
    echo "  : option<term>"
    echo "  ="
    echo "  match args with"
    echo -n "  | [(a1, _)"
    for i in $(seq 2 $((n+1))); do echo -n "; (a$i, _)"; done
    echo "] ->"
    for i in $(seq 1 $n); do
    echo "    BU.bind_opt (unembed e$i a$i ncb) (fun a$i ->"
    done
    echo "    BU.bind_opt (unembed E.e_proofstate a$((n+1)) ncb) (fun ps ->"
    echo "    let ps = set_ps_psc psc ps in"
    echo -n "    let r = run_safe (t"
    for i in $(seq 1 $n); do echo -n " a$i"; done; echo ") ps in"
    echo -n "    Some (embed (E.e_result er) (Cfg.psc_range psc) r ncb)"
    for i in $(seq 1 $((n+1))); do echo -n ")"; done
    echo
    echo "  | _ ->"
    echo "    None"
    echo
}

function make_tactic_nbe_interp_def () {
    local n=$1

    echo "let mk_tactic_nbe_interpretation_$n"
    echo "    cb"
    echo -n "    (t : 't1"
    for i in $(seq 2 $n); do echo -n " -> 't$i"; done
    echo " -> tac<'r>)"
    for i in $(seq 1 $n); do
    echo "    (e$i:NBET.embedding<'t$i>)"
    done
    echo "    (er:NBET.embedding<'r>)"
    echo "    (args:NBET.args)"
    echo "  : option<NBET.t>"
    echo "  ="
    echo "  match args with"
    echo -n "  | [(a1, _)"
    for i in $(seq 2 $((n+1))); do echo -n "; (a$i, _)"; done
    echo "] ->"
    for i in $(seq 1 $n); do
    echo "    BU.bind_opt (NBET.unembed e$i cb a$i) (fun a$i ->"
    done
    echo "    BU.bind_opt (NBET.unembed E.e_proofstate_nbe cb a$((n+1))) (fun ps ->"
    echo -n "    let r = run_safe (t"
    for i in $(seq 1 $n); do echo -n " a$i"; done; echo ") ps in"
    echo -n "    Some (NBET.embed (E.e_result_nbe er) cb r)"
    for i in $(seq 1 $((n+1))); do echo -n ")"; done
    echo
    echo "  | _ ->"
    echo "    None"
    echo
}

function make_total_interp_def () {
    local n=$1

    echo "let mk_total_interpretation_$n"
    echo -n "    (f : 't1"
    for i in $(seq 2 $n); do echo -n " -> 't$i"; done
    echo " -> 'r)"
    for i in $(seq 1 $n); do
    echo "    (e$i:embedding<'t$i>)"
    done
    echo "    (er:embedding<'r>)"
    echo "    (psc:Cfg.psc)"
    echo "    (ncb:norm_cb)"
    echo "    (args:args)"
    echo "  : option<term>"
    echo "  ="
    echo "  match args with"
    echo -n "  | [(a1, _)"
    for i in $(seq 2 $n); do echo -n "; (a$i, _)"; done
    echo "] ->"
    for i in $(seq 1 $n); do
    echo "    BU.bind_opt (unembed e$i a$i ncb) (fun a$i ->"
    done
    echo -n "    let r = f"
    for i in $(seq 1 $n); do echo -n " a$i"; done; echo " in"
    echo -n "    Some (embed er (Cfg.psc_range psc) r ncb)"
    for i in $(seq 1 $n); do echo -n ")"; done
    echo
    echo "  | _ ->"
    echo "    None"
    echo
}

function make_total_nbe_interp_def () {
    local n=$1

    echo "let mk_total_nbe_interpretation_$n"
    echo "    cb"
    echo -n "    (f : 't1"
    for i in $(seq 2 $n); do echo -n " -> 't$i"; done
    echo " -> 'r)"
    for i in $(seq 1 $n); do
    echo "    (e$i:NBET.embedding<'t$i>)"
    done
    echo "    (er:NBET.embedding<'r>)"
    echo "    (args:NBET.args)"
    echo "  : option<NBET.t>"
    echo "  ="
    echo "  match args with"
    echo -n "  | [(a1, _)"
    for i in $(seq 2 $n); do echo -n "; (a$i, _)"; done
    echo "] ->"
    for i in $(seq 1 $n); do
    echo "    BU.bind_opt (NBET.unembed e$i cb a$i) (fun a$i ->"
    done
    echo -n "    let r = f"
    for i in $(seq 1 $n); do echo -n " a$i"; done; echo " in"
    echo -n "    Some (NBET.embed er cb r)"
    for i in $(seq 1 $n); do echo -n ")"; done
    echo
    echo "  | _ ->"
    echo "    None"
    echo
}

function make_tac_step_def () {
    local n=$1

    echo "let mk_tac_step_$n"
    echo "  (nunivs:int)"
    echo "  (name:string)"
    echo -n "  (t : 't1"
    for i in $(seq 2 $n); do echo -n " -> 't$i"; done
    echo " -> tac<'r>)"
    for i in $(seq 1 $n); do
    echo "  (e$i:embedding<'t$i>)"
    done
    echo "  (er:embedding<'r>)"
    echo -n "  (nt : 'nt1"
    for i in $(seq 2 $n); do echo -n " -> 'nt$i"; done
    echo " -> tac<'nr>)"
    for i in $(seq 1 $n); do
    echo "  (ne$i:NBET.embedding<'nt$i>)"
    done
    echo "  (ner:NBET.embedding<'nr>)"
    echo "  : Cfg.primitive_step"
    echo "  ="
    echo "    mk name $((n+1)) nunivs"
    echo -n "      (mk_tactic_interpretation_$n t"
      for i in $(seq 1 $n); do echo -n " e$i"; done; echo " er)"
    echo -n "      (fun cb args -> mk_tactic_nbe_interpretation_$n cb nt"
    for i in $(seq 1 $n); do echo -n " ne$i"; done; echo " ner (drop nunivs args))"
    echo
}

function make_total_step_def () {
    local n=$1

    echo "let mk_total_step_$n"
    echo "  (nunivs:int)"
    echo "  (name:string)"
    echo -n "  (f : 't1"
    for i in $(seq 2 $n); do echo -n " -> 't$i"; done
    echo " -> 'r)"
    for i in $(seq 1 $n); do
    echo "  (e$i:embedding<'t$i>)"
    done
    echo "  (er:embedding<'r>)"
    echo -n "  (nf : 'nt1"
    for i in $(seq 2 $n); do echo -n " -> 'nt$i"; done
    echo " -> 'nr)"
    for i in $(seq 1 $n); do
    echo "  (ne$i:NBET.embedding<'nt$i>)"
    done
    echo "  (ner:NBET.embedding<'nr>)"
    echo "  : Cfg.primitive_step"
    echo "  ="
    echo "    mk name $n nunivs"
    echo -n "      (mk_total_interpretation_$n f"
      for i in $(seq 1 $n); do echo -n " e$i"; done; echo " er)"
    echo -n "      (fun cb args -> mk_total_nbe_interpretation_$n cb nf"
    for i in $(seq 1 $n); do echo -n " ne$i"; done; echo " ner (drop nunivs args))"
    echo
}

function make_tac_step_decl () {
    local n=$1

    echo "val mk_tac_step_$n :"
    echo "  int ->"
    echo "  string ->"
    echo -n "  ('t1"
    for i in $(seq 2 $n); do echo -n " -> 't$i"; done
    echo " -> tac<'r>) ->"
    for i in $(seq 1 $n); do
    echo "  embedding<'t$i> ->"
    done
    echo "  er:embedding<'r> ->"
    echo -n "  ('nt1"
    for i in $(seq 2 $n); do echo -n " -> 'nt$i"; done
    echo " -> tac<'nr>) ->"
    for i in $(seq 1 $n); do
    echo "  NBET.embedding<'nt$i> ->"
    done
    echo "  NBET.embedding<'nr> ->"
    echo "  Cfg.primitive_step"
    echo
}

function make_total_step_decl () {
    local n=$1

    echo "val mk_total_step_$n :"
    echo "  int ->"
    echo "  string ->"
    echo -n "  ('t1"
    for i in $(seq 2 $n); do echo -n " -> 't$i"; done
    echo " -> 'r) ->"
    for i in $(seq 1 $n); do
    echo "  embedding<'t$i> ->"
    done
    echo "  embedding<'r> ->"
    echo -n "  ('nt1"
    for i in $(seq 2 $n); do echo -n " -> 'nt$i"; done
    echo " -> 'nr) ->"
    for i in $(seq 1 $n); do
    echo "  NBET.embedding<'nt$i> ->"
    done
    echo "  NBET.embedding<'nr> ->"
    echo "  Cfg.primitive_step"
    echo
}

function mk_defs () {
    local max=$1
    for i in $(seq 1 $max); do
        make_tactic_interp_def $i
    done

    for i in $(seq 1 $max); do
        make_tactic_nbe_interp_def $i
    done

    for i in $(seq 1 $max); do
        make_total_interp_def $i
    done

    for i in $(seq 1 $max); do
        make_total_nbe_interp_def $i
    done

    for i in $(seq 1 $max); do
        make_tac_step_def $i
    done

    for i in $(seq 1 $max); do
        make_total_step_def $i
    done
}

function mk_decls () {
    local max=$1

    for i in $(seq 1 $max); do
        make_tac_step_decl $i
    done

    for i in $(seq 1 $max); do
        make_total_step_decl $i
    done
}

case "$1" in
    defs)
        mk_defs "$2"
        ;;
    decls)
        mk_decls "$2"
        ;;
    *)
        echo "wrong usage" >&2
        exit 1
esac
