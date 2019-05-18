How to run
==========

With our extended F\* installed, calling the `fstar.exe` binary on each
file should simply work, such as:

    $ ~/FStar/bin/fstar.exe NDDemonic.fst
    Verified module: NDDemonic (944 milliseconds)
    All verification conditions discharged successfully

To check all of them one can just call `make`, as such:

    $ make
    /home/edsger/FStar/bin/fstar.exe  --use_hints --use_hint_hashes IOFr2.fst
    Unable to open hints file: FStarExamples/IOFr2.fst.hints; ran without hints
    Verified module: IOFr2 (1171 milliseconds)
    All verification conditions discharged successfully
    /home/edsger/FStar/bin/fstar.exe  --use_hints --use_hint_hashes NDAngelic.fst
    Unable to open hints file: FStarExamples/NDAngelic.fst.hints; ran without hints
    Verified module: NDAngelic (15568 milliseconds)
    All verification conditions discharged successfully
    [...]

The warnings are not important. "Hints" are a way for F\* to cache SMT
proofs. The F\* Makefiles enable hint usage by default, but we have
deliberately not included any hints here.

(If you compiled F\* yourself and you get an error about `FSTAR_HOME`
not being set, set it to the directory where the F\* source tree is.)

Effect declaration basics
=========================

The usual effect declaration looks like:

   total
   reifiable
   reflectable
   new_effect {
     EFF : a:Type -> Effect
     with
          repr      = repr
        ; return    = return
        ; bind      = bind

        ; wp_type   = wp
        ; return_wp = return_wp
        ; bind_wp   = bind_wp

        ; interp    = interp
   }

The `total`, `reifiable` and `reflectable` specify, respectively, that
the termination check is enabled for recursive definitions in `EFF`,
computations in `EFF` can be reified as their underlying `repr`, and
values in `repr` can be reflected to computations in `EFF`. These have
existed in F\* since DM4Free, and are all optional.

The first three fields define the computational monad, and the following
three define the specification monad. The `interp` field is the effect
observation from the computational monad into the specificational one.

One can provide a monadic relation (`mrelation`) instead. In that case,
one needs to provide explicit WPs when using `reflect` since there is no
way to compute a WP from an underlying computation.

Monadic actions are reflected in a posteriori from the effect
definition. For example, here's one from `NDDemonic`:

    val choose : #a:Type0 -> x:a -> y:a -> ND a (fun p -> p x /\ p y)
    let choose #a x y = ND?.reflect [x;y]

F\* checks that the annotated specification (`fun p -> p x /\ p y`) is
at least as strong as the interpretation of `[x;y]`. In this case,
they are equivalent.

Interactive mode
================

F\* has an emacs-based interactive mode. You can install it by
installing the `fstar-mode` package in MELPA (it is already
installed in the Docker image). There are instructions in
https://github.com/FStarLang/fstar-mode.el/blob/master/README.md, but
the most common commands are:

C-c C-n (next)          -- Send the next paragraph to F\*
C-c C-p (previous)      -- Retract the last paragraph
C-c RET or C-c C-RET    -- Send everything up to the current point to F\*
C-c C-r (reload)        -- Reload dependencies of the current buffer and reprocess its contents
C-c C-x (exit)  ￼       -- Kill the F\* subprocess
C-c C-c                 -- Interrupt the currently-running verification task.

Index of Examples
=================

- §3.3:
-- W^Exc: ExnHandle.fst
-- Non-determinism: NDAngelic.fst and NDDemonic.fst
-- IO: In order, IORWSt.fst, IORWLocal.fst and IORWFree.fst

- §3.4:
-- ST: St.fst
-- Non-determinism: NDDemonic.fst
-- IOFr: IORWFree.fst
-- IOHist: IORWLocal.fst

Others:

- PartialityTotal: partial programs, total correctness interpretation

- PartialityPartial: partial programs, partial correctness interpretation

- ExnTotal: Exceptions with Cont_P specs, total correctness interpretation

- ExnPartial: Exceptions with Cont_P specs, partial correctness interpretation

- ExnHandle.fst, ExnHandleTwoPostCond.fst: exceptions with canonical
  interpretation, and examples of handling exceptions

- IOForget.fst: IO with Cont_P specs, ignoring events

- IOWSt.fst: Reasoning about the writes on IO using ghost state

- IOWLocal.fst: Reasoning about the writes on IO in update monad style

- IOWFree.fst: Reasoning about the writes on IO without considering history

- IORWFree.fst, IORWLocal.fst, IORWSt.fst: Similar to above, but
  considering reads too

- StExnPartial.fst, StExnTotal.fst: State+Exceptions, but specs only
  over state, with partial and total correctness interpretations respectively.

Negative tests
==============

Please note that definitions prefixed with

  [@expect_failure]

are checked to *fail* by F\*. This is analogous to the `Fail` keyword of
Coq.

Well-foundedness axiom
======================

You will find calls to `FStar.WellFounded.axiom1` in some files. This
is an axiom stating that, for a function `f : A -> B` and `x : A`,
then `f x` is "smaller" than `f`, for the built-in "smaller" notion
F\* uses to check termination recursive functions. The termination
checkers of other proof assistants, e.g. of Coq, make a very similar
assumption, albeit without requiring explicit calls to an axiom.
