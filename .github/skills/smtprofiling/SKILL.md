---
name: smtprofiling
description: Debug F* queries sent to Z3, diagnosing proof instability and performance issues
---

## Invocation
This skill is used when:
- Verifying F* (.fst) or interface (.fsti) files
- Debugging verification failures and proof performance
- Especially when proofs require high rlimits or fail unpredictably

## Core Operations

### Collect an .smt2 file for problematic proof

Wrap the part of the program to diagnose proof failures with

```fstar
#push-options "--log_queries --z3refresh --query_stats --split_queries always"
let definition_to_be_debugged ...
#pop-options
```

Run F* on the file (with appropriate include paths)

```bash
fstar.exe Module.fst
```

The log messages will show the name of the .smt2 file logged for each proof obligation

### Verify .smt2 file independently of F*

Find `z3` in the path. It might be named `z3-4.13.3`, `z3-4.15.1` etc., with a version number suffix

```bash
z3 queries-myquery.smt2
```

You can add z3 options like `smt.qi.profile=true` to see which quantifiers were firing 
too much and what to do about it

### Interpreting a quantifier profile

Some quantifiers in F*'s SMT encoding always fire a lot---this is
by design. Typically, quantifiers with unqualified names 
(Box_bool_proj_0) or those with names in Prims, or FStar.
Pervasives will fire a lot.

Look for quantifiers in modules that are in files that you 
authored that are firing a lot---these might signify that you 
should write a pattern for those quantifiers, or control their 
instantiation explicitly.

### More information on SMT profiling

Find the directory PoP-in-FStar on the local machine, or locate it here:
https://github.com/FStarLang/PoP-in-FStar

The section under_the_hood/uth_smt.rst contains information about F*'s SMT
encoding and how to profile.
