---
name: pulseverifier
description: Use fstar.exe to verify Pulse code and interpret the errors reported
---

## Invocation
This skill is used when:
- Verifying Pulse (.fst) files with `#lang-pulse` directive
- Debugging separation logic proof failures
- Checking resource management correctness

## Core Operations

PULSE_HOME is usually located adjacent to the FStar directory.

### Basic Verification
```bash
# Verify Pulse file (--include <PULSE_HOME>/out/lib/pulse is required)
fstar.exe --include <PULSE_HOME>/out/lib/pulse Module.fst

# With include paths for Pulse library
fstar.exe --include <PULSE_HOME>/out/lib/pulse --include out/lib/pulse --include lib/pulse/lib Module.fst

# Verify interface first, then implementation
fstar.exe --include <PULSE_HOME>/out/lib/pulse --include paths... Module.fsti
fstar.exe --include <PULSE_HOME>/out/lib/pulse --include paths... Module.fst
```

### Building with Pulse Repository
```bash
# In pulse repository root
make -j4

# Or verify specific file
cd /path/to/pulse
fstar.exe --include out/lib/pulse --include lib/pulse/lib lib/pulse/lib/Module.fst
```

## Pulse-Specific Errors

### "Application of stateful computation cannot have ghost effect"
**Cause:** Trying to call a stateful `stt` function inside a ghost context
**Diagnosis:** 
- Variables bound with `with x y z. _` are ghost
- If an `if` condition uses ghost values, both branches become ghost

**Solutions:**
1. Read from actual data structures instead of ghost sequences:
```pulse
// WRONG: bucket_ptrs is ghost from 'with'
let ptr = Seq.index bucket_ptrs idx;

// RIGHT: Read from actual vector
let ptr = V.op_Array_Access vec idx;
```

2. Restructure to perform stateful ops before ghost conditionals:
```pulse
// Do stateful work first
let result = stateful_operation();
// Then do ghost reasoning
if ghost_condition then ... else ...
```

### "Expected a term with non-informative (erased) type"
**Cause:** Binding a concrete type from a ghost expression
**Solutions:**
1. Use assertion instead of let binding:
```pulse
// WRONG
let x : list entry = Seq.index ghost_seq idx;

// RIGHT
assert (pure (Cons? (Seq.index ghost_seq idx)));
```

2. Keep ghost values as ghost:
```pulse
let x : erased (list entry) = Seq.index ghost_seq idx;
```

### "Could not prove post-condition" (separation logic)
**Cause:** Resources don't match expected slprop

**Diagnosis Steps:**
1. Check fold/unfold balance
2. Verify rewrite statements are correct
3. Ensure all resources are accounted for

**Solutions:**
1. Add explicit fold/unfold:
```pulse
unfold (my_predicate args);
// ... work with internal structure ...
fold (my_predicate args);
```

2. Use rewrite for type equality:
```pulse
rewrite (pred x) as (pred y);  // when x == y is known
```

3. For OnRange predicates:
```pulse
get_bucket_at ptrs contents lo hi idx;  // Extract element
// ... use element ...
put_bucket_at ptrs contents lo hi idx;  // Put back
```

### "Ill-typed application" in fold/unfold
**Cause:** Predicate arguments don't match definition
**Solutions:**
1. Check all arguments are provided
2. Verify implicit arguments are inferable
3. Add explicit type annotations

## Proof Patterns

### FiniteSet Reasoning
```pulse
// ALWAYS call this before FiniteSet assertions
FS.all_finite_set_facts_lemma();

// Now SMT can prove these
assert (pure (FS.mem x (FS.insert x s)));
assert (pure (FS.cardinality (FS.remove x s) == FS.cardinality s - 1));
```

### Sequence Equality
```pulse
// Use extensional equality
assert (pure (Seq.equal s1 s2));

// NOT propositional equality
// assert (pure (s1 == s2));  // Often fails
```

### Ghost Lemma Calls
```pulse
// Call F* lemmas in ghost context
my_lemma arg1 arg2;
assert (pure (lemma_conclusion));
```

## Resource Management Verification

### Checking for Memory Leaks
Look for:
1. `drop_` calls - should only be on empty/null resources
2. All allocated resources must be freed or returned
3. Box.box allocations must have corresponding B.free

### Acceptable Drops
```pulse
// OK: Empty linked list (null pointer)
drop_ (LL.is_list null_ptr []);

// NOT OK: Non-empty resources
// drop_ (LL.is_list ptr (hd::tl));  // Memory leak!
```

## Verification Checklist

Before considering code complete:
- [ ] No `admit()` calls
- [ ] No `assume_` calls  
- [ ] No `drop_` of non-empty resources
- [ ] Interface (.fsti) verified separately
- [ ] Implementation (.fst) verified
- [ ] rlimits ≤10 throughout
- [ ] All queries pass (no cancelled in --query_stats)
