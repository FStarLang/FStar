---
name: fstarverifier
description: Use fstar.exe to verify F* code and interpret the errors reported
---

## Invocation
This skill is used when:
- Verifying F* (.fst) or interface (.fsti) files
- Debugging verification failures
- Checking proof completeness

## Core Operations

### Basic Verification
```bash
# Verify a single file
fstar.exe Module.fst

# With Pulse extension
fstar.exe --include <PULSE_HOME>/out/lib/pulse Module.fst

# With include paths
fstar.exe --include <PULSE_HOME>/out/lib/pulse --include path/to/lib Module.fst
```

### Diagnostic Options
```bash
# Show query statistics (find slow/cancelled proofs)
fstar.exe --query_stats Module.fst

# Split queries for isolation
fstar.exe --split_queries always Module.fst

# Log SMT queries for analysis
fstar.exe --log_queries Module.fst

# Refresh Z3 between queries
fstar.exe --z3refresh Module.fst

# Combined debugging
fstar.exe --include <PULSE_HOME>/out/lib/pulse --query_stats --split_queries always --z3refresh Module.fst
```

### Resource Limits
```bash
# Set rlimit (default varies, target ≤10 for robustness)
# In file: #push-options "--z3rlimit 10"

# Set fuel for recursive functions
# In file: #push-options "--fuel 1 --ifuel 1"
```

## Error Interpretation

### "Could not prove post-condition"
**Cause:** SMT cannot establish the postcondition from available facts
**Solutions:**
1. Add intermediate `assert` statements
2. Call relevant lemmas explicitly
3. Use `Seq.equal`/`Set.equal` for collection equality
4. Call `FS.all_finite_set_facts_lemma()` for FiniteSet reasoning

### "Identifier not found"
**Cause:** Symbol not in scope
**Solutions:**
1. Check module imports (`open`, `module X = ...`)
2. Verify definition order (F* is order-sensitive)
3. Check for typos in names

### "rlimit exhausted" / Query cancelled
**Cause:** Proof too complex for SMT within time limit
**Solutions:**
1. Factor proof into smaller lemmas
2. Reduce fuel: `#push-options "--fuel 0 --ifuel 0"`
3. Add explicit type annotations
4. Use patterns on quantifiers
5. Make definitions `opaque_to_smt` and instantiate manually

### "Expected type X, got type Y" (Unification failure)
**Cause:** Type mismatch, often with refinements
**Solutions:**
1. Add explicit type annotations
2. Cast values to base types
3. Check refinement predicates

### "Application of stateful computation cannot have ghost effect"
**Cause:** Calling stateful function in ghost context (Pulse-specific)
**Solutions:**
1. Ensure condition variables are concrete, not from `with` bindings
2. Read from actual data structures, not ghost sequences
3. Restructure to avoid ghost conditionals

## Verification Strategy

### For New Code
1. Start with admitted proofs to check structure
2. Remove admits one at a time
3. Add helper lemmas as needed
4. Verify interface (.fsti) before implementation (.fst)

### For Failing Proofs
1. Use `--query_stats` to identify slow queries
2. Add `assert` statements to locate failure point
3. Factor out failing assertion into separate lemma
4. Reduce proof to minimal failing case
5. Add explicit lemma calls or type annotations

### For Robustness
1. Keep rlimits low (≤10)
2. Split large proofs into lemmas
3. Use explicit types over inference
4. Prefer `Seq.equal` over `==` for sequences

## Additional resources

Find the directory PoP-in-FStar on the local machine, or locate it
here: https://github.com/FStarLang/PoP-in-FStar

This contains the sources to the Proof-oriented Programming in F* 
book. You can search through the book for various explanations, 
tips and common patterns.

Also look at FStar/ulib, FStar/doc, FStar/examples for sample code.
