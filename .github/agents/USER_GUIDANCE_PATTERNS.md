---
name: UserGuidancePatterns
description: Patterns for guiding AI agents through F*/Pulse verification tasks
---

# User Guidance Patterns

This document captures effective patterns for guiding an AI agent through complex F*/Pulse verification tasks, based on a 67-hour session.

## Effective Guidance Strategies

### 1. Clear Constraints
State non-negotiable requirements upfront and repeat them:
- "No admits!"
- "No assumes!"
- "No memory leaks - don't drop any resource unless it is ghost state!"
- "Work hard!"

### 2. Iterative Refinement
Start broad, then focus:
1. "Implement X with admitted proofs to check structure"
2. "Now remove the admits one at a time"
3. "Focus on proving Y - that's the key invariant"
4. "Finish Z and let's complete this"

### 3. Technical Hints When Stuck
Provide specific technical direction:
- "Use Seq.equal for sequence equality proofs"
- "Call all_finite_set_facts_lemma to expose FiniteSet axioms"
- "Variables from 'with' bindings are ghost - use actual data structure access"
- "Keep rlimits ≤10 for robustness"

### 4. Design Guidance
Point to relevant existing code:
- "Take a look at Pulse.Lib.ConditionVar, which uses a similar pattern"
- "Look at FStar.FiniteMap.Base - it packages a map with a finite set"
- "Use GhostFractionalTable for permission accounting"

### 5. Debugging Direction
Guide systematic debugging:
- "Use --query_stats to find cancelled queries"
- "Drill down into the proof, add intermediate assertions"
- "Factor out the failing assertion into a separate lemma"
- "Don't increase rlimit - find the root cause instead"

### 6. Course Correction
Redirect when implementation diverges:
- "The invariant looks wrong - it requires X but should allow Y"
- "You're CAS'ing from 0 to 1, but should allow multiple readers"
- "Split reader_token to expose the predicate to callers"

### 7. Encouragement
Keep momentum going:
- "Great work, good progress. Keep going!"
- "Almost there! Let's finish this."
- "Push on! Finish X first, then keep working on the rest."
- "You can do it!"

### 8. Clarification Requests
Ask the agent to stop when uncertain:
- "If you think you need to change the invariant, stop and ask"
- "Ask clarifying questions, make a plan, then implement"

## Anti-Patterns to Avoid

### Too Vague
❌ "Make it work"
❌ "Fix the proof"
✅ "The issue is in release_reader - you're not decrementing the counter"

### Too Prescriptive (Initially)
❌ "Use exactly this code: ..."
✅ "Here's the invariant I have in mind - implement the rest"

### Accepting Shortcuts
❌ "That's fine for now" (when there are admits)
✅ "No admits! Work on those lemmas and prove them fully"

### Ignoring Flakiness
❌ "It passes sometimes, so it's fine"
✅ "The proof is still flaky. Reduce rlimit to 10 and make it robust"

## Session Structure

### Phase 1: Exploration & Planning
- Agent analyzes existing codebase
- Identifies what exists and what's missing
- Creates implementation plan

### Phase 2: Initial Implementation
- Rough implementation with admits
- Establish core structure and types
- Validate approach compiles

### Phase 3: Proof Engineering
- Remove admits systematically
- Add helper lemmas
- Debug failing proofs

### Phase 4: Hardening
- Reduce rlimits
- Make proofs robust
- Clean up code

### Phase 5: Integration
- Copy to target location
- Verify build succeeds
- Commit with detailed message
