.. _Agentic_search_trees:

====================
Rubrics as Templates
====================

In the previous chapter, we used our proof-engineering experience to define a
fairly sophisticated parameteric typeclass as a rubric for complexity-aware
sorting algorithms. But, now that we've defined one of these rubrics, we can use
it as a template to have agents define other rubrics of a similar flavor.

CLRS contains various implementations of search trees, including binary search
trees, red-black trees, B-trees, etc. Each of these data structures has a
different set of invariants, and offers different tradeoffs in terms of
performance and complexity. An initial version of AutoCLRS included several
separate search tree implementations, each with its own specification. 

In this chapter, we look at how to develop a rubric for search trees to
abstractly capture the specifications of these various search tree
implementations under a single abstraction.

----------------------------------------------------------------
Background: Verifying Data Structures with Functional Refinement
----------------------------------------------------------------

``