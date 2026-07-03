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

A typical way to verify a data structure in separation logic is to prove that
the in-memory representation of the data strcture is a refinement of some purely
functional model.

We saw this in a previous :ref:`chapter on linked lists <Pulse_linked_list>`
where an in-memory linked data structure is related to a purely functional list.
Let's recall that here briefly.

Here is an in-memory, pointer-based representation of a linked list in Pulse.

.. code-block:: pulse

    type node (t:Type0) = {
        head : t;
        tail : llist t;
    }

    and node_ptr (t:Type0) = ref (node t)

    and llist (t:Type0) = option (node_ptr t)

And here is a separation logic predicate relating an ``x:llist t`` to a purely
functional list ``l:list t``:

.. code-block:: pulse

    let rec is_list #t (x:llist t) (l:list t)
    : Tot slprop (decreases l)
    = match l with
      | [] -> pure (x == None)
      | head::tl -> 
        exists* (p:node_ptr t) (tail:llist t).
        pure (x == Some p) **
        pts_to p { head; tail } **
        is_list tail tl

Sometimes we call the in-memory data structure the "representation" (or
``repr``) and its purely functional counterpart the "model". Imperative
operations on the representation are specified by their action on the model.

With this style in mind, let's see how we can use our previous rubric for
sorting algorithms to define a complexity aware rubric for search data
structures.

Complexity Aware Search Structures
----------------------------------

Providing with our sorting rubric, and existing verified implementations of
binary trees and red-black trees as templates, we asked an agent to develop a
typeclass as a rubric for search data structures. Here's what it produced; we'll
present it piece by piece.

* First, we have a typeclass ``search_structure`` indexed by representation type
  ``repr`` and ``model`` (both parameterized by the element type ``a``).

* We have a predicate ``owns`` a separation logic predicate relating the
  representation and model
  
* And a predicate ``valid`` that defines some structural validity property of
  the model, e.g., some ordering property on the tree.

* Then we have model functions for the ``empty_model``, ``find_model``,
  ``insert_model``, and ``delete_model``, all ghost functions used to specify
  the behavior of the imperative operations on the representation.

* Two metrics on the model, the ``height`` and the ``size`` of the model, which
  are used to define complexity bounds on the imperative operations.

* And, finally, functions to characterize the complexity of the three main operations.

.. code-block:: fstar

    class search_structure
        (repr: Type0 -> Type0)
        (model: Type0 -> Type0)
        (owns: (a:Type0) -> repr a -> model a -> slprop)
        (valid: (a:Type0) -> erased (TO.total_order a) -> model a -> GTot prop)
        (empty_model: (a:Type0) -> GTot (model a))
        (find_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (option a))
        (insert_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
        (delete_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
        (height: (a:Type0) -> model a -> nat)
        (size: (a:Type0) -> model a -> nat)
        (search_bound insert_bound delete_bound: nat -> nat -> nat)

The class contains several fields, starting with a function to create an empty
representation, with a postcondition stating that the representation refines the
empty model.

.. code-block:: pulse

    create:
        (fn (a:Type0)
            (#ord:erased (TO.total_order a))
        requires emp
        returns tree:repr a
        ensures owns a tree (empty_model a) ** pure (valid a ord (empty_model a)));

Then, function to dispose the tree, reclaiming the memory associated with it.

.. code-block:: pulse

    dispose:
        (fn (a:Type0)
            (tree:repr a)
            (#m:erased (model a))
        requires owns a tree m
        ensures emp);


Now to the interesting functions. 

We have ``search``, which follows the pattern from our sorting rubric as a
template. It is parametric in the type of elements and uses an instrumented
total order ``iord``, and proves that the result is consistent with the model,
and that the number of ticks is bounded by the search bound.

.. code-block:: pulse

    search:
        (fn (a:Type0)
            (tree:repr a)
            (key:a)
            (ctr:ticks_t)
            (#ord:erased (TO.total_order a))
            (iord:instrumented_total_order a ord ctr)
            (#m:erased (model a))
            (#i:erased nat)
        preserves owns a tree m
        requires MR.pts_to ctr #1.0R i ** pure (valid a ord m)
        returns result:option a
        ensures exists* ticks.
            MR.pts_to ctr #1.0R ticks **
            pure (
            result == find_model a ord m key /\
            ticks <= i + search_bound (height a m) (size a m)));

Insert and delete follow the same pattern, showing that modified tree
is consistent with the model, and that the number of ticks is bounded by the
insert and delete bounds, respectively.

.. code-block:: pulse

    insert:
        (fn (a:Type0)
            (tree:repr a)
            (key:a)
            (ctr:ticks_t)
            (#ord:erased (TO.total_order a))
            (iord:instrumented_total_order a ord ctr)
            (#m:erased (model a))
            (#i:erased nat)
        requires owns a tree m ** MR.pts_to ctr #1.0R i ** pure (valid a ord m)
        returns tree':repr a
        ensures exists* ticks.
            owns a tree' (insert_model a ord m key) **
            MR.pts_to ctr #1.0R ticks **
            pure (
            valid a ord (insert_model a ord m key) /\
            ticks <= i + insert_bound (height a m) (size a m)));

    delete:
        (fn (a:Type0)
            (tree:repr a)
            (key:a)
            (ctr:ticks_t)
            (#ord:erased (TO.total_order a))
            (iord:instrumented_total_order a ord ctr)
            (#m:erased (model a))
            (#i:erased nat)
        requires owns a tree m ** MR.pts_to ctr #1.0R i ** pure (valid a ord m)
        returns tree':repr a
        ensures exists* ticks.
            owns a tree' (delete_model a ord m key) **
            MR.pts_to ctr #1.0R ticks **
            pure (
            valid a ord (delete_model a ord m key) /\
            ticks <= i + delete_bound (height a m) (size a m)));


Of course, this rubric only counts the comparison operations for complexity, not
every read, write, or allocation. For that we'll need a more powerful form of
abstraction, that we'll leave for later. But, using rubrics as templates
demonstrates how agents can generalize from patterns in existing code to produce
new specifications for other settings.

Constraining the Model
----------------------

We have a class for a search structure showing that it refines a model type, but
we haven't yet constrained the model type, e.g., nothing would prevent an
instance of ``search_structure`` above with a trivial model (e.g., ``unit``).

To constrain the model, we also asked the agent to write a class to prove that
the model satsifies a few expected laws, e.g., that find after insert succeeds
on the inserted key etc.

.. code-block:: fstar

    class search_model_laws
        (model: Type0 -> Type0)
        (valid: (a:Type0) -> erased (TO.total_order a) -> model a -> prop)
        (empty_model: (a:Type0) -> GTot (model a))
        (find_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (option a))
        (insert_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
        (delete_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    = {
        find_empty:
            ((a:Type0) ->
            (ord:erased (TO.total_order a)) ->
            (key:a) ->
            Lemma
                (ensures find_model a ord (empty_model a) key == None));

        find_insert_hit:
            ((a:Type0) ->
            (ord:erased (TO.total_order a)) ->
            (m:model a) ->
            (key:a) ->
            Lemma
                (requires valid a ord m)
                (ensures find_model a ord (insert_model a ord m key) key == Some key));

        find_insert_other:
            ((a:Type0) ->
            (ord:erased (TO.total_order a)) ->
            (m:model a) ->
            (inserted:a) ->
            (key:a) ->
            Lemma
                (requires valid a ord m /\ same_key a ord key inserted = false)
                (ensures find_model a ord (insert_model a ord m inserted) key ==
                        find_model a ord m key));

        find_delete_hit:
            ((a:Type0) ->
            (ord:erased (TO.total_order a)) ->
            (m:model a) ->
            (key:a) ->
            Lemma
                (requires valid a ord m)
                (ensures find_model a ord (delete_model a ord m key) key == None));

        find_delete_other:
            ((a:Type0) ->
            (ord:erased (TO.total_order a)) ->
            (m:model a) ->
            (deleted:a) ->
            (key:a) ->
            Lemma
                (requires valid a ord m /\ same_key a ord key deleted = false)
                (ensures find_model a ord (delete_model a ord m deleted) key ==
                        find_model a ord m key));
        }

Auditing the Rubric with Small Proof-Oriented Tests
----------------------------------------------------

Whereas in the previous chapter, we wrote a rubric for sorting ourselves, here
we had agents author a rubric for search structures. It would be prudent to
check that the agent-authored specification is reasonable.

In this `blog post <https://risemsr.github.io/blog/2026-04-16-spotting-specs/>`_
we wrote about the idea of "Small Proof-Oriented Tests" (SPOTs) to audit
agent-generated specifications, a technique where one writes a few small tests
against a specification to check that the specification is usable and precise.
For example, could one prove that creating a search structure and inserting and
deleting a few keys, and then searching for a key returns the expected result?
Such tests shake out bugs in specifications by checking that they are precise
enough to prove expected properties on small inputs.

A Rubric-compliant Binary Search Tree
-------------------------------------

Now, with our audited rubric in place, reviewing a 1000 line implementation of a
binary search tree for rubric compliance amounts to checking these lines only:

.. code-block:: fstar

    instance bst_search_structure_instance : SC.search_structure
        bst_ptr bst owns valid empty_model find_model insert_model delete_model
        height size bst_search_bound bst_insert_bound bst_delete_bound
    
    instance bst_search_model_laws_instance :
        SC.search_model_laws bst valid empty_model find_model insert_model  delete_model
    
where the complexity bounds are linear in the height of the tree. 

.. code-block:: fstar

    let bst_search_bound (h:nat) (_n:nat) : nat = h
    let bst_insert_bound (h:nat) (_n:nat) : nat = h
    let bst_delete_bound (h:nat) (_n:nat) : nat = 4 * h + 1

One should also review the definition of ``height`` to check that it is indeed
the height of the tree, and not some other measure.

A Rubric-compliant Red-Black Tree
---------------------------------

The solution for a red-black tree is about 2000 lines of Pulse code, but its
typeclass instantiation is also just a few lines of F*. The only thing to audit
for rubric compliance is the complexity bound.

For red-black trees, these are as follows. Since a red-black tree is balanced,
the complexity bounds are logarithmic in the size of the tree.

.. code-block:: fstar

    let rb_search_bound (_h:nat) (n:nat) : nat =
        if n = 0 then 1 else 2 * log2_floor (n + 1) + 1

    let rb_insert_bound (_h:nat) (n:nat) : nat =
        if n = 0 then 2 else 2 * log2_floor (n + 1) + 2

    let rb_delete_bound (_h:nat) (n:nat) : nat =
        if n = 0 then 2 else 4 * log2_floor (n + 1) + 2

One should also review the definition of ``size`` to check that it is indeed the
size of the tree, and not some other measure.

Auditing Red-Black Trees
------------------------

As before, rubric compliance is a big step towards checking a result, but it is
not the full story. For instance, on closer inspection, we found that the
agent's first solution to this rubric implemented a version of red-black trees
based on Chris Okasaki's purely functional red-black trees. One can see this by
inspecting the type of the model and the representation:

.. code-block:: fstar
    
    noeq
    type rb_node (a:Type0) = {
        key: a;
        color: color;
        left: rb_ptr a;
        right: rb_ptr a;
    }
    and rb_node_ptr (a:Type) = box (rb_node a)
    and rb_ptr (a:Type) = option (rb_node_ptr a)

In contrast, the CLRS red-black tree uses a tree with parent pointers at each
node, to enable efficient insertion and deletion. As mentioned before, for 
algorithmic fidelity, audits via code inspection seem unavoidable. 

Noting this discrepancy, we asked the agent to rewrite the red-black tree
implementation to use the CLRS representation with parent pointers, and it did
so successfully, using this representation below and a rubric instance similar
to the one shown above.

.. code-block:: fstar

    type rb_node (a:Type0) = {
        key: a;
        color: color;
        left: rb_ptr a;
        right: rb_ptr a;
        p: rb_ptr a;
    }
    and rb_node_ptr (a:Type) = box (rb_node a)
    and rb_ptr (a:Type) = option (rb_node_ptr a)

