.. _Part2_merkle:

Merkle Trees
============

A `Merkle tree <https://en.wikipedia.org/wiki/Merkle_tree>`_ is a
cryptographic data structure designed by `Ralph Merkle
<https://en.wikipedia.org/wiki/Ralph_Merkle>`_ in the late 1970s and
has grown dramatically in prominence in the last few years, inasmuch
as variants of Merkle trees are at the core of most `blockchain
systems <https://en.wikipedia.org/wiki/Blockchain>`_.

A Merkle tree makes use of cryptographic hashes to enable efficient
cryptographic proofs of the authenticity of data stored in the
tree. In particular, for a Merkle tree containing :math:`2^n` data
items, it only takes :math:`n` hash computations to prove that a
particular item is in the tree.

In this section, we build a very simple, but canonical, Merkle tree
and prove it correct and cryptographically secure. And we'll use
several indexed inductive types to do it. Thanks to Aseem Rastogi for
this example!

Setting
.......

Merkle trees have many applications. To motivate our presentation
here, consider the following simple scenario.

A content provider (someone like, say, the New York Times) has a large
archive of digital artifacts---documents, multimedia files, etc. These
artifacts are circulated among users, but when receiving an artifact
one may question its authenticity. One way to ensure the authenticity
of received artifacts is for the content provider to use a digital
signature based on a public-key cryptosystem and for users to verify
these signatures upon receiving an artifact. However, signatures can
be quite heavyweight for certain applications.

Instead, the content provider can organize their archive into a Merkle
tree, a tree of hashes with the artifacts themselves stored at the
leaves, such that a single hash associated with the root node of the
tree authenticates *all* the artifacts in the tree. By publishing just
this root hash, and associating with each artifact a path in the tree
from the root to it, a skeptical client can quickly check using a
small number of hash computations (logarithmic in the size of the
entire archive) whether or not a given artifact is authentic (by
recomputing the root hash and checking if it matches the known
published root hash).


Intuitions
..........

Our Merkle tree will be a full binary tree of height :math:`n` storing
:math:`2^n` data items and their corresponding hashes at the
nodes. The main idea of a Merkle tree is for each internal node to
also maintain a *hash of the hashes* stored at each of its
children. If the hash algorithm being used is cryptographically
secure, in the sense that it is collision resistant (i.e., it is
computationally hard to find two strings that hash to the same value),
then the hash associated with the root node authenticates the content
of the entire tree.

Informally, a Merkle tree is an authenticated data structure in that
it is computationally hard to tamper with any of the data items in the
tree while still producing the same root hash. Further, to prove that
a particular data item ``d`` is in the tree, it suffices to provide
the hashes associated with the nodes in the path from the root to that
the leaf containing that item ``d``, and one can easily check by
comparing hashes that the claimed path is accurate. In fact, we can
prove that if a claimed path through the tree attests to the presence
of some other item ``d' <> d``, then we can construct a collision on
the underlying hash algorithm---this property wil be our main proof of
security.


Preliminaries
.............

We'll model the resources and the hashes we store in our tree as
strings of characters. F* standard library ``FStar.String`` provides
some utilities to work with strings.

In the code listing below, we define the following

  * ``lstring n``, the type of strings of length ``n``. Like the
    ``vec`` type, ``lstring`` is a length-indexed type; unlike
    ``vector`` it is defined using a refinement type rather than an
    indexed inductive type. Defining indexed types using refinements
    is quite common in F*.

  * ``concat``, a utility to concatenate strings, with its type
    proving that the resulting string's length is the sum of the lengths
    of the input strings.

  * ``hash_size`` and ``hash``, a parameter of our development
    describing the length in characters of a ``hash`` function. The F*
    keyword ``assume`` allows you to assume the existence of a symbol
    at a given type. Use it with care, since you can trivially prove
    anything by including an ``assume nonsense : False``.

  * The type of resources we store in the tree will just be
    ``resource``, an alias for ``string``.

.. literalinclude:: ../code/MerkleTree.fst
   :language: fstar
   :start-after: //SNIPPET_START: preliminaries
   :end-before: //SNIPPET_END: preliminaries


Defining the Merkle tree
........................

The inductive type ``mtree`` below defines our Merkle tree. The type
has *two* indices, such that ``mtree n h`` is the type of a Merkle
tree of height ``n`` whose root node is associated with the hash
``h``.

Leaves are trees of height ``0`` and are constructed using ``L res``,
where the hash associated with this node is just ``hash res``, the
hash of the resource stored at the leaf.

Internal nodes of the tree are constructed using ``N left right``,
where both the ``left`` and ``right`` trees have the same height
``n``, producing a tree of height ``n + 1``. More interestingly, the
hash associated with ``N left right`` is ``hash (concat hl hr)``, the
hash of the concatenation of hashes of the left and right subtrees.


.. literalinclude:: ../code/MerkleTree.fst
   :language: fstar
   :start-after: //SNIPPET_START: mtree
   :end-before: //SNIPPET_END: mtree

In our previous examples like vectors, the index of the type
abstracts, or summarizes, some property of the type, e.g., the
length. This is also the case with ``mtree``, where the first index is
an abstraction summarizing only the height of the tree; the second
index, being a cryptographic hash, summarizes the entire contents of
the tree.


Accessing an element in the tree
................................

A resource identifier ``resource_id`` is a path in the tree from the
root to the leaf storing that resource. A path is just a list of
booleans describing whether to descend left or right from a node.

Just like a regular binary tree, it's easy to access an element in the
tree by specifying its ``resource_id``.


Exercise
^^^^^^^^

Implement a function to access an element in a ``mtree`` in given a
``rid : list bool``. Figuring out its type, including its decreases
clause, is the most interesting part. The function itself is
straightforward.

`Exercise file <../code/exercises/Part2.MerkleTreeGet.fst>`__

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/MerkleTree.fst
       :language: fstar
       :start-after: //SNIPPET_START: get
       :end-before: //SNIPPET_END: get

--------------------------------------------------------------------------------

The Prover
..........

Unlike the ordinary ``get`` function, we can define a function
``get_with_evidence`` that retrieves a resource from the tree together
with some evidence that that resource really is present in the tree.
The evidence contains the resource identifier and the hashes of
sibling nodes along the path from root to that item.

First, we define ``resource_with_evidence n``, an indexed type that
packages a ``res:resource`` with its ``rid:resource_id`` and
``hashes:list hash_t``---both ``rid`` and ``hashes`` have the same
length, which is the index of the constructed type.

The function ``get_with_evidence`` is similar to ``get``, except as it
returns from descending into a child node, it adds the hash of the
other child node to the list of hashes.

.. literalinclude:: ../code/MerkleTree.fst
   :language: fstar
   :start-after: //SNIPPET_START: prover
   :end-before: //SNIPPET_END: prover

In the cryptographic literature, this function is sometimes calles
*the prover*. A ``RES r ri hs`` is a claimed proof of the membership
of ``r`` in the tree at the location specified by ``ri``.

Going back to our motivating scenario, artifacts distributed by our
content provider would be elements of the type
``resource_with_evidence n``, enabling clients to verify that a given
artifact is authentic, as shown next.

The Verifier
............

Our next step is to build a checker of claimed proofs, sometimes
called *a verifier*. The function ``verify`` below takes a
``p:resource_with_evidence n``, re-computes the root hash from the
evidence presented, and checks that that hash matches the root hash of
a given Merkle tree. Note, the ``tree`` itself is irrelevant: all
that's needed to verify the evidence is *the root hash* of the Merkle
tree.

.. literalinclude:: ../code/MerkleTree.fst
   :language: fstar
   :start-after: //SNIPPET_START: verify
   :end-before: //SNIPPET_END: verify

The main work is done by ``compute_root_hash``, shown below.

   * In the first branch, we simply hash the resource itself.

   * In the second branch, we recompute the hash from the tail of the
     path, and then based on which direction was taken, we either
     concatenate sibling hash on the left or the right, and hash the
     result.

.. literalinclude:: ../code/MerkleTree.fst
   :language: fstar
   :start-after: //SNIPPET_START: compute_root_hash
   :end-before: //SNIPPET_END: compute_root_hash


Convince yourself of why this is type-correct---refer back to the
description of :ref:`vectors<Part2_vectors>`, if needed. For example,
why is it safe to call ``L.hd`` to access the first element of
``hashes``?


Correctness
...........

Now, we can prove our main correctness theorem, namely that
``get_with_evidence`` returns a resource with verifiable
evidence.

.. literalinclude:: ../code/MerkleTree.fst
   :language: fstar
   :start-after: //SNIPPET_START: correctness
   :end-before: //SNIPPET_END: correctness

The proof is a simple proof by induction on the height of the tree, or
equivalently, the length of the resource id.

In other words, evidence constructed by a honest prover is accepted by
our verifier.

Security
........

The main security theorem associated with this construction is the
following: if the verifier can be convinced to accept a resource with
evidence of the form ``RES r rid hs``, and if the resource in the
Merkle tree associated with ``rid`` is *not* ``r``, then we can easily
construct a collision on the underlying cryptographic hash. Since the
hash is meant to be collision resistant, one should conclude that it
is at least as hard to convince our verifier to accept incorrect
evidence as it is to find collisions on the underlying hash.

We start by defining the type of a ``hash_collision``, a pair of
distinct strings that hash to the same value.

.. literalinclude:: ../code/MerkleTree.fst
   :language: fstar
   :start-after: //SNIPPET_START: hash_collision
   :end-before: //SNIPPET_END: hash_collision

The ``security`` theorem shown below takes a ``tree`` and
``p:resource_with_evidence n``, where the refinement on ``p`` states
that the verifier accepts the evidence (``verify p tree``) although
the resource associated with ``p.ri`` is not ``p.res``: in this case,
we can build a function, by induction on the height of the tree, that
returns a hash collision.

.. literalinclude:: ../code/MerkleTree.fst
   :language: fstar
   :start-after: //SNIPPET_START: security
   :end-before: //SNIPPET_END: security

We look at its cases in detail:

   * In the base case, it's easy to construct a hash collision
     directly from the differing resources.

   * Otherwise, we recompute the hash associate with the current node
     from the tail of the evidence presented, and the two cases of the
     left and right subtrees are symmetric.

     - If the recomputed hash matches the hash of the node, then we
       can generate a collision just by the induction hypothesis on
       the left or right subtree.

     - Otherwise, we can build a hash collision, relying on
       ``String.concat_injective``, a lemma from the library stating
       that the concatenation of two pairs of equal length strings are
       equal only if their components are. Knowing that ``h' <> h1``
       (or, symmetically, ``h' <> h2``) this allows us to prove that
       the concatenations are unequal, although their hashes are, by
       assumption, equal.

.. _Part2_merkle_insert:

Exercise
........

Implement a function to update an ``mtree`` at a given
``rid:resource_id`` with a new resource ``res:resource``. The
resulting tree will have a new root hash, so you will have to return
the new hash along with the updated tree.

`Exercise file <../code/exercises/Part2.MerkleTreeUpdate_V0.fst>`__

.. container:: toggle

    .. container:: header

       **Hint**

    One type of the ``update`` function could be as follows:

    .. literalinclude:: ../code/MerkleTree.fst
       :language: fstar
       :start-after: //SNIPPET_START: update_hint
       :end-before: //SNIPPET_END: update_hint

--------------------------------------------------------------------------------

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/MerkleTree.fst
       :language: fstar
       :start-after: //SNIPPET_START: update_mtree'
       :end-before: //SNIPPET_END: update_mtree'

    One interesting part of our solution is that we never explicitly
    construct the hash of the nodes. Instead, we just use ``_`` and
    let F* infer the calls to the hash functions.

----------------------------------------------------------------------------------------------------------------------------------------------------------------


Summary and Further Reading
...........................

In summary, we've built a simple but powerful authenticated data
structure with a proof of its correctness and cryptographic security.

In practice, Merkle trees can be much more sophisticated than our the
most basic one shown here. For instance, they can support incremental
updates, contain optimizations for different kinds of workloads,
including sparse trees, and be implemented using high-performance,
mutable structures.

You can read more about various flavors of Merkle trees implemented in
F* in the following papers.

* `EverCrypt, Section VII (B)
  <https://project-everest.github.io/assets/evercrypt.pdf>`_,
  describes a high-performance Merkle tree with fast incremental
  updates.

* `FastVer <https://dl.acm.org/doi/10.1145/3448016.3457312>`_
  describes the design and use of hybrid authenticated data strutures,
  including sparse Merkle trees, for applications such as verificable
  key-value stores.
