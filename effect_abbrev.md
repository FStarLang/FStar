1. Restrict the syntax of new effect and effect abbreviations to what is actually supported:

assumed effects, e.g, 

* assume effect Tot a

* defined new effects, e.g., 
    effect { TAC with { repr = tac_repr; return = tac_return; bind = tac_bind } }

And this is the main part of this work, effect abbreviations:

* effect abbreviations are unary, with a computation type on the RHS

    effect Pure a = Tot a

I would not even allow extra pre/postconditions on the RHS of an effect
abbreviation, otherwise one would need to handle things like this, by conjoining
postconditions etc.

    effect A a = Tot a (ensures p1)
    effect B a = A a (ensures p2)

We should check that the abbreviations are a pure renaming only, i.e., 
    effect A a = Tot (list a)
should be detected and disallowed in the ToSyntax phase itself.

2. Effect abbreviations are just for syntactic sugar and should be desugared
   away in ToSyntax. The core syntax should not even need to contain a
   Sig_effect_abbrev node.

When desugaring an computation type, we should desugar it all the way to its
root effect. This should be easy since effect abbreviations as described above
are also very simple.

Say we have

    effect Pure a = Tot a
    effect Pure2 a = Pure a

When desugaring 

a -> Pure2 b (requires pre) (ensures post)

We should first desugar it to 

a -> Tot b (requires pre) (ensures post)

And then to 

a -> #_:squash pre -> Tot (x:b{post x})

In the representation of computation types, we should record, in an additional
field (e.g., source_effect_name) the effect name as written in the source
program (e.g,. Pure2, Lemma etc.) so that we can resugar it correctly to what
the programmer wrote.

Finally, I want to remove the TOTAL flag and LEMMA flag. 

- Whether or not an effect is TOTAL should be determined by its effect name,
  which after desugaring is always a root effect name, e.g., Tot, GTot, etc.

- Whether or not an effect is a Lemma should be detected by the
  source_effect_name, no need for an additional flag.

This would be a significant simplification and rule out the mess noted above
with the various sources of confusion around effect abbreviations.