.. _algebra_tactics:

Algebraic computations in Lean
==============================

This is a tutorial on doing proofs with a computational flavour using the
`mathlib4 <https://github.com/leanprover-community/mathlib4>`_ library for the
`Lean 4 <https://leanprover.github.io/>`_ proof assistant. It is a port to Lean 4 of the tutorial
written by Heather Macbeth, `Algebraic Computations in Lean <https://hrmacbeth.github.io/computations_in_lean/>`_

The phrase "computational flavour" might need some explanation. These are not heavy computations
that require two hours running SageMath, but simply the kind of mildly-painful calculation that
might take a couple of paragraphs on paper.

Currently the tutorial focuses on the tactic ``polyrith`` and on ``field_simp``.  There
are several other powerful tactics which are commonly needed for "computational" proofs, notably
``norm_num``, ``norm_cast`` (and variants), and ``(n)linarith``. These other tactics are discussed
in context as the need arises.

This is an intermediate-level tutorial, but the focus of the exercises and
presentation is on the computations, so don't worry about understanding every detail of the syntax
if you can pick up the general idea.

Feedback is very welcome. If you try this tutorial, come to
the Lean chat room on `Zulip <https://leanprover.zulipchat.com/>`_ and say hello!

**Acknowledgements:** As explained above, this tutorial was authored by Heather Macbeth,
and the port to Lean 4 was made in collaboration
with Marc Masdeu. The examples in
this tutorial are taken from some mathlib contributions by several people.
Thank you to Johan Commelin, Julian Külshammer and François
Sunatori! And particular thanks to Jeremy Avigad, for sharing the Sphinx template for the tutorial,
and Rob Lewis, for many conversations about automation in Lean.
