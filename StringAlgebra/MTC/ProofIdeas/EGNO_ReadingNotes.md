# Reading Notes: EGNO "Tensor Categories" (2015)

## Sections 8.9-8.17 — Drinfeld morphism, Ribbon categories, S-matrix, Verlinde

These notes focus on what is relevant for formalizing the MTC module, especially
the proof that ribbon categories are spherical.

---

## Section 8.9: The Drinfeld morphism

### Definition (equation 8.30)
The Drinfeld morphism u_X : X -> X** is defined as the composition:
```
X --[id_X tensor coev_{X*}]--> X tensor X* tensor X**
  --[c_{X,X*} tensor id_{X**}]--> X* tensor X tensor X**
  --[ev_X tensor id_{X**}]--> X**
```

**EGNO convention**: Uses LEFT duals X* (not right duals X^vee). Their
coevaluation goes 1 -> X tensor X*, evaluation goes X* tensor X -> 1.
This is OPPOSITE to Mathlib's convention where `ExactPairing X Y` has
eta : 1 -> X tensor Y, eps : Y tensor X -> 1, and right duals satisfy
ExactPairing X X^vee.

**Key translation**: EGNO's u_X corresponds to our `drinfeldIsoIso X` but
built with right duals. The construction is formally the same: compose
coevaluation, braiding, and evaluation to get X -> (X^vee)^vee.

### Proposition 8.9.3 (equation 8.31)
```
u_X tensor u_Y = u_{X tensor Y} circ c_{Y,X} circ c_{X,Y}
```
This says u is NOT a monoidal natural transformation — it differs from
monoidal by the monodromy c^2.

**Critical for us**: This is exactly WHY we need the twist correction!
The pivotal iso j = u circ theta^{-1} IS monoidal because:
- u_{X tensor Y} = (u_X tensor u_Y) circ (c^2)^{-1}
- theta_{X tensor Y} = (theta_X tensor theta_Y) circ c^2  (twist_tensor axiom)
- So j_{X tensor Y} = u_{X tensor Y} circ theta^{-1}_{X tensor Y}
               = (u_X tensor u_Y) circ (c^2)^{-1} circ (theta_X tensor theta_Y)^{-1} circ (c^2)^{-1}
  Hmm, this needs more careful analysis...

### Proposition 8.9.5 (Properties of Drinfeld element for Hopf algebras)
- (iv) S^2(x) = u x u^{-1} — the squared antipode is conjugation by u
- (v) Delta(u) = (u tensor u)(R^{21} R)^{-1} — u is NOT grouplike (relates to monodromy)
- (vi) z := u S(u) is central, and g := u^{-1} S(u) is grouplike

**Important**: Property (v) confirms u is not a tensor morphism, matching Prop 8.9.3.

---

## Section 8.10: Ribbon monoidal categories

### Definition 8.10.1 (Twist / balancing transformation)
A twist on a braided rigid monoidal category is theta in Aut(id_C) such that:
```
theta_{X tensor Y} = (theta_X tensor theta_Y) circ c_{Y,X} circ c_{X,Y}   ... (8.32)
```
A twist is a RIBBON STRUCTURE if additionally:
```
(theta_X)* = theta_{X*}
```

**Note on conventions**: EGNO uses LEFT duals X*, we use RIGHT duals X^vee.
The axiom `twist_dual` in our formalization is:
```
rightAdjointMate (twist X).hom = (twist X^vee).hom
```
which is the right-dual version of (theta_X)* = theta_{X*}.

### Proposition 8.10.6 (u_X is an isomorphism)
The Drinfeld morphism u_X : X -> X** is an isomorphism when X is simple.
**Proof**: Shows v_X circ u_X = f' tensor id_X tensor f where f, f' are nonzero
scalars (from Lemma 8.10.5). Hence u_X is invertible.

**For us**: We get this for free from Mathlib's `rightDualIso` construction.

### Equation 8.35: Pivotal structure from twist
Any natural isomorphism psi_X : X -> X** in a braided category can be
written as:
```
psi_X = u_X theta_X,    theta in Aut(id_C)
```
and psi is a tensor isomorphism (i.e., pivotal structure) if and only if
theta is a twist.

**CRITICAL**: This is the key theorem linking twists and pivotal structures!

BUT NOTE: EGNO writes psi = u circ theta, while our formalization has
j = u circ theta^{-1}. This is because of the different convention:
- EGNO's twist_tensor: theta_{X tensor Y} = (theta_X tensor theta_Y) circ c^2
- To make u circ theta a tensor morphism: need theta to "cancel" the c^2 in u's non-monoidality
- Since u_{X tensor Y} = (u_X tensor u_Y) circ (c^2)^{-1}, we need theta to
  satisfy theta_{X tensor Y} = (theta_X tensor theta_Y) circ c^2
- Then (u circ theta)_{X tensor Y} = u_{X tensor Y} circ theta_{X tensor Y}
  = (u tensor u) circ (c^2)^{-1} circ (theta tensor theta) circ c^2
  This is NOT simply (u theta) tensor (u theta) unless c^2 commutes with theta tensor theta.

WAIT — I think the issue is that EGNO may use psi = u_X theta_X differently
from what I wrote. Let me re-read...

Actually, equation (8.35) says: "any natural isomorphism psi_X : X -> X**
can be written as psi_X = u_X theta_X" where theta_X is an automorphism of X.
And "psi is a tensor isomorphism iff theta is a twist."

So psi = u composed with theta (theta acts FIRST, then u).
In our Lean code: j_X = theta^{-1}_X then u_X, i.e., j = u circ theta^{-1}.
This means our theta^{-1} plays the role of EGNO's theta.

Since EGNO's twist axiom (8.32) for theta becomes, for theta^{-1}:
```
(theta^{-1})_{X tensor Y} = (c^2)^{-1} circ ((theta^{-1})_X tensor (theta^{-1})_Y)
```
which is the inverse of the twist_tensor axiom. So j = u circ theta^{-1}
is indeed the right construction.

### Proposition 8.10.12: Ribbon iff spherical
**THIS IS THE KEY RESULT FOR OUR PROOF.**

> Let C be a braided fusion category with a twist theta. The canonical
> pivotal structure psi = theta circ u is spherical if and only if
> theta is a ribbon structure.

**Proof sketch from EGNO**:
- The condition theta_X* = (theta_X)* translates to:
  psi_{X*} = (psi_X circ u_X^{-1})^* circ u_{X*}
- Using naturality of u and Theorem 8.10.7 (relating u to the tensor structure delta):
  psi_{X*} = psi_{X**}^* circ delta_{X*}^{-1}
- This is equivalent to the condition:
  Tr(psi_{X*}) = Tr(psi_{X**}^*) for every simple X  ... (8.39)
- By Corollary 7.21.8, the last expression equals Tr(psi_{X**}*)
- Thus (8.39) says Tr(psi_{X*}) = Tr(psi_{X**}), i.e., psi is spherical.

**IMPORTANT**: The proof in EGNO uses:
1. Fusion category structure (semisimplicity — suffices to check on simples)
2. Properties of the tensor structure delta from Section 7.19
3. Corollary 7.21.8 (trace property for pivotal functors)

This is a HIGH-LEVEL proof that works for FUSION categories. For general
ribbon categories (not necessarily semisimple), the proof needs to be
more direct — working at the morphism level rather than reducing to simples.

### Our situation
Our `RibbonCategory` class does NOT assume semisimplicity. So we need a
DIRECT proof that leftTrace f = rightTrace f for all f : X -> X.

The direct proof approach (from our ProofIdeas) works at the morphism level:

After expanding j = theta^{-1} composed with u and applying the Drinfeld iso
helper lemmas (drinfeldIsoIso_eval, drinfeldIsoIso_coeval), the goal reduces to:

```
eta >>>= beta^{-1} >>>= X^vee whisker theta >>>= X^vee whisker f >>>= eps
  = eta >>>= f whisker X^vee >>>= theta^{-1} whisker X^vee >>>= beta >>>= eps
```

The KEY IDENTITY needed is:
```
beta^{-1}_{X^vee, X} composed with (X^vee whisker theta_X)
  = (theta^{-1}_X whisker X^vee) composed with beta_{X, X^vee}
```
as morphisms X tensor X^vee -> X^vee tensor X.

This rearranges to:
```
theta_X whisker X^vee composed with beta_{X, X^vee}
  = beta^{-1}_{X^vee, X}^{-1} composed with (X^vee whisker theta_X)^{-1}
  wait, let me be more careful...
```

The identity `(beta_{X^vee,X})^{-1} circ (X^vee whisker theta) = (theta^{-1} whisker X^vee) circ beta_{X,X^vee}`

Rearranging: `beta_{X,X^vee} circ (theta^{-1} whisker X^vee)^{-1} = (X^vee whisker theta)^{-1} circ (beta_{X^vee,X})^{-1}^{-1}`

i.e., `beta circ theta whisker X^vee = X^vee whisker theta^{-1}^{-1} circ beta_{X^vee,X}`

i.e., `theta whisker X^vee circ beta = beta_{X^vee,X} circ X^vee whisker theta`

This is just BRAIDING NATURALITY! `theta whisker X^vee circ beta_{X,X^vee} = beta_{X,X^vee} circ X^vee whisker theta`???

No wait, braiding naturality says: `f whisker Y circ beta_{X',Y} = beta_{X,Y} circ Y whisker f` for f : X -> X'.
With f = theta_X : X -> X, Y = X^vee:
`theta whisker X^vee circ beta_{X,X^vee} = beta_{X,X^vee} circ X^vee whisker theta`

That's NOT what we need. We need:
`(beta_{X^vee,X})^{-1} circ X^vee whisker theta = theta^{-1} whisker X^vee circ beta_{X,X^vee}`

Let me try again from the equation. We need to show:
```
A := (beta_{X^vee,X}).inv composed_with (X^vee whisker theta)
B := (theta.inv whisker X^vee) composed_with (beta_{X,X^vee}).hom
```
are equal as morphisms X tensor X^vee -> X^vee tensor X.

Multiply both sides on the left by beta_{X^vee,X}.hom:
```
beta.hom circ A = X^vee whisker theta    (since beta.hom circ beta.inv = id)
beta.hom circ B = beta_{X^vee,X}.hom circ theta^{-1} whisker X^vee circ beta_{X,X^vee}.hom
```

For these to be equal:
```
X^vee whisker theta = beta_{X^vee,X}.hom circ theta^{-1} whisker X^vee circ beta_{X,X^vee}.hom
```

This says: `X^vee whisker theta = beta circ (theta^{-1} whisker X^vee) circ beta`

i.e., conjugation by the double braiding (monodromy) sends theta^{-1} whisker X^vee
to X^vee whisker theta.

Actually, by braiding naturality:
```
beta_{X^vee,X}.hom circ theta^{-1} whisker X^vee = X whisker theta^{-1} circ beta_{X^vee,X}.hom
```
Wait no. braiding_naturality_left says:
`f whisker Y circ beta_{X',Y}.hom = beta_{X,Y}.hom circ Y whisker f`

So with f = theta^{-1} : X -> X, Y = X^vee:
`theta^{-1} whisker X^vee circ beta_{X,X^vee}.hom = beta_{X,X^vee}.hom circ X^vee whisker theta^{-1}`

And with beta_{X^vee,X}:
`(f whisker X) circ beta_{X^vee,X}.hom = beta_{X^vee,X}.hom circ X whisker f`

Taking f = theta^{-1}_{X^vee}:
Wait, theta^{-1} acts on X, not X^vee. Let me be systematic.

braiding_naturality_left: for f : W -> X, any Y:
`f whisker Y circ beta_{X,Y}.hom = beta_{W,Y}.hom circ Y whisker f`

So `theta^{-1} whisker X^vee circ beta_{X,X^vee}.hom = beta_{X,X^vee}.hom circ X^vee whisker theta^{-1}`

Then:
```
beta_{X^vee,X}.hom circ theta^{-1} whisker X^vee circ beta_{X,X^vee}.hom
  = beta_{X^vee,X}.hom circ beta_{X,X^vee}.hom circ X^vee whisker theta^{-1}
  = monodromy(X,X^vee) circ X^vee whisker theta^{-1}
```

So the equation becomes:
```
X^vee whisker theta = monodromy(X,X^vee) circ X^vee whisker theta^{-1}
```
i.e.,
```
X^vee whisker theta^2 = monodromy(X,X^vee)
```
i.e.,
```
X^vee whisker (theta^2_X) = beta_{X,X^vee} circ beta_{X^vee,X}
```

By twist_tensor applied to X^vee and X (with appropriate rewriting):
```
theta_{X^vee tensor X} = (theta_{X^vee} tensor theta_X) circ beta_{X^vee,X} circ beta_{X,X^vee}
```

Hmm, this gives monodromy in terms of theta_{tensor} and theta tensor theta,
not directly theta^2 whisker.

OK I think I'm going in circles. Let me try the DIRECT approach that actually
worked in the Lean proof attempt.

---

## The correct helper lemma approach (from current Lean proof)

The Lean goal after all simplifications is:
```
eta circ f whisker X^vee circ theta whisker X^vee circ beta^{-1}_{X^vee,X} circ eps
  = eta circ f whisker X^vee circ theta^{-1} whisker X^vee circ beta_{X,X^vee} circ eps
```

So we need (after canceling the common prefix `eta circ f whisker X^vee`):
```
theta whisker X^vee circ beta^{-1}_{X^vee,X} circ eps
  = theta^{-1} whisker X^vee circ beta_{X,X^vee} circ eps
```

This is our `coeval_twist_braiding` helper, but stated at the evaluation end rather
than the coevaluation end. It was noted to possibly require theta^4 = id.

HOWEVER, with the full eta...eps structure, we have more room. The full equation is:
```
eta circ theta whisker X^vee circ beta^{-1} circ eps
  = eta circ theta^{-1} whisker X^vee circ beta circ eps
```
(after moving f whisker X^vee past the twist terms via naturality)

Using the mate-coeval identity:
```
eta circ theta whisker X^vee = eta circ X whisker theta_{X^vee}
```
(from coevaluation_comp_rightAdjointMate + twist_dual)

And the mate-eval identity:
```
theta_{X^vee} whisker X circ eps = X^vee whisker theta circ eps
```

These convert between "theta on X acting via whiskering" and "theta on X^vee
acting via whiskering".

### NEW APPROACH: Use twist_tensor on coevaluation

From twist_naturality on eta : 1 -> X tensor X^vee:
```
eta = eta circ theta_{X tensor X^vee}    (since theta_1 = id)
```

Expanding theta_{X tensor X^vee} via twist_tensor:
```
theta_{X tensor X^vee} = (theta_X tensor theta_{X^vee}) circ beta circ beta_{X^vee,X}
```

So:
```
eta = eta circ (theta_X tensor theta_{X^vee}) circ beta_{X,X^vee} circ beta_{X^vee,X}   ... (*)
```

Using mate-coeval: `eta circ X whisker theta_{X^vee} = eta circ theta whisker X^vee`:
```
eta circ (theta tensor theta_{X^vee}) = eta circ theta whisker X^vee circ X whisker theta_{X^vee}
  = eta circ theta whisker X^vee circ theta whisker X^vee    (by mate-coeval: X whisker theta_{X^vee} = theta whisker X^vee after eta)
```

Wait: mate-coeval says `eta circ X whisker theta_{X^vee} = eta circ theta_X whisker X^vee`.
So after eta, we can freely swap X whisker theta_{X^vee} with theta_X whisker X^vee.

So: `eta circ (theta_X tensor theta_{X^vee})`
  = `eta circ theta_X whisker X^vee circ X whisker theta_{X^vee}`  (tensorHom_def)
  = `eta circ theta_X whisker X^vee circ theta_X whisker X^vee`   (mate-coeval applied to second term)

So (*) becomes:
```
eta = eta circ (theta whisker X^vee)^2 circ beta circ beta_{X^vee,X}
```

This means:
```
eta circ (theta whisker X^vee)^2 circ beta circ beta_{X^vee,X} = eta
```

Now multiply on the right by (beta_{X^vee,X})^{-1}:
```
eta circ (theta whisker X^vee)^2 circ beta = eta circ beta_{X^vee,X}^{-1}    ... (**)
```

Our target is: `eta circ theta whisker X^vee circ beta^{-1} = eta circ theta^{-1} whisker X^vee circ beta`

From (**): `eta circ theta^2 whisker X^vee circ beta = eta circ beta^{-1}`

So: `eta circ beta^{-1} = eta circ theta^2 whisker X^vee circ beta`

Then:
```
eta circ theta whisker X^vee circ beta^{-1}
  = eta circ theta whisker X^vee circ theta^2 whisker X^vee circ beta   (using **)
  = eta circ theta^3 whisker X^vee circ beta
```

And we need this to equal `eta circ theta^{-1} whisker X^vee circ beta`.
So we'd need `theta^3 = theta^{-1}`, i.e., `theta^4 = id`.
This confirms the EARLIER FINDING that the naive approach requires theta^4 = id.

### THE FIX: Don't separate eta and eps!

The key insight is that we should NOT try to prove the helper lemma
`coeval_twist_braiding` separately. Instead, we need to use BOTH the
coevaluation identity AND the evaluation identity TOGETHER.

From the twist_tensor identity on eta:
```
eta = eta circ theta^2 whisker X^vee circ beta circ beta'   (where beta' = beta_{X^vee,X})
```

There should be a DUAL identity on eps:
From twist_naturality on eps : X^vee tensor X -> 1:
```
eps = theta_{X^vee tensor X} circ eps = eps   (since theta_1 = id)
```
Wait, theta_1 = id, so:
```
eps circ theta_{X^vee tensor X}^{-1} = eps
```
i.e., `theta_{X^vee tensor X} circ eps^T = eps^T` or dually:
```
eps = eps    ... (tautology from twist_naturality on eps)
```

Actually, let me be more careful. twist_naturality says:
`f circ theta_Y = theta_X circ f` for any f : X -> Y.
Applied to eps : X^vee tensor X -> 1:
`eps circ theta_1 = theta_{X^vee tensor X} circ eps`
Since theta_1 = id:
`eps = theta_{X^vee tensor X} circ eps`
i.e.,
`theta_{X^vee tensor X}^{-1} circ eps^{co} = eps^{co}`
Wait no. Let me write it correctly:
`eps = (twist (X^vee tensor X)).hom circ eps`
Hmm that's wrong, twist_naturality gives:
`eps circ (twist 1).hom = (twist (X^vee tensor X)).hom circ eps`
Since twist_unit: `(twist 1).hom = id`:
`eps = (twist (X^vee tensor X)).hom circ eps`

But eps : X^vee tensor X -> 1, and twist acts on X^vee tensor X:
`(twist (X^vee tensor X)).hom : X^vee tensor X -> X^vee tensor X`

So: `eps = eps circ (twist (X^vee tensor X)).inv`
(multiply both sides by (twist)^{-1} on the right... wait, twist acts before eps)

Actually the identity is: `eps = (twist (X^vee tensor X)).hom >>> eps`
Wait no. twist_naturality: `eps >>> (twist 1).hom = (twist (X^vee tensor X)).hom >>> eps`
Hmm, that has the wrong types. Let me think about the types:
- eps : X^vee tensor X -> 1
- twist_naturality for eps: `eps circ (twist (X^vee tensor X)).hom = (twist 1).hom circ eps`
  Wait, this has wrong types too. twist_naturality says for f : X -> Y:
  `f circ (twist X).hom = (twist Y).hom circ f`... no wait.

twist_naturality: `f >>> theta_Y = theta_X >>> f`
i.e., `f circ theta_Y.hom = theta_X.hom circ f` where f : X -> Y.
Hmm no: `f >>> theta_Y` means `f` then `theta_Y`, so `theta_Y circ f`...
No, in our notation (Lean/category theory): `f >>> theta_Y.hom = f circ theta_Y.hom`???

Actually in our Lean formalization:
```
twist_naturality : f circ (twist Y).hom = (twist X).hom circ f
```
Wait, the actual statement in our code is:
```
twist_naturality : ∀ {X Y : C} (f : X ⟶ Y),
    f ≫ (twist Y).hom = (twist X).hom ≫ f
```
So `f ≫ θ_Y = θ_X ≫ f`, i.e., `θ_Y ∘ f = f ∘ θ_X` (in diagrammatic order: f then θ_Y).

Applied to `ε_ X X^vee : X^vee ⊗ X ⟶ 𝟙`:
```
ε circ θ_1 = θ_{X^vee tensor X} circ ε
```
Since θ_1 = id: `ε = θ_{X^vee tensor X} circ ε`

Wait, `≫` is diagrammatic order, so:
```
ε ≫ (twist 1).hom = (twist (X^vee ⊗ X)).hom ≫ ε
```
means ε then θ_1 = θ_{X^vee⊗X} then ε.
Since θ_1 = id: `ε = (twist (X^vee ⊗ X)).hom ≫ ε`

So `(twist (X^vee ⊗ X)).hom ≫ ε = ε`, i.e., theta acts trivially before eps.

Now expand twist_tensor on X^vee and X:
```
θ_{X^vee ⊗ X} = (θ_{X^vee} ⊗ θ_X) ≫ β_{X^vee,X} ≫ β_{X,X^vee}
```

So:
```
((θ_{X^vee} ⊗ θ_X) ≫ β_{X^vee,X} ≫ β_{X,X^vee}) ≫ ε = ε
```

Using the mate identities (eval versions):
```
θ_{X^vee} ▷ X ≫ ε = X^vee ◁ θ_X ≫ ε
```

So `(θ_{X^vee} ⊗ θ_X) ≫ ε'` can be simplified...
Actually (θ_{X^vee} ⊗ θ_X) = θ_{X^vee} ▷ X ≫ X^vee ◁ θ_X (tensorHom_def)
= X^vee ◁ θ_X ≫ θ_{X^vee} ▷ X (whisker_exchange, since they commute)

So the eval identity `θ_{X^vee ⊗ X} ≫ ε = ε` gives:
```
(X^vee ◁ θ ≫ θ_{X^vee} ▷ X) ≫ β ≫ β' ≫ ε = ε
```
where we can use mate: X^vee ◁ θ = θ_{X^vee} ▷ X before ε
(but NOT generally — only when composed with ε at the end).

This is getting complex. Let me document the KEY APPROACH that should work:

### THE CORRECT APPROACH (avoiding helper lemma)

Instead of trying to prove `coeval_twist_braiding` as a standalone lemma,
prove the spherical identity DIRECTLY by:

1. Start from the goal: LHS = RHS (both are scalars: 1 -> 1)
2. After expanding j and applying drinfeldIso helpers, we have:
   ```
   eta circ beta^{-1} circ X^vee whisker theta circ X^vee whisker f circ eps
     = eta circ f whisker X^vee circ theta^{-1} whisker X^vee circ beta circ eps
   ```
3. Use twist_naturality to commute theta and f:
   - LHS: theta circ f = f circ theta, so X^vee whisker theta circ X^vee whisker f = X^vee whisker (f circ theta)
   - Then use braiding inv naturality to move f past beta^{-1}
4. Use mate identities (eval and coeval) to convert whisker types
5. The full eta...eps sandwich allows cancellations that individual halves don't

Alternatively: use `coeval_twist_braiding` but stated differently.
The correct version should be an identity involving BOTH eta and eps:

```
eta circ theta whisker X^vee circ beta^{-1} circ eps
  = eta circ theta^{-1} whisker X^vee circ beta circ eps
```

This is a scalar equation (1 -> 1) and should follow from:
- twist_tensor on eta (gives eta = eta circ theta^2 whisker ... circ beta circ beta')
- twist_tensor on eps (gives eps = theta^2_{...} circ eps via naturality)
- The eta/eps zigzag identities

---

## Section 8.10 continued: Trace and Dimension

### Equation 8.40 (Trace in ribbon category)
For f in End_C(X):
```
Tr(f) : 1 --coev_X--> X tensor X* --psi_X circ f tensor id_{X*}--> X** tensor X* --ev_X--> 1
```

### Proposition 8.10.12: ψ = θ∘u spherical iff θ ribbon
The canonical pivotal structure ψ = θ ∘ u is spherical if and only if θ is ribbon.

Proof uses that fusion categories are automatically unimodular (Theorem 8.10.7),
then invokes properties of the tensor structure δ.

**Key equation**: Tr(ψ_{X*}) = Tr(ψ_{X**}^* ∘ δ_{X*}^{-1})
By Corollary 7.21.8: right side = Tr(ψ_{X**})
So spherical iff Tr(ψ_{X*}) = Tr(ψ_{X**}) for all simple X, which is (8.39).

### Proposition 8.10.14
For any object X in ribbon category, the composition:
```
1 --coev_X--> X tensor X* --theta_X tensor id--> X tensor X* --c_{X,X*}--> X* tensor X --ev_X--> 1
```
equals dim(X).

---

## Section 8.13: The S-matrix

### Definition 8.13.1
A pre-modular category = ribbon fusion category = braided fusion category with spherical structure.

### Definition 8.13.2 (S-matrix)
```
s_{XY} = Tr(c_{Y,X} c_{X,Y})     (trace of monodromy)
```

### Proposition 8.13.8 (equation 8.48)
```
s_{XY} = theta_X^{-1} theta_Y^{-1} sum_Z N^Z_{XY} theta_Z dim(Z)
```
Proof: Apply Tr to both sides of twist_tensor formula (8.32).

### Proposition 8.13.10 (equation 8.49)
```
s_{XY} s_{XZ} = dim(X) sum_W N^W_{YZ} s_{XW}
```
Proof: Uses (8.50) which is a braiding identity, then applies trace.

---

## Section 8.14: Modular categories

### Proposition 8.14.2
```
S^2 = dim(C) E      (where E_{ij} = delta_{i,j*})
```
i.e., S^4 = dim(C)^2 id.

### Corollary 8.14.4 (Verlinde formula)
```
sum_X s_{XY} s_{XZ} s_{XW*} / dim(X) = dim(C) N^W_{YZ}
```

### Corollary 8.14.5
```
D^Z = S^{-1} N^Z S      (S-matrix diagonalizes fusion matrices)
```

---

## Section 8.15: Gauss sums and central charge

### Definition 8.15.1
```
tau^{+-}(C) = sum_X theta_X^{+-1} dim(X)^2
```

### Proposition 8.15.4
```
tau^+(C) tau^-(C) = dim(C)
```

---

## Section 8.16: Representation of the modular group

### Theorem 8.16.1
```
(ST)^3 = tau^-(C) S^2
```
where S = s-matrix, T = diag(theta_X^{-1}).

This gives a projective representation of SL(2,Z).

---

## Key takeaways for our formalization

1. **Ribbon -> Spherical proof**: EGNO only proves this for fusion categories
   (Prop 8.10.12) using semisimplicity. For our general RibbonCategory class,
   we need a DIRECT proof at the morphism level.

2. **The helper lemma `coeval_twist_braiding` is WRONG as stated** — it requires
   theta^4 = id. We need a different approach.

3. **Correct approach**: Work with the FULL scalar equation
   `eta ... eps = eta ... eps` (both sides are 1 -> 1), using BOTH zigzag
   identities and the twist_tensor identity applied to eta and eps simultaneously.

4. **All S-matrix formulas** (8.48, 8.49, Verlinde) match our theorem statements.

5. **Convention differences**: EGNO uses left duals, we use right duals.
   EGNO writes psi = u theta, we write j = theta^{-1} then u.

---

## Re-read of Prop 8.10.12 (session 3, 2026-02-23)

### Precise proof structure in EGNO

**Statement**: Let C be a braided **fusion** category with twist θ. The canonical
pivotal structure ψ = θ∘u is spherical iff θ is a ribbon structure.

**Proof (⇐ direction, ribbon → spherical)**:
1. θ*_X = (θ_X)* translates to ψ_{X*} = (ψ_X ∘ u_X⁻¹)* ∘ u_{X*}
2. By naturality of u and **unimodularity** (Theorem 8.10.7 — fusion categories
   are automatically unimodular), get:
   ψ_{X*} = ψ*_{X**} ∘ δ_{X*}⁻¹
   where δ is the distinguished invertible object from unimodularity
3. Since C is unimodular, δ = 1, so ψ_{X*} = ψ*_{X**}
4. This gives Tr(ψ_{X*}) = Tr(ψ*_{X**})
5. By **Corollary 7.21.8**: Tr(ψ*_{X**}) = Tr(ψ_{X**})
   (This corollary works for SIMPLE objects only — reduces to scalars)
6. Since X** ≅ X (via ψ itself), get Tr(ψ_{X*}) = Tr(ψ_X), i.e., spherical.

### Why this CANNOT be directly adapted to our setting

- Step 2 uses **unimodularity**, which is a property of FINITE tensor categories
- Step 5 uses **Corollary 7.21.8**, which requires **semisimplicity** (reduces to simples)
- Our RibbonCategory class has no semisimplicity assumption

### Prop 8.10.14 (useful identity, also from EGNO)

For any ribbon fusion category, for any object X:
```
1 --coev_X--> X ⊗ X* --θ_X ⊗ id--> X ⊗ X* --c_{X,X*}--> X* ⊗ X --ev_X--> 1
```
equals dim(X). This is `η ≫ θ ▷ X* ≫ β ≫ ε = dim(X)`.
This is a CONSEQUENCE of spherical, not a proof tool.

### Next steps for ribbon→spherical

Need to find a DIRECT morphism-level proof. Check Turaev "Quantum Invariants"
and Kassel "Quantum Groups" for diagrammatic proofs not relying on semisimplicity.
See ProofIdeas/Ribbon.md for detailed analysis of approaches tried.
