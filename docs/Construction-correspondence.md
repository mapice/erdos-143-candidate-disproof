# Construction: correspondence between the proof and the manuscript

The formal proof has the exact final conclusion and the same private-prime,
primitive-block, fixed-grid round construction. Two sufficient intermediate
statements are slightly simpler than those in the original candidate.

## Private-prime budget

For a finite state, the invariant is

    sum_{h in H} 1/h < 1/100.

When adjoining a private prime, choose it above all stored nonprivate numerator
parts, above the current grid, and so large that its reciprocal is smaller than
the remaining budget. `fresh_private_prime` proves this existence using Euclid's
unboundedness of the primes and the Archimedean property. No quantitative prime
number theorem or asymptotic prime distribution is used. This replaces the
indexed sufficient restriction H_i > 2^(i+10); it preserves exactly the density
bound needed at every finite stage.

## Stronger periodic filter

For a root p/(p-1), write q=p-1 and r=floor(q/D). Exclude the image of every
integer in [-r,r] in ZMod p. A closed collision

    | (p/q) D k - D n | <= 1

implies D |pk-qn| <= q, and hence |pk-qn| <= r. Since pk-qn is congruent to n
modulo p, the label lies in the excluded residue set. Its cardinality is at
most 2r+1, so its density is at most 3/D when p>=D. The proof actually chooses
p>=2D. Excluding a closed interval is stronger than excluding the manuscript's
half-open collision interval and is therefore sufficient for `RightFree`.

All labels also avoid multiples of every currently chosen private prime,
including the new one. At s<=floor(D/12) inserted roots, the total forbidden
density is less than

    1/100 + 3s/D <= 1/100 + 1/4 < 1/3.

The common period is the product of the finitely many moduli. Surjective
homomorphisms of finite additive groups preserve uniform density, and the
union bound does not require any independence or coprimality of the moduli.
The already proved `periodicPrimitiveSelection_proved` therefore applies.

## Parameter order and simultaneous invariants

`insert_block_exists` first chooses H, then the periodic exclusions, then a
finite primitive set P of weight greater than 1/6, and only then the auxiliary
prime G. Thus all maxima of P and all denominators of earlier rational points
are fixed before G is made large. The stored point is

    a = H N/q,  N=G D n,  q=HG-1.

Every private prime avoids every stored N. The new private prime avoids old
N's because it exceeds them. Old private primes avoid new N's because they
avoid G, D, and n. The new private prime also avoids D and n. The denominator
q is not divisible by H, and a/H>4.

At the beginning of a round, `state_grid_exists` chooses D>=48 divisible by
all old stored N's and avoiding all old private primes. It uses a product of
the stored N's, multiplied by a sufficiently large power of two, instead of
an lcm. Each old-round source is separated from an allowed lattice label by
more than four; every within-round source is handled by its virtual root.

The auxiliary prime forces the positive displacement to be below every old
rational denominator gap and at most 1/(2(Dn)^12). All new points are above
every old point plus one, so the reverse ordered inequality is also safe.
The exact primitive-block lemma handles distinct points within each new
block. These ingredients are assembled simultaneously in
`block_extension_valid`, rather than merely provided as assumed interfaces.

## Weight and recursion

Each block contributes strictly more than 1/(24D). The formal round theorem
uses the non-strict consequence

    mass(F') >= mass(F) + 1/576.

This is sufficient: after R rounds mass(F_R)>=R/576. Applying this bound at
R=(n+1)*576 makes the finite-prefix mass greater than n. The nested union is
therefore of ENNReal total weight equal to top. The non-strict round version
is weaker than the manuscript's strict inequality but has the same conclusion.

`nextState` uses Classical.choice only on the proved `round_extension_exists`.
`stateSequence` is ordinary natural-number recursion starting from the empty
valid state. Every finite stage retains all old atoms, so every ordered pair
in the union occurs together at some finite stage. No multiplier cutoff is
introduced. Local finiteness follows already from the k=1 separation bound.

## Closed theorem declarations

- `Erdos143.mainConclusion_proved : MainConclusion`
- `Erdos143.strongConclusion_proved : StrongConclusion`
- `Erdos143.realConclusion_proved`: explicit real subset, countability,
  rationality, lower bound 2, all ordered positive-natural multiplier
  inequalities, ENNReal divergence, and ordinary real non-summability

None of these declarations has an additional analytic, arithmetic, existence,
or construction hypothesis. The exact rational-to-real transfer uses the
injective map q |-> (q : Real) and an explicit equivalence of the two subtypes.
`constructedRealSet_not_summable` uses the nonnegativity of every real term,
so the ENNReal statement is genuine positive divergence, not Lean's default
value of a non-summable real `tsum`.
