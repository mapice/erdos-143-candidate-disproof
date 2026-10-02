# The periodic primitive-selection lemma: a proved Abel-average route

Status: the lemma at the end of this note is proved in Lean, with no added axioms or proof placeholders. This note covers the analytic proof of the periodic-selection lemma. The complete block/round construction and main existence theorem are now proved separately; see [Construction-correspondence.md](Construction-correspondence.md) and [Main.lean](../Erdos143/Main.lean).

## Exact proved statement

For each fixed integer L > 0, each set S of residue classes modulo L with |S|/L > 2/3, and each N ≥ 2, there exists a finite primitive set P of integers such that every n in P is at least N and lies in a class of S, and

    sum_{n in P} 1/(n log n) > 1/6.

The period and residue set are fixed before the cutoff and the finite primitive set are chosen. The theorem `Erdos143.periodicPrimitiveSelection_proved` proves the original `PeriodicPrimitiveSelection` proposition in `Definitions.lean`, including its `Fin L` encoding and rational density comparison. The equivalent `ZMod L` versions are `periodic_primitive_selection_real` and `periodic_primitive_selection`.

This proof does not claim that every sufficiently high individual Ω layer has large weight. It proves the existence of arbitrarily high sufficiently heavy layers by Abel averaging. The manuscript's stronger layerwise liminf assertion should not be presented as formalized by this argument.

## Notation and classical ingredients

Put w(n)=1/(n log n) for n≥2, and let Ω(n) count prime factors with multiplicity. For a Dirichlet character χ modulo L, real 0≤u≤1, and t>0, put

    Gχ(u,1+t) = product_p (1 - u χ(p) p^(-1-t))^(-1).

For each t>0 this is the absolutely convergent series

    sum_{n≥1} u^Ω(n) χ(n) n^(-1-t).

The n=0 convention in Lean contributes zero. The n=1 term is exactly 1.

The classical ingredients are the Euler products, character orthogonality, continuity of a nonprincipal L-function at s=1, and the principal-character residue

    t L(1+t,χ0) → κ_L = φ(L)/L.

The last identity also follows directly from the elementary bound 1/t≤ζ(1+t)≤1+1/t and the finite Euler factors at primes dividing L. Nonvanishing of L(1,χ) is not needed by this proof. No result about real original sets or modern almost-prime Erdős sums is used.

## 1. Uniform Euler-factor comparisons

For 0≤u≤1 and 0≤x<1, weighted AM–GM gives

    (1+x)^u ≤ 1+ux ≤ (1-ux)^(-1).

For complex z with |z|≤1/2, let A=|1-z|² and S=(1-u)+uA. The exact identity

    |1-uz|² = S - u(1-u)|z|²

and the inequalities A≥1/4, S≥1/4, u(1-u)≤1/4 imply

    |1-uz|² ≥ S(1-|z|²) ≥ A^u(1-|z|²).

The final step is again weighted AM–GM. Inverting gives

    |(1-uz)^(-1)|² ≤ |(1-z)^(-1)|^(2u) (1-|z|²)^(-1).

All the quadratic correction products are uniformly bounded by 2. Indeed, when |z_p|≤1/p,

    product_{p in T} (1-|z_p|²)^(-1)
      ≤ product_{n=2}^M (1-n^(-2))^(-1)
      = 2M/(M+1) < 2

for any finite prime set T and M≥max T. Passing through the convergent Euler products therefore yields

    |Gχ(u,s)|² ≤ 2 |L(s,χ)|^(2u),        s>1.

There is no complex-logarithm choice in this estimate.

For the principal character all nonzero prime factors are positive real numbers. The identity

    (1+x)(1-x²)^(-1) = (1-x)^(-1)

and the same correction bound show

    Gχ0(u,s) ≥ (L(s,χ0)/2)^u.

These statements, including passage from finite to convergent products, are checked in `EulerFactorBounds.lean`, `CorrectionProducts.lean`, `TwistedBound.lean`, and `PrincipalBound.lean`.

## 2. Bounds at zero and infinity

For nonprincipal χ, continuity of L(s,χ) on the real compact segment [1,2] and the squared norm estimate show

    |Gχ(u,1+t)| ≤ C_L,χ       (0≤u≤1, 0<t≤1).

The constant is allowed to depend on the fixed character and modulus.

For the principal character, the residue identity supplies some eps>0, eps≤1, for which

    κ_L/(2t) ≤ L(1+t,χ0) ≤ 2κ_L/t,     0<t≤eps.

Consequently

    Gχ0(u,1+t) ≥ (κ_L/(4t))^u.

For the unrestricted product (modulus one), the upper bound gives, after decreasing eps if necessary,

    |G1(u,1+t)| ≤ 4 t^(-u),            0≤u≤1, 0<t≤eps.

At infinity, uniformly for every character and even complex |u|≤1,

    |Gχ(u,1+t)-1| ≤ C exp(-t log 2),  t≥1.

For this last estimate, bound the terms n≥2 by n^(-1-t)≤n^(-2)2^(-(t-1)) and use the convergent square-reciprocal series. Continuity in t>0 is proved through the Dirichlet series' abscissa of absolute convergence.

## 3. Justified integration

For 0≤u<1 the preceding bounds are integrable. Thus

    Jχ(u) = integral_0^infinity (Gχ(u,1+t)-1) dt
          = sum_{n≥2} χ(n) u^Ω(n) w(n).

The interchange is not assumed. For the unrestricted nonnegative series, integrability of its pointwise sum first proves summability of the integrals. The identity

    integral_0^infinity n^(-1-t) dt = 1/(n log n)

then proves absolute convergence of the weighted logarithmic series. The twisted series is dominated term by term by this nonnegative series, giving summability of its integrals of norms and the complex termwise-integral identity.

The exact checked identity is `integratedGeneratingValue_eq_weighted_series`, or its unshifted-index version `integratedGeneratingValue_eq_full_series`.

For nonprincipal χ the bounds are uniform in 0≤u≤1, so Jχ(u) stays bounded and

    (1-u)Jχ(u) → 0                       as u→1 from below.

This is `nonprincipal_normalized_integral_tendsto_zero`.

For the principal character the integrand is real and nonnegative. Integrating the lower bound only over (0,eps) gives

    Jχ0(u) ≥ (κ_L/4)^u eps^(1-u)/(1-u) - eps.

Therefore

    liminf_{u→1-} (1-u)Jχ0(u) ≥ κ_L/4.

The checked theorem is `principal_abel_lower_bound`; its precise lower-limit predicate is `HasAbelLowerBound`.

## 4. Every residue class

For an invertible class b modulo L, orthogonality gives

    sum_{n≡b (mod L), n≥2} u^Ω(n)w(n)
      = (1/φ(L)) sum_χ χ(b^(-1)) Jχ(u).

Finite summation, absolute convergence, the principal lower bound, and the vanishing nonprincipal contributions imply

    liminf_{u→1-} (1-u) sum_{n≡b (mod L), n≥2} u^Ω(n)w(n)
      ≥ 1/(4L).

For a possibly noninvertible class, write g=gcd(b,L), M=L/g, c=b/g. Then c is invertible modulo M; when M=1 its only class is a unit. Multiplication m↦gm embeds the class c modulo M into the original class b modulo L, and Ω(gm)=Ω(g)+Ω(m).

The logarithmic shift has a uniformly summable error. For x>1 and y≥0,

    0 ≤ 1/(x log x) - 1/(x(log x+y)) ≤ y/(x(log x)²).

Moreover C2=sum_{m≥2}1/(m(log m)²) is finite. The Lean proof obtains this by integrating t(ζ(1+t)-1): the integrand is bounded near zero and decays exponentially at infinity, and its individual integrals are 1/(m(log m)²).

Writing A_{M,c}(u) for the class mass, the injection and the shift estimate give

    A_{L,b}(u) ≥ (u^Ω(g)/g) A_{M,c}(u) - (log g/g) C2.

This inequality also covers the harmless m=0,1 conventions, whose logarithmic weights are zero. After multiplication by 1-u the error vanishes and u^Ω(g)/g tends to 1/g. The lower bound is consequently 1/(4gM)=1/(4L), for every class, including b=0. This is `all_residues_abel_lower_bound`.

## 5. Abel averaging and finite extraction

Summing over S gives

    liminf_{u→1-} (1-u) sum_{n mod L in S} u^Ω(n)w(n)
      ≥ |S|/(4L) > 1/6.

Let f_r be the weight of the r-th Ω layer restricted to S. Each f_r is finite: the convergent weighted series at u=1/2 dominates that layer after multiplication by 2^r. Absolute summability also justifies

    sum_{n mod L in S} u^Ω(n)w(n) = sum_{r≥0} u^r f_r.

If all r≥R satisfied f_r≤1/6, then for 0≤u<1,

    (1-u) sum_r u^r f_r
      ≤ 1/6 + (1-u) sum_{r<R} f_r,

contradicting the strict Abel lower bound. Thus there are arbitrarily high r with f_r>1/6. Choose r≥N≥2. The r-th Ω layer is primitive; also n≥2^r≥r≥N. A finite truncation of this positive convergent layer still has weight >1/6.

This is precisely the selection lemma required by the construction. Its constants remain 1/6 per primitive label set, 1/(24D) per block, and 1/576 per completed round. Only the analytic route has changed; no stronger layerwise asymptotic or liminf assertion is needed.

## Verification record

- Lean 4.24.0
- mathlib commit f897ebcf72cd16f89ab4577d0c826cd14afaafc7
- `bash scripts/verify.sh` passed with warnings treated as errors
- `#print axioms Erdos143.periodicPrimitiveSelection_proved` reports only `propext`, `Classical.choice`, and `Quot.sound`
- MainConclusion and StrongConclusion are proved by the separate construction in `Erdos143/Main.lean`; their real-domain interpretation is proved in `Erdos143/RealConclusion.lean`
