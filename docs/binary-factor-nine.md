# Binary factor nine

This is the binary proof. Every analytic step is an exact rational-logarithm
bound proved in Lean; no step is delegated to a numerical certificate, which
is what "certificate-free" means throughout this repository.

Let `p` be a probability law on `{0,1} x {0,1}`. With the notation of the
[constructive blueprint](blueprint.md), the theorem is:

> **Binary factor-nine theorem.** If `p` has full support, there is an
> attained `tau`-optimal latent `L` and a deterministic code `g` such that
>
> ```text
> W3(L) <= 8 * tau(p),
> T(p) <= D_p(g) <= 9 * tau(p).
> ```
>
> On full support, `g` may be the law-only selector `g_p` of the blueprint.
> For every binary law, with or without zero cells, `T(p) <= 9 * tau(p)`.

The theorem is `kernel-verified` in this repository. The public endpoint
`Binary.T_le_nine_mul_tau` covers every binary law.
`Binary.exists_optimalLatent_w3_le_eight_of_fullSupport` supplies the selected
optimal latent, and
`Binary.detScore_selector_le_nine_mul_tau_of_fullSupport` bounds the law-only
selector on full support. On a law with a zero cell, section 6 transfers the
bound on `T`; `Binary.exists_code_detScore_le_nine_mul_tau` supplies a
deterministic witness. The sparse conclusion includes no `W3` estimate and no
bound for the named selector.

The proof uses exact rational-log bounds and no interval certificate. See the
[verification procedure](../verification/README.md) and the
[admission record](../verification/admissions.md) for its audits and discovered
axiom sets.

For the construction, start with the [blueprint's selector recipe](blueprint.md#5-recover-the-code-from-the-law)
and [section 7](#7-pricing-and-recovery-from-the-law), which connects the chart
witness to the code chosen from the law. For the full proof, follow these steps:

| Step | Sections |
|---|---|
| Select the optimizer and express the two code costs | [1. Normal form](#1-binary-normal-form), [2. Two-arm identity](#2-the-two-arm-identity), [3. Entropy identities](#3-homogeneous-entropy-identities) |
| Bound each arm and close the seam | [4. Nonpositive phase](#4-the-nonpositive-phase), [5. Positive phase](#5-the-positive-phase) |
| Extend the bound on `T` to laws with zero cells | [6. Sparse and degenerate laws](#6-sparse-and-degenerate-laws) |
| Price the witness and recover the full-support selector | [7. Pricing and recovery](#7-pricing-and-recovery-from-the-law) |

## 1. Binary normal form

For a full-support binary law, the optimizer-selection theorem supplies an
attained `tau`-optimal latent with at most two distinct active component laws.

If there is one active component, the latent is constant. The constant code has
`W3Cost = 0`, so `W3(L) = 0`.

Otherwise observable and latent relabeling put the optimizer on the
two-contact chart. It is convenient to display its closed compactification:

```text
q0 = (A,1,r,D)/Q,
q1 = (A,r,1,D)/Q,

0 <= x <= 1,
r = x^4,
m = x^3/(1+x+x^2),
2*m <= s = A+D <= x^2,
A*D = r*(x^2-s)/(1+x^2+r),
Q = 1+r+s,
0 <= pi <= 1/2.
```

The strict realized region has

```text
0 < x < 1,
2*m <= s < x^2,
0 < pi <= 1/2.
```

The faces `s=x^2`, `pi=0`, `x=0`, and `x=1` are analytic or continuity
boundaries, not positive two-contact chart points.

The two contacts have prior weights `1-pi` and `pi`. Put

```text
e   = r + pi*(1-r),
ell = 1 - pi + pi*r.
```

The observable law on the chart is `(A,ell,e,D)/Q`.

The exact binary code reduction applies to the global minimum over all
deterministic codes. It leaves two candidates: the constant code and the
singleton isolating the high likelihood-ratio cell.

## 2. The two-arm identity

Let `Z=(X,Y)` and write

```text
K = I(L;Z).
```

For a deterministic code `g`, define

```text
Reward_L(g) = H(g) - 4 H(g | L).
```

Then

```text
W3Cost_L(g) = K - Reward_L(g).
```

Let `R_H` be the reward of the high singleton. Choose `g_chart` to be that
singleton when `R_H >= 0` and the constant code otherwise. Its cost is exactly

```text
W3Cost_L(g_chart) = K - max(0,R_H).
```

The separate binary reduction theorem proves that this code minimizes
`W3Cost` over the canonical code space. The factor-nine upper bound only needs
`W3(L) <= W3Cost_L(g_chart)`, so the argument follows the selected code's cost.

There are two phases:

```text
R_H <= 0:  W3Cost_L(g_chart) = K,
R_H >= 0:  W3Cost_L(g_chart) = K-R_H.
```

## 3. Homogeneous entropy identities

Use natural logarithms in the chart formulas and define

```text
E(u,v) = (u+v)*log(u+v) - u*log(u) - v*log(v),
```

with `0*log(0)=0`. Let

```text
C    = pi*(1-pi)*(1-r)^2,
U(z) = (z+r)*(z+1),

b(z) = E(z,e) + E(z,ell) - E(z,r) - E(z,1).
```

Multiplication by `Q*log(2)` converts the bit-valued information quantities to

```text
Kbar = E(e,ell) - E(r,1),
Bbar = b(A) + b(D),

A_H = (1-pi)*E(r,1+s) + pi*E(1,r+s),
I_H = E(e,ell+s) - A_H,
Rbar = I_H - 3*A_H.
```

In particular,

```text
Kbar = Q*log(2)*K,
Bbar = Q*log(2)*Bq,
Rbar = Q*log(2)*R_H.
```

Here `Bq` is the sum of the two latent-observable conditional information
terms in `score_p(L)`. If `M = I(X;Y | L)` and
`Mbar = Q*log(2)*M`, then optimality gives

```text
Q*log(2)*tau(p) = Mbar + Bbar,
Mbar >= 0.
```

Differentiating in `C` and integrating from `C=0` gives

```text
Kbar
  = integral_0^C integral_0^infinity
      1/(U(z)+c) dz dc,

b(z)
  = integral_0^C integral_0^z
      1/(U(t)+c) dt dc,

b'(z) = beta(z) = log(1+C/U(z)).
```

Hence `b` is nonnegative, increasing, and concave, while `beta` is nonnegative,
decreasing, and convex. Nonnegative, not positive: at `pi = 0` the contact mass
`C` vanishes and `beta` is identically zero. Strict positivity needs extra
hypotheses on the chart, and the argument below never uses it.

Every fixed logarithm bound below is exact rational arithmetic. For `u>0`, put
`y=(u-1)/(u+1)`. Then `|y|<1` and

```text
log(u) = 2 * sum_(k=0)^n y^(2*k+1)/(2*k+1) + R_n,

|R_n|
  <= 2*|y|^(2*n+3)/((2*n+3)*(1-y^2)).
```

Taking `n=100` and comparing the rational partial sum and remainder proves each
displayed fixed logarithm inequality below without floating-point input.

## 4. The nonpositive phase

Assume `R_H <= 0`. It is enough to prove

```text
Kbar <= 8*Bbar,
```

because `Mbar >= 0`.

Put

```text
rho = r/(1+x^2+r).
```

The contact equation is equivalent to

```text
(A+rho)*(D+rho) = rho*x^2 + rho^2.
```

Differentiation along this fiber gives

```text
d Bbar/ds
  = integral_0^C
      c/((U(A)+c)*(U(D)+c)) dc
  >= 0.
```

At the lower seam `s=2m`, one has `A=D=m`. Therefore

```text
Bbar >= 2*b(m).
```

The reward moves in the opposite direction:

```text
d Rbar/ds
  = -3*log Q - log(ell+s)
    +4*(1-pi)*log(1+s)
    +4*pi*log(r+s)
  < 0.
```

It remains to prove `Kbar <= 16*b(m)`.

### Small `x`

For `x <= 3/10`, the condition `Rbar <= 0` forces

```text
pi < 10*r.
```

Indeed, at the upper fiber endpoint `s=x^2`, exact entropy bounds give positive
reward at both `pi=10r` and `pi=1/2`. Put `q=x^2`, so
`0<q<=9/100`, `r=q^2`, `Q=1+q+q^2`, and at `pi=10r` put
`a=e/r=11-10q^2`. Cubic lower and upper entropy bounds give

```text
Rbar/r >= P(q)
  +(7-40q-10q^2)*log(Q)
  +40q(1+q)*log(1+q)
  -2(7-20q+10q^2)*log(q)
  -a*log(a),

P(q)
  = [1000*q^10 - 3400*q^8 - 100*q^7 + 3730*q^6 + 180*q^5
     -1314*q^4 -249*q^3 -215*q^2 -52*q +14]
    / [2*(1+q+q^2)^2].
```

The first two logarithmic terms are nonnegative. Also

```text
7-20q+10q^2 >= 5281/1000,
-log(q) >= log(100/9) > log(11),
a*log(a) <= 11*log(11),
log(11) < 12/5.
```

Dropping the positive numerator monomials of `P` and maximizing every negative
monomial and the denominator at `q=9/100` gives

```text
P(q) >= 365537402057293/120582361000000.
```

Consequently

```text
Rbar/r
  > 365537402057293/120582361000000 - 657/625
  = 238781224174093/120582361000000
  > 74007309/200000000
```

at `pi=10r`.

For balance, let `f(q)` be `Rbar` at `s=x^2` and `pi=1/2`.
Differentiation simplifies to

```text
f'(q)
  = (2q+1)*log(2)
    +(12q+2)*log(q)
    +(2q+2)*log(1+q)
    -(6q+3)*log(1+q+q^2)
    -q*log(1+q^2).
```

Discarding the last two negative terms and using
`log(2)<7/10`, `log(q)<-9/4`, and `log(1+q)<=q` gives

```text
f'(q)
  < (59/50)*(7/10) - 2*(9/4) + (109/50)*(9/100)
  = -17389/5000 < 0.
```

At `q=9/100`, the exact logarithm lemma gives

```text
log(2)                    >  693147/1000000,
log(109/100)              >   86177/1000000,
log(9/100)                > -2407950/1000000,
log(10981/10000)          <   93582/1000000,
log(10081/10000)          <    8068/1000000.
```

Substitution yields

```text
f(9/100)
  > 900483/1250000000
  > 20241/100000000
```

at balance. Strict concavity in `pi` makes the reward positive throughout the
interval between `10r` and `1/2`, contradicting reward monotonicity in `s`.

For each `c` in `[0,C]`, let `e_c <= ell_c` have sum `1+r` and product `r+c`.
The inequalities

```text
e_c <= 11*r,
ell_c <= 1,
1+x+x^2 <= 7/5
```

and

```text
6561*625 > 1331*2401
```

give

```text
16 * integral_0^m
       1/((z+e_c)*(z+ell_c)) dz
  >= integral_0^infinity
       1/((z+e_c)*(z+ell_c)) dz.
```

Integrating in `c` yields `Kbar <= 16*b(m)`.

### Remaining `x`

For `x >= 3/10`, put

```text
G(pi) = 16*b(m) - Kbar.
```

Then

```text
G'(pi)/(1-r)
  = 15*log(ell/e)
    -16*log((ell+m)/(e+m)).
```

Writing the ratio of the two logarithms as

```text
atanh(k*zeta)/atanh(zeta),
zeta = (ell-e)/(ell+e),
k    = (1+r)/(1+r+2*m),
```

exposes positive odd-power series whose coefficient ratios `k^(2*n+1)`
decrease with `n`. Differentiating and pairing terms shows that the quotient
decreases with `zeta`. Since `zeta` decreases with `pi`, `G'` can change sign
only from positive to negative. Thus `G` has no interior minimum. At `pi=0`,
`G=0`.

At `pi=1/2` and `3/10 <= x <= 1/2`,

```text
b(m) >= m*log((1+x^3)^2/(4*x^3)).
```

The product on the right has no interior minimum. Its endpoint comparisons
reduce to the integer inequalities

```text
39^9 > 2^47,
3^32 > 2^47.
```

They imply `16*b(m) >= log 2 >= Kbar`.

For `1/2 <= x < 1`, put `y=(1+r)/2`. The same rational-kernel comparison used
for small `x` applies whenever

```text
e_c^3 * ell_c <= (9*m)^4.
```

Here `e_c <= y` and `ell_c <= 1`, so it is enough to prove
`y^3 <= (9*m)^4`. The factorization

```text
238*x^3 - 16*(1+x+x^2)*(1+x^4)
  = -2*(x-2)*(2*x-1)*(4*x^4+14*x^3+35*x^2+14*x+4)
  >= 0
```

gives `m >= (16/119)*y`. Also `y >= 17/32` and the exact rational comparison

```text
(144/119)^4 * (17/32) >= 1
```

imply

```text
y^3 <= ((144/119)*y)^4 <= (9*m)^4.
```

The rational-kernel estimate therefore gives `Kbar <= 16*b(m)` after
integration in `c`, completing the balanced-prior endpoint. The endpoint
minimum in `pi` then gives the same bound for every prior in `[0,1/2]`.


Consequently

```text
R_H <= 0
  ==> Kbar <= 8*Bbar
  ==> W3(L) <= 8*tau(p).
```

## 5. The positive phase

Assume `R_H >= 0`. Let `I_low` be the information of the exchanged low
singleton and define

```text
N_H   = Kbar-I_H,
N_low = Kbar-I_low,
F     = b(s).
```

Exact entropy cancellation gives

```text
F = N_H + N_low.
```

The high singleton has at least as much information as the low singleton. For
fixed `x,s`, write

```text
c     = r/Q,
b     = 1/Q,
delta = b-c,
v     = c+pi*delta,
u     = b-pi*delta.
```

Define the normalized information difference by

```text
I_diff(pi) = (I_H-I_low)/Q.
```

Then

```text
I_diff(0) = I_diff(1/2) = 0,
I_diff''(pi)
  = delta^2 * (1/(u*(1-u)) - 1/(v*(1-v)))
  <= 0,
```

because `v <= u <= 1-v` on `0 <= pi <= 1/2`. Hence

```text
I_H >= I_low,
N_H <= F/2.
```

Concavity of `b` and `b(0)=0` also give

```text
Bbar = b(A)+b(D) >= b(A+D) = F.
```

The selected high-arm cost satisfies

```text
Q*log(2)*W3Cost_L(g_chart)
  = Kbar-Rbar
  = N_H + 3*A_H.
```

It is therefore enough to prove

```text
A_H <= (5/2)*F.
```

### Reduction to two seam endpoints

Reward monotonicity in `s` reduces phase exclusion to the seam `s=2m`.
An exact Bernoulli-entropy comparison at `x=2/5` gives `Rbar<0`. For larger
`x`, the seam channel is an affine garbling of the `x=2/5` channel. Its mutual
information decreases while its conditional entropy increases. Therefore

```text
R_H >= 0  ==>  x < 2/5.
```

For `x<2/5`, concavity of `Rbar` in `pi` bounds it by its tangent at zero.
Writing

```text
H0 = E(r,1+s),
H1 = E(1,r+s),
L  = log((1+s)/r),
```

that tangent is

```text
T(pi) = -3*H0 + pi*((1-r)*L + 4*H0 - 4*H1).
```

Here `0 <= s <= 1`, since the strict chart has `s < x^2 < 1`. Under
these bounds, the inequalities `H0 >= r*L` and `H1 >= r*L` imply

```text
T(3r) <= -3*r^2*L < 0.
```

Thus

```text
R_H >= 0  ==>  pi > 3r.
```

Set

```text
J = (5/2)*F - A_H,
t = (1+s)/(r+s).
```

Direct differentiation gives

```text
J_s
  = (5/2)*beta(s)
    - pi*log t
    - log(1+r/(1+s)).
```

On `x<2/5` and `pi>=3r`, one has

```text
(3/2)*beta(s) >= pi*log t,
beta(s) >= log(1+r/(1+s)).
```

Hence `J_s >= 0`. The function `J` is concave in `pi`, so its minimum on
`[3r,1/2]` occurs at an endpoint. The positive phase is reduced to

```text
s = 2m,
pi = 3r or pi = 1/2.
```

### Balanced endpoint

At `pi=1/2`, put `y=(1+r)/2`. Convexity of `beta` gives

```text
F >= 2*m*beta(m),
beta(m) = log((1+x^3)^2/(4*x^3)).
```

An entropy upper bound gives `A_H <= U_bal`, where

```text
U_bal = (1/2) *
  (r*(1+log(Q/r)) + (r+2*m)*(1+log(Q/(r+2*m)))).
```

After division by `m`, it is enough to prove positivity of the decreasing
function

```text
g_half(x) = 4*log((1+x^3)^2/(4*x^3)) - U_bal/m.
```

At `x=2/5`, the required exact logarithm bounds are

```text
log(17689/4000) > 37/25,
log(812/133) < 909/500,
log(78/125) > -59/125,
log(328/125) > 241/250.
```

The resulting margin is

```text
3597/62500 > 0.
```

In fact this proves the stronger estimate `A_H < 2*F`.

### Endpoint `pi=3r`

At `pi=3r` and `s=2m`, put

```text
q = r+s,
t = s/r,
Lambda(t)
  = (t+17/5)*log(t+17/5)
    -(17/5)*log(17/5)
    -(t+1)*log(t+1).
```

The kernel lower bound and entropy upper bound give

```text
F >= r*Lambda(t),

A_H/r
  <= (1-3r)*(log(Q/r)+1)
     +3q*(log(Q/q)+1)
  = U(x).
```

Set

```text
G(x) = (5/2)*Lambda(t) - U(x).
```

Write `s=2*m`, `q=r+s`, `Q=1+q`, and use primes for derivatives in `x`.
Differentiation gives

```text
U' = -3*r'*log(Q/r) - 4/x
     + 3*(r'+s')*log(Q/q) + (1+3*s)*(r'+s')/Q.
```

On `0<x<=2/5`, one has `q<=1/7`, so
`log(Q/q)>=log(8)>=56/27`. Also,

```text
r'*s/(r*s') = 4*(1+x+x^2)/(3+2*x+x^2) <= 56/27.
```

These bounds give
`r'*s/r <= s'*log(Q/q)`. Together with `log(q/r)<=s/r`, they imply
`U' >= -4/x`.

The other derivative term satisfies

```text
(5/2)*(-t')*log((t+17/5)/(t+1)) >= 4/x.
```

Indeed, `log(v)>=1-1/v` reduces this inequality to

```text
5 + 3*x + x^2 - 51*x^3 - 34*x^4 - 17*x^5 > 0.
```

The negative tail is at most

```text
(1683/25)*x^3 <= 13464/3125 < 5.
```

Thus `(5/2)*Lambda'(t)*t' <= -4/x <= U'`, which proves `G'<=0`.

At `x=2/5`, a four-panel midpoint bound gives

```text
Lambda(125/39)
  >= (125/156)*log(
       1157525834384227/69564432491875),
```

and the rational inside the logarithm is greater than `16`. The endpoint
comparison is

```text
(5/2)*Lambda(125/39) - U(2/5)
  >= 17500/3159 - 224632/40625
  = 101924/9871875
  > 0.
```

Thus `A_H < (5/2)*F` throughout the positive phase. Therefore

```text
Q*log(2)*W3Cost_L(g_chart)
  = N_H + 3*A_H
  <= F/2 + (15/2)*F
  = 8*F
  <= 8*Bbar
  <= 8*Q*log(2)*tau(p).
```

Since `W3(L) <= W3Cost_L(g_chart)`, this proves the factor-eight W3
bound at the selected optimizer on the strict chart.

## 6. Sparse and degenerate laws

Sections 1 to 5 argue on the positive two-contact chart. For a full-support
binary law the normal form of section 1 puts the selected optimizer either at a
single active component, where the constant code gives `W3(L) = 0`, or on the
strict chart, where sections 4 and 5 give `W3(L) <= 8*tau(p)`. The faces of the
compactification are not positive chart points, so a law with a zero cell is not
covered by that argument.

This section closes the gap by transferring the deterministic bound itself from
full-support laws to all laws. The transfer is stated for a general constant, is
proved by an explicit smoothing construction, and uses no subsequence extraction
and no limit latent. It does use the attainment half of the optimizer-selection
theorem quoted in section 1: for the sparse law `p` there is a finite stochastic
latent whose score equals `tau(p)`. Only that existence is used here, not the
two-component normal form.

Everything below is on four observable cells, but nothing in the argument uses
binarity: only that the observable alphabets are finite and nonempty. What is
binary-specific is the full-support input that the transfer consumes.

### Mixture form and the smoothing family

Write `Z = {0,1} x {0,1}` for the observable cells and `N = card(Z) = 4`. A
finite stochastic latent `L` for a law `p` is presented in mixture form as a
finite index set `I`, a prior `pi` on `I`, and component laws `q_v` on `Z` with

```text
sum_{v in I} pi_v * q_v = p.
```

This is the form in which the blueprint writes latent decompositions, and `pi_v`
below always means such a prior weight. No chart parameter of sections 1 to 5
appears in this section.

Since `Z` is nonempty, the uniform law `u` with `u(z) = 1/N` exists. For `t` in
`[0,1]` set

```text
p_t = (1-t)*p + t*u.
```

Each `p_t` is a law: it is a convex combination of two laws, hence nonnegative
with total mass `(1-t) + t = 1`. For `t > 0` it has full support, because

```text
p_t(z) >= t*u(z) = t/N > 0
```

for every cell `z`.

All quantities below are in bits, with `0 log 0 = 0`. A change of logarithm base
multiplies both sides of every inequality in this section by the same positive
constant, so the statements are base-independent.

### Continuity of entropy at the boundary of the simplex

**Lemma 6.1 (entropy is continuous on the closed simplex).** Let `S` be a finite
set and let `Delta(S)` be the closed simplex of laws on `S`, viewed as a subset
of `R^S`. Then `m -> H(m)` is continuous on `Delta(S)`, including at laws with
zero entries. Consequently, for every fixed map `f : S -> U` into a finite set,
`m -> H(f_* m)` is continuous on `Delta(S)`, where `f_* m` is the pushforward
`(f_* m)(w) = sum_{f(s)=w} m(s)`.

*Proof.* Put

```text
theta(x) = x*log(x)   for x > 0,
theta(0) = 0.
```

Then `H(m) = -sum_{s in S} theta(m(s))` for every `m` in `Delta(S)`, so it
suffices that `theta` is continuous on `[0,1]`. Continuity away from `0` is
clear. At `0`, write `x = 2^(-r)` with `r >= 0`, so that

```text
|theta(x)| = r * 2^(-r).
```

From `exp(y) >= y^2/2` for `y >= 0` one gets
`2^r = exp(r*log_e 2) >= (r*log_e 2)^2/2`, hence for `r > 0`

```text
0 <= r*2^(-r) <= 2/(r*(log_e 2)^2),
```

which tends to `0` as `r -> infinity`, that is, as `x` decreases to `0`. So
`theta` is continuous at `0`, and `H` is a finite sum of continuous functions.

For the pushforward, each coordinate of `f_* m` is a finite sum of coordinates of
`m`, so `m -> f_* m` is linear, hence continuous, and it maps `Delta(S)` into
`Delta(U)`. Composing with `H` on `Delta(U)` gives the second claim.

Every quantity used below is a fixed finite linear combination of entropies of
pushforwards of the law along fixed maps, so Lemma 6.1 gives its continuity in
the law without further comment.

### The score decomposition

**Lemma 6.2 (component decomposition of the score).** For a law `m` on `Z` write
`m_X` and `m_Y` for its two marginals and put

```text
Psi(m) = 2*H(m) - H(m_X) - H(m_Y).
```

With `Phi` as in the blueprint, `Phi(q) = 3*H(q) - 2*H(q_X) - 2*H(q_Y)`, every
finite stochastic latent `L = (I, pi, q)` for `p` satisfies

```text
score_p(L) = Psi(p) - sum_{v in I} pi_v * Phi(q_v).
```

*Proof.* Let `J(v,z) = pi_v * q_v(z)` be the joint law of `L` and the
observations. For a fixed map `f` defined on `Z`, the joint law of `(L,f)` is
`(v,w) -> pi_v * (f_* q_v)(w)`, so

```text
H(L,f)
  = - sum_{v,w} pi_v*(f_* q_v)(w) * log(pi_v*(f_* q_v)(w))
  = H(pi) + sum_v pi_v * H(f_* q_v).                          (6.1)
```

A label with `pi_v = 0` contributes zero to both sides, since the entropies
`H(f_* q_v)` are finite and `0 log 0 = 0`.

Expanding the three terms of `score_p(L)` into entropies,

```text
I(X;Y | L) = H(X,L) + H(Y,L) - H(X,Y,L) - H(L),
I(L;X | Y) = H(L,Y) + H(X,Y) - H(L,X,Y) - H(Y),
I(L;Y | X) = H(L,X) + H(X,Y) - H(L,X,Y) - H(X),
```

and adding gives

```text
score_p(L)
  = 2*H(L,X) + 2*H(L,Y) + 2*H(X,Y)
    - 3*H(L,X,Y) - H(L) - H(X) - H(Y).                        (6.2)
```

Apply (6.1) with `f = X`, `f = Y`, and `f = (X,Y)`, and use that the observable
marginal of `J` is `p`:

```text
H(L,X)   = H(pi) + sum_v pi_v * H((q_v)_X),
H(L,Y)   = H(pi) + sum_v pi_v * H((q_v)_Y),
H(L,X,Y) = H(pi) + sum_v pi_v * H(q_v),
H(L)     = H(pi),
H(X,Y)   = H(p),   H(X) = H(p_X),   H(Y) = H(p_Y).
```

Substituting into (6.2), the coefficient of `H(pi)` is `2 + 2 - 3 - 1 = 0`, so
those terms cancel and what remains is

```text
2*H(p) - H(p_X) - H(p_Y)
  - sum_v pi_v * (3*H(q_v) - 2*H((q_v)_X) - 2*H((q_v)_Y)),
```

which is the claimed identity.

**Lemma 6.3 (a zero-weight label is inert).** Let `L = (I, pi, q)` be a finite
latent for `p`. Adjoin one new label `*` with prior weight `0` and an arbitrary
law as its component. The result is again a finite latent for `p`, and its score
equals `score_p(L)`.

*Proof.* The mixture is unchanged because the new component enters with
coefficient `0`, so the enlarged family is a latent for the same `p` and `Psi(p)`
is the same. By Lemma 6.2 the only new term in the component sum is
`0 * Phi(q_*) = 0`. Hence the score is unchanged.

At the level of entropies the same fact reads: the enlarged joint law assigns
mass `0` to every coordinate containing `*`, so each marginal appearing in the
score is either unchanged or gains entries equal to zero, and zero entries alter
neither mass nor entropy.

### The smoothed latent

Let `L* = (I, pi, q)` be a finite latent with `score_p(L*) = tau(p)`, supplied by
the attainment statement quoted in section 1. For `t` in `[0,1]` define the
smoothed latent `L_t` for `p_t` by adjoining a single new label `*` that carries
all the uniform mass:

```text
index set   I + {*},
prior       pi_t(*) = t,   pi_t(v) = (1-t)*pi_v  for v in I,
components  q_* = u,       q_v unchanged        for v in I.
```

The existing components are not smoothed; the adjoined label carries the whole
perturbation. This is a latent for `p_t`: the prior is nonnegative for `t` in
`[0,1]` and has total mass

```text
t + (1-t) * sum_v pi_v = t + (1-t) = 1,
```

and its mixture is

```text
t*u + (1-t) * sum_v pi_v * q_v = t*u + (1-t)*p = p_t.
```

Since `tau(p_t)` is an infimum over finite latents for `p_t`,

```text
tau(p_t) <= score_{p_t}(L_t)   for every t in [0,1].          (6.3)
```

**Lemma 6.4 (the smoothed score is continuous, with the right value at `t=0`).**
The map `t -> score_{p_t}(L_t)` is continuous on `[0,1]`, and

```text
score_{p_0}(L_0) = tau(p).
```

*Proof.* Lemma 6.2 applied to `L_t` gives the exact expression

```text
score_{p_t}(L_t)
  = Psi(p_t) - t*Phi(u) - (1-t) * sum_{v in I} pi_v * Phi(q_v).  (6.4)
```

The sum on the right is a constant: it is computed from the fixed components of
`L*` and does not depend on `t`. The map `t -> p_t` is affine, hence continuous,
and takes values in the closed simplex of laws on `Z`. By Lemma 6.1, `Psi` is
continuous there, being a fixed linear combination of entropies of pushforwards
along the identity and the two projections. So the right-hand side of (6.4) is
continuous in `t` on `[0,1]`.

At `t = 0` we have `p_0 = p`, and `L_0` is exactly `L*` with one extra label of
prior weight `0`. Lemma 6.3 gives `score_{p_0}(L_0) = score_p(L*) = tau(p)`.

### Continuity of the deterministic optimum

**Lemma 6.5 (`T` is continuous on the closed simplex).** The map `p -> T(p)` is
continuous on the closed simplex of laws on `Z`.

*Proof.* Fix a code `g : Z -> Fin(N)`. Expanding the definition
`D_p(g) = I(X;Y | g) + H(g | X) + H(g | Y)` into entropies gives

```text
D_p(g)
  = 2*H(X,g) + 2*H(Y,g) - H(X,Y,g) - H(g) - H(X) - H(Y),
```

a fixed finite linear combination of entropies of pushforwards of `p` along the
fixed maps `(X,g)`, `(Y,g)`, `(X,Y,g)`, `g`, `X`, `Y`. By Lemma 6.1 each term is
continuous in `p`, so `p -> D_p(g)` is continuous.

There are finitely many codes: `N^N` maps from `Z` to `Fin(N)`, so `256` here.
By the blueprint, `T(p)` is the minimum of `D_p(g)` over that finite set. The
minimum of finitely many continuous functions `f_1, ..., f_k` is continuous,
since

```text
| min_i f_i(a) - min_i f_i(b) | <= max_i | f_i(a) - f_i(b) |,
```

and the right-hand side tends to `0` as `b -> a`. Hence `p -> T(p)` is
continuous.

**Lemma 6.6 (limits preserve a one-sided inequality).** Let `F` and `G` be
real-valued functions on `(0,1]` with `F(t) <= G(t)` for all `t`, and suppose
`F(t) -> a` and `G(t) -> b` as `t` decreases to `0`. Then `a <= b`.

*Proof.* Suppose `a > b` and put `eps = (a-b)/2 > 0`. For all small enough `t`
we have `F(t) > a - eps = (a+b)/2` and `G(t) < b + eps = (a+b)/2`, so
`G(t) < F(t)`, contradicting the hypothesis.

### The transfer

**Proposition 6.7 (boundary transfer).** Let `c >= 0`. Suppose

```text
T(p) <= c * tau(p)
```

holds for every full-support law on `Z`. Then it holds for every law on `Z`.

*Proof.* Let `p` be any law on `Z` and build `p_t`, `L*`, and `L_t` as above.
For `t` in `(0,1]` the law `p_t` has full support, so the hypothesis applies:

```text
T(p_t) <= c * tau(p_t).
```

Combining with (6.3), and using `c >= 0` so that multiplying (6.3) by `c`
preserves its direction,

```text
T(p_t) <= c * tau(p_t) <= c * score_{p_t}(L_t)   for t in (0,1].  (6.5)
```

Now let `t` decrease to `0`. On the left, `t -> p_t` is continuous into the
closed simplex and `T` is continuous there by Lemma 6.5, so
`T(p_t) -> T(p_0) = T(p)`. On the right, Lemma 6.4 gives
`c * score_{p_t}(L_t) -> c * tau(p)`. Applying Lemma 6.6 to (6.5),

```text
T(p) <= c * tau(p).
```

Two features of the argument are worth naming. First, it never uses
`tau(p_t) -> tau(p)`, and no such continuity statement is claimed: the only
information used about the perturbed stochastic optimum is the one-sided bound
(6.3), together with the limit of the explicitly constructed comparison score.
Second, the latent `L_t` is written down rather than extracted, so no compact
parameter space, no subsequence, and no limit latent enter. The one existence
input is the attained optimizer `L*` for `p` itself.

Uniformity of `u` is used only to make `p_t` full support for `t > 0`. Any fixed
full-support law would serve, with the adjoined component set equal to it.

### What this gives, and what it does not

Sections 1 to 5 give `W3(L) <= 8*tau(p)` for a selected attained optimizer of a
full-support binary law. The pricing computation of section 7 turns that into
`T(p) <= 9*tau(p)` for the same law; it is a per-law argument, it uses only the
full-support estimate, and it does not depend on this section, so invoking it
here is not circular. Applying Proposition 6.7 with `c = 9` therefore gives

```text
T(p) <= 9*tau(p)
```

for every binary law, including product laws, laws with zero cells, laws with
disconnected support, and laws with `tau(p) = 0`.

For a law that is not full support, that inequality is the whole conclusion.
Three things do not come with it.

1. **No `W3` estimate at the boundary.** The transfer passes through the values
   `T` and `tau` only. It produces no attained optimizer `L` for the sparse law
   `p` with `W3(L) <= 8*tau(p)`, and the `W3` display of the theorem statement is
   not asserted for such `p`.

2. **A deterministic witness exists but is not described.** `T(p)` is a minimum
   over finitely many codes, so some code `g` satisfies
   `D_p(g) = T(p) <= 9*tau(p)`. This argument supplies no selection rule for
   that minimizing code. Section 7 identifies a law-only witness on full
   support; its proof uses the positive chart and does not extend that
   guarantee to a sparse law.

3. **No law-only selector bound.** In particular this section does not prove
   `D_p(g_p) <= 9*tau(p)` for the law-only selector `g_p` of the blueprint.
   Nothing here relates a minimizing code for a sparse `p` to `g_p`, and the
   limit carries no selection rule across. The full-support selector guarantee
   of section 7 supplies no such boundary conclusion.

Finally, the transfer step itself is alphabet-free: Lemmas 6.1 to 6.6 and
Proposition 6.7 use only that the observable alphabets are finite and nonempty.
That does not extend the theorem beyond binary laws, because the full-support
hypothesis it consumes is exactly the binary estimate of sections 1 to 5. The
arbitrary-alphabet statement remains open for the reason recorded in the
blueprint: the estimate it would consume is still a conjecture there.

## 7. Pricing and recovery from the law

Let `p` have full support. The normal form and the two phase bounds provide an
attained optimal latent `L` and a chart-selected code of cost at most
`8*tau(p)`. In the one-component case, use the constant code. In the
two-contact case, transport the chart code back to the observable law.

Catalog recovery supplies a code `g` in the catalog `C(p)` with the same cost.
At balanced prior, the two possible active singletons have equal `W3Cost`,
which allows the catalog's row-major tie rule. The latent remains the selected
optimal quotient throughout this recovery. Thus

```text
score_p(L) = tau(p),
g in C(p),
W3Cost_L(g) <= 8*tau(p).
```

Pricing and minimization over the catalog give

```text
D_p(g_p) <= D_p(g)
         <= score_p(L) + W3Cost_L(g)
         <= 9*tau(p).
```

Every choice defining `g_p` uses only `p`: determine the active checkerboard
from the determinant, isolate its lower-mass endpoint with row-major priority
at a tie, and compare that singleton's deterministic score with the constant
code's. The existence proof uses an optimal latent, but evaluating the
mathematical selector does not require that latent.

For laws with zero cells, section 6 proves `T(p)<=9*tau(p)`. A minimizing
code exists because the canonical code space is finite. This gives the
all-law existential endpoint without a sparse selector guarantee or a sparse
`W3` estimate.

The real-valued selector is defined by classical exact comparisons. The count
and rational implementations still need their refinement proofs before the
verified bound can be asserted for those implementations. The proof uses no
interval certificate and establishes no arbitrary-finite-alphabet bound.
