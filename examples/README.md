# Binary selector examples

These examples apply the
[selector recipe](../docs/blueprint.md#5-recover-the-code-from-the-law) to
natural count tables. Each table $`q`$ defines the probability law $`p = q\text{/}N`$,
where $`N`$ is its total count. The displayed partitions describe the code on
positive support; labels on zero-mass cells do not affect the partition.

The calculations specify the intended executable behavior. They are not proofs
of the factor-nine bound or of the missing count/rational refinement theorem.

| Case | Normalization | Selected supported partition |
|---|---|---|
| [Product law](#product-law) | $`N = 9`$ | $`\{00,01,10,11\}`$ |
| [Sparse nonproduct law](#sparse-nonproduct-law) | $`N = 3`$ | $`\{00\}`$, $`\{11\}`$ |
| [Sparse endpoint tie](#sparse-endpoint-tie) | $`N = 2`$ | $`\{00\}`$, $`\{11\}`$ |
| [Endpoint-mass tie](#endpoint-mass-tie) | $`N = 20`$ | $`\{00\}`$, $`\{01,10,11\}`$ |
| [Final-score tie](#final-score-tie) | $`N = 20`$ | $`\{00,01,10,11\}`$ |
| [Strict singleton win](#generic-full-support-selection) | $`N = 25`$ | $`\{11\}`$, $`\{00,01,10\}`$ |
| [Negative determinant](#negative-determinant) | $`N = 25`$ | $`\{10\}`$, $`\{00,01,11\}`$ |

## Exact score comparison

For a selected cell, write:

```text
N = total count
Q = selected count
R = selected row count
C = selected column count
S = N - Q
U = R - Q
V = C - Q
```

```math
\begin{aligned}
A &= R^{2R} C^{2C} S^S \\
B &= N^N U^{2U} V^{2V} Q^{3Q}.
\end{aligned}
```

The intended score-key identity is

```math
N\,\log(2)\,(D_p(\mathrm{singleton}) - D_p(\mathrm{constant})) = \log(A\text{/}B).
```

Since $`N > 0`$, the selector chooses the singleton when $`A < B`$ and the
constant when $`B \le A`$. Natural powers use $`0^0 = 1`$. The integer
comparisons below are exact; the public Lean proof of the identity connecting
them to $`D_p`$ is still pending. The
[API contracts](../docs/lean-contracts.md#bin-law-selector) state the missing
refinement endpoints.

## Product law

```math
q = \begin{pmatrix} 1 & 2 \\ 2 & 4 \end{pmatrix}, \qquad p = q\text{/}9.
```

Both checkerboard products equal `4`. The determinant is zero, so the
selector returns the constant partition $`\{00,01,10,11\}`$ without evaluating
a score key. The normalized law is the product of `(1/3, 2/3)` with itself.

## Sparse nonproduct law

```math
q = \begin{pmatrix} 2 & 0 \\ 0 & 1 \end{pmatrix}, \qquad p = q\text{/}3.
```

The diagonal product is `2` and the off-diagonal product is `0`. The lower
diagonal endpoint is cell `11`. For that cell,

```math
\begin{aligned}
(N,Q,R,C,S,U,V) &= (3,1,1,1,2,0,0) \\
A &= 4 \\
B &= 27.
\end{aligned}
```

Since $`A < B`$, the selector chooses the support-canonical singleton. Its
partition $`\{00\}`$, $`\{11\}`$ separates the two positive-mass cells and has
deterministic score zero. Cells `01` and `10` are off support.

### Sparse endpoint tie

```math
q = \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}, \qquad p = q\text{/}2.
```

The diagonal product is `1` and the off-diagonal product is `0`. The
endpoint masses tie, so row-major priority selects `00`. The score keys are

```math
\begin{aligned}
(N,Q,R,C,S,U,V) &= (2,1,1,1,1,0,0) \\
A &= 1 \\
B &= 4.
\end{aligned}
```

The singleton again gives the supported partition $`\{00\}`$, $`\{11\}`$. Here
the constant code has score `1` bit and the singleton has score `0`, so the
singleton wins strictly.

## Endpoint-mass tie

```math
q = \begin{pmatrix} 9 & 1 \\ 1 & 9 \end{pmatrix}, \qquad p = q\text{/}20.
```

The diagonal product is `81` and the off-diagonal product is `1`. The two
diagonal endpoints have equal mass, so row-major priority selects cell `00`.
For that cell,

```math
\begin{aligned}
(N,Q,R,C,S,U,V) &= (20,9,10,10,11,1,1) \\
A &= 10^{40}\,11^{11} \\
B &= 20^{20}\,9^{27} \\
A &< B.
\end{aligned}
```

The selector chooses the singleton at `00`, with partition
$`\{00\}`$, $`\{01,10,11\}`$.

## Final-score tie

```math
q = \begin{pmatrix} 14 & 1 \\ 1 & 4 \end{pmatrix}, \qquad p = q\text{/}20.
```

The diagonal product is `56` and the off-diagonal product is `1`. The lower
diagonal endpoint is cell `11`. For that cell,

```math
\begin{aligned}
(N,Q,R,C,S,U,V) &= (20,4,5,5,16,1,1) \\
A &= 5^{20}\,16^{16} \\
B &= 20^{20}\,4^{12} \\
A &= B = 5^{20}\,2^{64}.
\end{aligned}
```

The deterministic scores tie, so the final rule returns the constant
partition $`\{00,01,10,11\}`$.

## Generic full-support selection

```math
q = \begin{pmatrix} 14 & 1 \\ 1 & 9 \end{pmatrix}, \qquad p = q\text{/}25.
```

The diagonal product is `126` and the off-diagonal product is `1`. Cell `11`
is the lower diagonal endpoint. For that cell,

```math
\begin{aligned}
(N,Q,R,C,S,U,V) &= (25,9,10,10,16,1,1) \\
A &= 10^{40}\,16^{16} \\
B &= 25^{25}\,9^{27} \\
A &< B.
\end{aligned}
```

The selector chooses the singleton at `11`, with partition
$`\{11\}`$, $`\{00,01,10\}`$.

## Negative determinant

```math
q = \begin{pmatrix} 1 & 14 \\ 9 & 1 \end{pmatrix}, \qquad p = q\text{/}25.
```

The diagonal product is `1` and the off-diagonal product is `126`. Thus
$`\Delta < 0`$, and the active pair is $`\{01,10\}`$. Cell `10` has the lower
mass. For that cell,

```math
\begin{aligned}
(N,Q,R,C,S,U,V) &= (25,9,10,10,16,1,1) \\
A &= 10^{40}\,16^{16} \\
B &= 25^{25}\,9^{27} \\
A &< B.
\end{aligned}
```

The selector chooses the singleton at `10`, with partition
$`\{10\}`$, $`\{00,01,11\}`$.
