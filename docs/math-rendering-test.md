# Math rendering test

Throwaway page. It exists only to see which LaTeX constructs GitHub's
Markdown math renderer handles, before any documentation page is converted.
Every numbered case names what it tests. Not for merge.

## 1. Delimiters

1a. Inline dollars: $\tau(p) \le T(p) \le I_p(X;Y)$ in running text.

1b. Inline backtick form: $`\tau(p) \le T(p) \le I_p(X;Y)`$ in running text.

1c. Display with two dollars:

$$
f_p(u) = u^3 - v u^2 - w u - w s.
$$

1d. Math fence:

```math
f_p(u) = u^3 - v u^2 - w u - w s.
```

1e. Display with the delimiters on the same lines as the content: $$\Psi(p) = H(X \mid Y) + H(Y \mid X)$$ done.

## 2. Adjacent characters

2a. Punctuation after math: $\tau(p)$, then $\Phi(q)$. Then ($\Psi(p)$) in parentheses.

2b. Hyphenated: a $\tau$-optimal latent; the $2 \times 2$ case.

2c. Digit right after: $u_0$2 and $u_0$ 2.

2d. Math at line start:
$x$ first on its line.

2e. Math next to a code span: `tau_le_score` and $\tau$ on one line; also $\tau$ then `tau`.

2f. Code span containing a dollar on the same line as inline math: `$5` and $x^2$.

2g. Literal dollar outside math: costs <span>$</span>5, and escaped \$5, and a bare $5 with no closing.

2h. Two inline spans with underscores on one line, the classic italics trap: $p_{01}$ and $p_{10}$ and $a_1 b_2$.

2i. Asterisks: $a * b$ and $c * d$ on one line.

## 3. Comparison signs and HTML-like shapes

3a. Spaced: $x < y$ and $y > x$.

3b. Tight: $x<y$ and $y>x$.

3c. Tag-like: $a<b>c$ and $x<y>z$.

3d. Angle brackets: $\langle c, x \rangle$.

3e. Ampersand outside an environment: $a \& b$ and $a & b$.

## 4. Tables

| Case | Content | Expected |
|---|---|---|
| 4a raw pipe | $H(X|Y)$ | probably splits the cell |
| 4b mid | $H(X \mid Y)$ | should render |
| 4c vert | $H(X \vert Y)$ | should render |
| 4d escaped pipe | $H(X \| Y)$ | unknown |
| 4e backtick form | $`H(X|Y)`$ | should protect the pipe |
| 4f absolute value | $\lvert x \rvert$ and $\|x\|$ | unknown |
| 4g display in cell | $$\tau(p) = \Psi(p) - \Phi(q_+)$$ | unknown |
| 4h code span with pipe | `H(X\|Y)` | escaped pipe in code |

## 5. Environments

5a. aligned:

$$
\begin{aligned}
\delta_p(q) &= \Phi(q) - \Phi(p) - \langle \nabla \Phi(p), q - p \rangle \\
&= \sum_z q_z \log_2 \frac{q_z}{p_z} - \text{(marginal terms)}.
\end{aligned}
$$

5b. align (numbered, usually unsupported inside dollars):

$$
\begin{align}
a &= b \\
c &= d
\end{align}
$$

5c. cases:

$$
\tau(p) =
\begin{cases}
I_p(X;Y) & \text{if } \sqrt{ad} \le u_0, \\
\Psi(p) - \Phi(q_+) & \text{otherwise.}
\end{cases}
$$

5d. pmatrix and bmatrix:

$$
p = \begin{pmatrix} a & b \\ c & d \end{pmatrix}, \qquad
\begin{bmatrix} 1 & 0 \\ 0 & 1 \end{bmatrix}.
$$

5e. gathered and line breaks without an environment:

$$
\begin{gathered}
x = 1 \\
y = 2
\end{gathered}
$$

$$
x = 1 \\
y = 2
$$

5f. array:

$$
\begin{array}{c|c}
a & b \\
\hline
c & d
\end{array}
$$

## 6. Numbering and references

6a. tag:

$$
f_p(u) = u^3 - v u^2 - w u - w s. \tag{6.1}
$$

6b. label and eqref (probably unsupported): see $\eqref{eq:cubic}$ and $\ref{eq:cubic}$.

$$
g(u) = 0. \label{eq:cubic}
$$

6c. Plain trailing number, the fallback convention:

$$
h(u) = 0.
$$
(6.3)

## 7. Macros

7a. newcommand defined and used in one block:

$$
\newcommand{\conc}{\operatorname{conc}}
\conc_S \Phi(p) \ge \Phi(p)
$$

7b. Used again in a later block on the same page (tests whether macros persist):

$$
\conc_S \Phi(q) = \Phi(q)
$$

7c. Used inline: $\conc_S \Phi$.

7d. def form: $$\def\PsiP{\Psi(p)} \PsiP$$ and later $\PsiP$.

## 8. Commands used by the pages

8a. $\operatorname{score}_p(L) = \Psi(p) - \sum_{v \in I} \pi_v \Phi(q_v)$.

8b. $D_p(g) = I(X;Y \mid g) + H(g \mid X) + H(g \mid Y)$.

8c. $W_3(L) \le 8\,\tau(p)$, $T(p) \le 9\,\tau(p)$.

8d. Set braces: $\{0,1\} \times \{0,1\}$ and $\{1, t\}$; grouping braces $2^{h_j}$, $q_{v}$.

8e. Roots and fractions: $\sqrt{ad} \le u_0$, $\rho = \sqrt{s^2 - 4u_0^2}$, $\lambda = \frac{a - (s - \rho)/2}{\rho}$, $\dfrac{1}{Q^3}$, $\tfrac{1}{2}$.

8f. Operators: $\min_g D_p(g)$, $\inf_L$, $\lim_{t \to 0}$, $\prod_{i=1}^n$, $\log_2$, $\ln$, $\exp$, $\det q$, $\operatorname{conc}_S \Phi$.

8g. Sizing: $\left( \frac{a}{b} \right)$, $\bigl( x \bigr)$, $\Bigl[ y \Bigr]$, $\lfloor x \rfloor$, $\lceil x \rceil$.

8h. Text and spacing: $x \text{ for all } y$, $\mathrm{d}x$, $\mathbb{R}$, $\mathcal{L}$, $\mathbf{v}$, $a \, b \; c \quad d \qquad e$.

8i. Relations and arrows: $\le \ge \ne \equiv \approx \subseteq \in \notin \to \mapsto \Rightarrow \iff$.

8j. Unicode in math: $τ(p) ≤ T(p)$ and $α, β$.

8k. Binomials and substack: $\binom{n}{k}$, $\sum_{\substack{i \in I \\ i \ne j}} x_i$.

8l. Accents and primes: $\hat{q}$, $\bar{p}$, $\tilde{u}$, $q'$, $q''$, $\dot{x}$.

8m. Color and boxed (often disabled): $\boxed{x}$, $\color{red}{y}$.

8n. Long inline that wraps across the source line break: $\Psi(p) - \Phi(q_+) = H(X \mid Y) + H(Y \mid X) - 3H(q_+) + 2H(X_{q_+}) + 2H(Y_{q_+})$
continued on the next source line inside the same paragraph.

## 9. Placement

9a. In a heading: see the next heading.

### 9a heading with $\tau(p)$ inside

9b. In link text: [the cubic $f_p(u)$](#5-environments) and [plain link](#5-environments).

9c. In a list:
- item with $x_1$
- item with $$y_2$$ display attempt
- item with a display below:

  $$
  z_3 = 0
  $$

9d. In a blockquote, the theorem shape the pages use:

> **Theorem.** Let $p$ be a binary law with $\Delta = ad - bc > 0$. Then
>
> $$
> \tau(p) = \Psi(p) - \Phi(q_+).
> $$
>
> The constant latent is optimal when $\sqrt{ad} \le u_0$.

9e. In bold and italics: **bold $x$** and *italic $y$* and ***both $z$***.

9f. In a footnote-like HTML detail block:

<details>
<summary>Summary with $x$</summary>

Body with $\tau(p)$ and a display:

$$
w = 1
$$

</details>

9g. Display with a blank line inside (probably breaks):

$$
a = 1

b = 2
$$

9h. Display indented four spaces (code block trap):

    $$
    c = 3
    $$

9i. Inline math split across a blank line (should not render): $a

b$ end.

## 10. Escapes and specials

10a. Percent: $50\%$ and $50 \%$.

10b. Hash: $\#$ and $x \# y$.

10c. Backslash-backslash inside inline: $a \\ b$.

10d. Braces escaped: $\{ \}$ and $\lbrace \rbrace$.

10e. Tilde and caret: $\sim$, $\hat{}$, $x \tilde{} y$.

10f. Underscore literal: $x \_ y$ and $\mathrm{full\_support}$.

10g. Trailing backslash-space: $a\ b$.

10h. Double dollar inline on one line: $$e = mc^2$$ mid sentence.
