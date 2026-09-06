# Math rendering test, round two

Throwaway page, round two: workarounds for what round one broke. Not for merge.

Round one found: Markdown backslash escapes are applied inside plain `$...$`
(so `\{`, `\,`, `\%`, `\#`, `\_`, `\\` are eaten), `_` next to punctuation
inside `$...$` is read as emphasis, `\operatorname` is a forbidden macro,
`\tag` renders the whole display stacked vertically, `\label` and `\eqref`
give `???`, and inline `&` fails outright.

## A. Backtick inline form as the escape-proof inline syntax

A1. Emphasis trap: $`\mathrm{score}_p(L) = \Psi(p) - \sum_{v \in I} \pi_v \Phi(q_v)`$ end.

A2. Set braces: $`\{0,1\} \times \{0,1\}`$ and $`\{1, t\}`$ end.

A3. Thin space: $`W_3(L) \le 8\,\tau(p)`$ and $`a \, b \; c`$ end.

A4. Percent and hash: $`50\%`$ and $`x \# y`$ end.

A5. Double backslash inline: $`a \\ b`$ end.

A6. Underscore literal: $`\mathrm{full\_support}`$ and $`x \_ y`$ end.

A7. Tag-like shape, the round-one page killer: $`a<b>c`$ and $`x<y>z`$ end.

A8. Ampersand: $`a \& b`$ end.

A9. In parentheses: ($`\Psi(p)`$) and ( $`\Psi(p)`$ ) end.

A10. Digit right after: $`u_0`$2 end.

A11. Inside italics: *italic $`y`$* and ***both $`z`$*** and **bold $`x`$** end.

A12. In link text: [the cubic $`f_p(u)`$](#a-backtick-inline-form-as-the-escape-proof-inline-syntax) end.

A13. Backtick inside the math, which the form cannot express; skipped.

A14. Adjacent to a code span: `tau_le_score` is $`\tau \le \operatorname{score}`$; expect the operatorname error only.

## B. Plain inline variants for the parentheses and digit cases

B1. ($\Psi(p)$) and ( $\Psi(p)$ ) and [$\Psi(p)$] and "$\Psi(p)$" and '$\Psi(p)$' end.

B2. $\Psi(p)$) and ($\Psi(p)$ end.

B3. Tight lt via macro: $x \lt y$ and $a \lt b \gt c$ end.

B4. Underscore before a letter inside plain dollars, isolated: $D_p(g)$ and $\sum_v \pi_v$ and $q_+$ and $\mathrm{score}_p(L)$ end.

B5. Two underscores in one span, punctuation-adjacent: $\Phi(q)_v + \Phi(q)_w$ end.

## C. Math fences as the escape-proof display syntax

C1. Mid-line double backslash in a matrix:

```math
p = \begin{pmatrix} a & b \\ c & d \end{pmatrix}, \qquad
\begin{bmatrix} 1 & 0 \\ 0 & 1 \end{bmatrix}.
```

C2. Set braces, thin space, percent, hash, underscore:

```math
\{0,1\} \times \{0,1\}, \quad 8\,\tau(p), \quad 50\%, \quad x \# y, \quad \mathrm{full\_support}
```

C3. Aligned with ampersands:

```math
\begin{aligned}
\delta_p(q) &= \Phi(q) - \Phi(p) - \langle \nabla \Phi(p), q - p \rangle \\
&= \sum_z q_z \log_2 \frac{q_z}{p_z} - \text{(marginal terms)}.
\end{aligned}
```

C4. Emphasis trap inside a fence:

```math
\mathrm{score}_p(L) = \Psi(p) - \sum_{v \in I} \pi_v \Phi(q_v)
```

C5. Fence inside a list item:

- item with a fence below:

  ```math
  z_3 = 0
  ```

- next item.

C6. Fence inside a blockquote:

> **Theorem.** Let $`p`$ be a binary law. Then
>
> ```math
> \tau(p) = \Psi(p) - \Phi(q_+).
> ```
>
> The constant latent is optimal when $`\sqrt{ad} \le u_0`$.

C7. Fence in a table cell (probably impossible):

| Case | Content |
|---|---|
| C7 | ```math x = 1 ``` |
| C7b backtick form with escaped pipe | $`H(X \| Y)`$ |
| C7c backtick form with mid | $`H(X \mid Y)`$ |
| C7d plain with escaped pipe | $H(X \| Y)$ |

## D. Equation numbers

D1. Plain number after a blank line following a fence:

```math
f_p(u) = u^3 - v u^2 - w u - w s.
```

(6.1)

D2. Number inside the math with text:

```math
f_p(u) = u^3 - v u^2 - w u - w s. \qquad \text{(6.2)}
```

D3. tag inside a fence, to see whether the vertical stacking recurs:

```math
f_p(u) = u^3 - v u^2 - w u - w s. \tag{6.3}
```

D4. tag star:

```math
f_p(u) = u^3 - v u^2 - w u - w s. \tag*{(6.4)}
```

D5. Number on the closing line of a dollar display:

$$
h(u) = 0. \qquad (6.5)
$$

## E. Macros and operator names

E1. mathrm operator: $`\mathrm{conc}_S \Phi`$ and $`\mathop{\mathrm{conc}}_S \Phi`$ and $`\text{conc}_S \Phi`$ end.

E2. DeclareMathOperator in a fence:

```math
\DeclareMathOperator{\conc}{conc}
\conc_S \Phi(p) \ge \Phi(p)
```

E3. newcommand with an allowed body:

```math
\newcommand{\concS}{\mathrm{conc}_S}
\concS \Phi(p) \ge \Phi(p)
```

E4. The macro from E3 in a later fence:

```math
\concS \Phi(q) = \Phi(q)
```

E5. The macro from E3 inline: $`\concS \Phi`$ and $\concS \Phi$ end.

E6. def in a fence:

```math
\def\PsiP{\Psi(p)} \PsiP
```

E7. Other macros, one per span, to see which are forbidden: $`\href{https://example.org}{x}`$, $`\textbf{x}`$, $`\underset{a}{b}`$, $`\overset{a}{b}`$, $`\stackrel{a}{b}`$, $`\xrightarrow{f}`$, $`\mathbin{\ast}`$, $`\mathrel{R}`$, $`\mathinner{x}`$, $`\phantom{x}y`$, $`\hphantom{x}y`$, $`\smash{x}`$, $`\mathstrut`$, $`\rule{1em}{1pt}`$, $`\unicode{x263A}`$, $`\class{x}{y}`$, $`\style{color:red}{y}`$, $`\cssId{a}{b}`$, $`\require{ams}`$, $`\mathbb{1}`$, $`\mathfrak{g}`$, $`\mathscr{L}`$, $`\varphi \varepsilon \vartheta`$, $`\nabla \partial`$, $`\infty \emptyset`$, $`\mid \nmid`$, $`\cdot \cdots \ldots \vdots \ddots`$, $`\bigl\lvert x \bigr\rvert`$, $`\left\{ x \right\}`$, $`\lVert v \rVert`$ end.

## F. Dollar display line-break reliability

F1. Plain dollar display with an end-of-line double backslash, no environment:

$$
x = 1 \\
y = 2
$$

F2. The same with a trailing space after the double backslash:

$$
x = 1 \\ 
y = 2
$$

F3. Fence version:

```math
x = 1 \\
y = 2
```

## G. Details body

<details open>
<summary>Open details with $`x`$</summary>

Body with $`\tau(p)`$ and a fence:

```math
w = 1
```

</details>

## H. Heading anchors with math

### H1 heading with $`\tau(p)`$ inside

H2. Link to it: [anchor guess one](#h1-heading-with-taup-inside) and [anchor guess two](#h1-heading-with-inside) end.
