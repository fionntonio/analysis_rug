---
title: "Analysis"
author: "Marcello Seri, m.seri@rug.nl, adapted from slides by Alef Sterk"
date: "Lecture 14"
---

Topics:
- Abbott §7.2: the Riemann integral
- Abbott §7.3: integrals of discontinuous functions

Formalization: [`Integration.v`](docs/rocq/RUG.Analysis.Integration.html)

Tutorial: [Tutorial 13](#tutorials/tutorial-13)

---

# Upper and lower sums

## Partitions

**Definition:** a **partition** of $[a,b]$ is a set of the form
$$
P = \{a = x_0 < x_1 < x_2 < \dots < x_n = b\}
$$

\pause

**Examples:**

$P_1 = \{0, \tfrac{1}{4}, \tfrac{1}{2}, 1\}$ is a partition of $[0,1]$

$P_2 = \{0, 1, 2\}$ is NOT a partition of $[0,1]$

$P_3 = \{0, \tfrac{1}{2}\}$ is NOT a partition of $[0,1]$

---

## Lower sums

Let $f : [a,b]\to\mathbb{R}$ be bounded and $P$ be a partition of $[a,b]$

**Definition:** **lower sum** of $f$ w.r.t. $P$
$$\begin{aligned}
m_k & = \inf\{f(x) \,:\, x \in [x_{k-1},x_k]\} \\[5mm]
L(f,P) & = \sum_{k=1}^n m_k (x_k-x_{k-1})
\end{aligned}$$

"Approximate area below the graph of $f$"

---

## Upper sums

Let $f : [a,b]\to\mathbb{R}$ be bounded and $P$ be a partition of $[a,b]$

**Definition:** **upper sum** of $f$ w.r.t. $P$
$$\begin{aligned}
M_k & = \sup\{f(x) \,:\, x \in [x_{k-1},x_k]\} \\[5mm]
U(f,P) & = \sum_{k=1}^n M_k (x_k-x_{k-1})
\end{aligned}$$

"Approximate area above the graph of $f$"

---

## Approximate areas

![](../fig/lec16-sums.png)

*[Source: Stephen Abbott, *Understanding Analysis*, Springer, 2015]*

$L(f,P) \leq U(f,P)$ for any partition $P$ of $[a,b]$

---

## Refinements

**Definition:** $Q$ is called a **refinement** of $P$ if $P \subseteq Q$

*(Provided that $P$ and $Q$ are partitions of the same interval)*

\pause

**Example:**

$P = \{0, \tfrac{1}{2}, 1\}$ is a partition of $[0,1]$

$Q_1 = \{0, \tfrac{1}{4}, \tfrac{1}{2}, \tfrac{9}{10}, 1\}$ refines $P$

$Q_2 = \{0, \tfrac{1}{2}, 1, 2\}$ does NOT refine $P$

---

## Refinements

**Lemma:** if $P \subseteq Q$ then
$$
L(f,P) \leq L(f,Q)
\quad\text{and}\quad
U(f,P) \geq U(f,Q)
$$

\pause

**Corollary:** if $P \subseteq Q$ then
$$
U(f,Q) - L(f,Q) \leq U(f,P) - L(f,P)
$$

---

## Refinements

![](../fig/lec16-refine.png)

*[Source: Stephen Abbott, *Understanding Analysis*, Springer, 2015]*

---

## Refinements

**Proof (lower sum):** refine $P$ by adding one point $z \in [x_{k-1}, x_k]$
$$\begin{aligned}
m_k   & = \inf\{f(x) \,:\, x \in [x_{k-1},x_k]\} \\[3mm]
\pause m_k'  & = \inf\{f(x) \,:\, x \in [z,x_k]\} \\[3mm]
\pause m_k'' & = \inf\{f(x) \,:\, x \in [x_{k-1},z]\} \\[6mm]
\pause m_k(x_k-x_{k-1}) & = m_k(x_k - z) + m_k (z - x_{k-1}) \\[3mm]
\pause & \leq m_k'(x_k-z) + m_k'' (z-x_{k-1})
\end{aligned}$$

Then proceed by induction

---

## Refinements

**Lemma:** for any two partitions $P_1$ and $P_2$ we have
$$
L(f, P_1) \leq U(f, P_2)
$$

\pause

**Proof:** let $Q = P_1 \cup P_2$ then $P_1, P_2 \subseteq Q$ so
$$
L(f,P_1) \leq L(f,Q) \leq U(f,Q) \leq U(f,P_2)
$$

---

# The Riemann integral

## Best possible approximate area

Assume $f : [a,b] \to \mathbb{R}$ is bounded

Let $\mathcal{P}$ denote the collection of all partitions of $[a,b]$

**Definition:**
$$\begin{aligned}
U(f) & = \inf\{ U(f,P) \,:\, P \in \mathcal{P}\} \\[5mm]
L(f) & = \sup\{ L(f,P) \,:\, P \in \mathcal{P}\}
\end{aligned}$$

---

## Best possible approximate area

**Lemma:** $L(f) \leq U(f)$

\pause

**Proof:**
$$\begin{aligned}
L(f,P_1) & \leq U(f,P_2) \hspace{10mm} \text{for all } P_1, P_2 \in \mathcal{P} \\[3mm]
\pause L(f) & \leq U(f,P_2) \hspace{10mm} \text{for all } P_2 \in \mathcal{P} \text{ (take sup over $P_1$)}\\[3mm]
\pause L(f) & \leq U(f) \hspace{16mm}\text{(take inf over $P_2$)}
\end{aligned}$$

---

## The Riemann integral

**Definition:** a bounded function $f : [a,b] \to \mathbb{R}$ is called **Riemann integrable** if $U(f) = L(f)$

**Notation:**
$$
<<<<<<< HEAD
h(t) = f(t) - s_n(t) - \left(\frac{f(x) - s_n(x)}{x^{n+1}}\right)t^{n+1}
$$

Apply Weierstrass' test:
$$
\sum_{n=0}^\infty M_n \quad\text{conv.}
\quad\Rightarrow\quad
\sum_{n=0}^\infty a_n x^n \quad\text{unif.~conv.~on } [-|c|,|c|]
$$

---

## Recall: preservation of continuity

**Theorem:** assume

1. $\sum_{n=1}^\infty f_n \to f$ uniformly on $A$
2. $f_n$ is continuous on $A$ for all $n$

Then $f$ is continuous on $A$

---

## Continuity of the limit

**Corollary:** $\displaystyle\sum_{n=0}^\infty a_n x^n$ is a continuous function on $(-R,R)$

**Proof:** take $x_0 \in (-R,R)$ and $|x_0| < c < d < R$, then
$$\begin{aligned}
\text{PS convergent at } d
& \Rightarrow  \text{PS absolutely convergent at } c \\[3mm]
& \Rightarrow  \text{PS uniformly convergent on } [-c,c]\\[3mm]
& \Rightarrow  \text{PS continuous on } [-c,c] \\[1mm]
&              \quad\textit{[each term $a_n x^n$ is continuous!]}\\[3mm]
& \Rightarrow  \text{PS continuous at } x_0
\end{aligned}$$

---

## Continuity of the limit

**Corollary:**
$$
\sum_{n=0}^\infty |a_n R^n| \text{ convergent}
\;\;\Rightarrow\;\;
\sum_{n=0}^\infty a_n x^n \text{ uniformly conv.~on } [-R,R]
$$
In particular, the PS is continuous on $[-R,R]$

What if convergence is **conditional** at $x=R$ or $x=-R$?

---

## Abel's theorem

**Theorem:**

1. PS converges at $x=R \;\;\Rightarrow\;\;$ PS conv.~uniformly on $[0,R]$
2. PS converges at $x=-R \;\;\Rightarrow\;\;$ PS conv.~uniformly on $[-R,0]$

_Without proof_

---

# Term-wise differentiation

## Differentiation does not change $R$!

**Theorem:**
$$
\sum_{n=0}^\infty a_n x^n \text{ conv.~on } (-R,R)
\;\;\Rightarrow\;\;
\sum_{n=0}^\infty na_n x^{n-1} \text{ conv.~on } (-R,R)
$$

**Proof:** if $|c|<1$, then there exists $M > 0$ s.t.
$$
|nc^{n-1}| \leq M \quad\forall\,n\in\mathbb{N}
$$

Let $|x| < t < R$, then
$$
|na_n x^{n-1}|
=
\frac{1}{t}\left(n\left|\frac{x}{t}\right|^{n-1}\right)|a_n t^n|
\leq
\frac{M}{t} |a_n t^n|
$$

Apply comparison test

---

## Recall: preservation of differentiability

**Theorem:** assume

1. $f_n : [a,b] \to \mathbb{R}$ is differentiable for all $n$
2. $\sum_{n=1}^\infty f_n' \to g$ uniformly on $[a,b]$
3. $\sum_{n=1}^\infty f_n(x_0)$ converges for some $x_0\in[a,b]$

Then there exists a differentiable $f : [a,b]\to\mathbb{R}$ s.t.
$$
\sum_{n=1}^\infty f_n \to f \quad\text{uniformly}
\qquad\text{and}\qquad
f' = \sum_{n=1}^\infty f_n'
$$

*[Term-wise Differentiability Theorem]*

---

## Differentiation can be done term-by-term!

**Theorem:** for any PS with radius $R$ we have
$$
\bigg(\sum_{n=0}^\infty a_n x^n\bigg)' = \sum_{n=1}^\infty na_n x^{n-1} \qquad \forall\,x \in (-R,R)
$$

**Proof:** let $0 \leq c < R$, then

- $\sum_{n=0}^\infty na_n x^{n-1} \text{ converges uniformly on } [-c,c]$
- $\sum_{n=0}^\infty a_n x^n \text{ converges at } x = 0$

Now apply Term-wise Differentiability Theorem

*[Note: we can apply the theorem any number of times!]*

---

## Differentiation

**Example:** for all $x \in (-1,1)$ we have
$$\begin{aligned}
\sum_{n=1}^\infty \frac{(-1)^{n+1}}{n}x^n & \to f(x) \tag{$*$} \\[3mm]
\sum_{n=1}^\infty (-1)^{n+1}x^{n-1}       & \to \frac{1}{1+x} = f'(x) \;\;\Rightarrow\;\; f(x) = \log|1+x| + C
\end{aligned}$$

Note that:
$$
h(x) = 0
\quad\text{and}\quad
h^{(k)}(0) = 0, \quad k = 0,\dots,n
$$

*If $x<0$, then $c \in (x,0)$*

---

## Lagrange remainder

**Proof (ctd):** the lemma gives $c \in (0,x)$ such that
$$
f^{(n+1)}(c) - \underbrace{s_n^{(n+1)}(c)}_{= \, 0} - (n+1)! \left(\frac{f(x) - s_n(x)}{x^{n+1}}\right) = 0
$$

Rearranging gives
$$
f(x) - s_n(x) = \frac{f^{(n+1)}(c)}{(n+1)!} x^{n+1}
$$

---

## Criterion for integrability

**Theorem:** the following statements are equivalent

1. $f$ is integrable
2. for all $\epsilon>0$ there exists a partition $P_\epsilon$ such that
   $$
   U(f,P_\epsilon) - L(f,P_\epsilon) < \epsilon
   $$

\pause

**Proof ($2 \Rightarrow 1$):**
$$
\left.
\begin{matrix}
U(f) & \leq U(f,P_\epsilon) \\[3mm]
L(f) & \geq L(f,P_\epsilon)
\end{matrix}
\pause \right\}
\quad\Rightarrow\quad
U(f)-L(f) \leq U(f,P_\epsilon) - L(f,P_\epsilon) < \epsilon
$$

This holds for all $\epsilon>0$ so $U(f)=L(f)$

---

## Criterion for integrability

**Proof ($1 \Rightarrow 2$)**: let $\epsilon>0$ and choose $P_1$ and $P_2$ such that
$$
L(f,P_1) > L(f) - \tfrac{1}{2}\epsilon
\quad\text{and}\quad
U(f,P_2) < U(f) + \tfrac{1}{2}\epsilon
$$

\pause

Let $P_\epsilon = P_1 \cup P_2$ then
$$\begin{aligned}
U(f,P_\epsilon) - L(f,P_\epsilon) & \leq U(f,P_2) - L(f,P_1) \\[3mm]
\pause & = \big[U(f, P_2) - U(f)\big] + \big[L(f) - L(f,P_1)\big] \\[3mm]
\pause & < \tfrac{1}{2}\epsilon + \tfrac{1}{2}\epsilon \\[3mm]
& = \epsilon
\end{aligned}$$

---

## Continuous functions are integrable

**Theorem:** $f$ continuous on $[a,b] \;\Rightarrow\; f$ integrable on $[a,b]$

\pause

**Proof:** $f$ is uniformly continuous on $[a,b]$

For all $\epsilon>0$ there exists $\delta>0$ such that
$$
|x-y| < \delta \quad\Rightarrow\quad |f(x)-f(y)| < \frac{\epsilon}{b-a} \qquad\text{for all } x,y \in [a,b]
$$

\pause

Let $P$ be a partition such that $x_k - x_{k-1} < \delta$ for all $k=1,\dots,n$

---

## Continuous functions are integrable

**Proof (ctd):** there exist $y_k, z_k \in [x_{k-1},x_k]$ such that
$$
f(y_k) = M_k
\qquad\text{and}\qquad
f(z_k) = m_k
$$

\pause

Note
$$
|y_k-z_k| < \delta
\quad\Rightarrow\quad
M_k - m_k = f(y_k) - f(z_k) < \frac{\epsilon}{b-a}
$$

---

## Continuous functions are integrable

**Proof (ctd):**
$$\begin{aligned}
U(f,P)-L(f,P) & = \sum_{k=1}^n (M_k-m_k)(x_k - x_{k-1}) \\[4mm]
\pause & < \frac{\epsilon}{b-a}\sum_{k=1}^n (x_k - x_{k-1}) \\[4mm]
\pause & = \frac{\epsilon}{b-a}\cdot (x_n-x_0) \\[4mm]
\pause & = \frac{\epsilon}{b-a}\cdot (b-a) \;\; = \;\; \epsilon
\end{aligned}$$

---

# Integrals of discontinuous functions

## Integrals of discontinuous functions

**Example:** $f(x) = \begin{cases} 1 & \text{if } x\neq 1 \\ 0 & \text{if } x=1\end{cases}$
is integrable on $[0,2]$

\pause

Let $0<\epsilon<1$ and take the partition
$$\begin{aligned}
P & = \{0, 1 - \tfrac{1}{4}\epsilon, 1+\tfrac{1}{4}\epsilon, 2\} \\[3mm]
\pause U(f,P) & = 2 \\[3mm]
\pause L(f,P) & = 2-\tfrac{1}{2}\epsilon \\[3mm]
\pause U(f,P) - L(f, P) & < \epsilon
\end{aligned}$$

*[What if $\epsilon \geq 1$?]*

---

## Integrals of discontinuous functions

![](../fig/lec09-dirichlet.png)

*[Source: Stephen Abbott, *Understanding Analysis*, Springer, 2015]*

**Example:**
$f(x) = \begin{cases} 1 & \text{if } x \in \mathbb{Q} \\ 0 & \text{if } x \notin\mathbb{Q}\end{cases}$
is NOT integrable on $[0,1]$

---

## Integrals of discontinuous functions

Let $P$ be any partition of $[0,1]$ then
$$\begin{aligned}
[x_{k-1},x_k]\cap\mathbb{Q}^c \neq \varnothing
& \Rightarrow m_k=0 \text{ for all } k=1,\dots,n \\[3mm]
& \Rightarrow L(f,P) = 0 \\[6mm]
\pause [x_{k-1},x_k]\cap\mathbb{Q} \neq \varnothing
& \Rightarrow M_k=1 \text{ for all } k=1,\dots,n \\[3mm]
& \Rightarrow U(f,P) = 1
\end{aligned}$$

---

## Integrals of discontinuous functions

**Example:** any **increasing** function $f : [a,b]\to\mathbb{R}$ is integrable

For **any** partition of $[a,b]$ we have
$$\begin{aligned}
M_k & = \sup\{f(x) \,:\, x \in [x_{k-1},x_k]\} \\[2mm]
& = f(x_k) \\[6mm]
\pause m_k & = \inf\{f(x) \,:\, x \in [x_{k-1},x_k]\} \\[2mm]
& = f(x_{k-1})
\end{aligned}$$

---

## Integrals of discontinuous functions

**Example (ctd):** an **equispaced** partition $P$ gives
$$\begin{aligned}
U(f,P) - L(f,P)
& = \sum_{k=1}^n (M_k-m_k)(x_k-x_{k-1}) \\[2mm]
\pause & = \frac{(b-a)}{n} \sum_{k=1}^n \big[f(x_k)-f(x_{k-1})\big] \\[2mm]
\pause & = \frac{(b-a)(f(b)-f(a))}{n} \to 0 \quad\text{ as }\quad n \to \infty
\end{aligned}$$

**Exercise:** show that decreasing functions are also integrable
