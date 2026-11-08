---
title: "Analysis"
author: "Marcello Seri, m.seri@rug.nl"
date: "Lecture 4"
---

Topics:
- Abbott §2.6. The Cauchy criterion
- Abbott §2.7. Properties of infinite series

Formalization: [`CauchySequences.v`](docs/rocq/RUG.Analysis.CauchySequences.html), [`Series.v`](docs/rocq/RUG.Analysis.Series.html)

Tutorial: [Tutorial 4](#tutorials/tutorial-4)

---

# Cauchy sequences

## Cauchy sequences

**Definition:** $(a_n)$ **converges** to $a$ if
$$
\forall\,\epsilon>0 \quad\exists\,N \in \mathbb{N} \quad\text{s.t.}\quad
n \geq N \quad\Rightarrow\quad |a_n - a| < \epsilon
$$

**Note:** the limit must be known in advance!

---

## Cauchy sequences

**Definition:** $(a_n)$ is a **Cauchy sequence** if
$$
\forall\,\epsilon>0 \quad\exists\,N \in \mathbb{N} \quad\text{s.t.}\quad
n,m \geq N
\quad\Rightarrow\quad
|a_n - a_m| < \epsilon
$$

**Meaning:** the terms get close to **each other**

---

## Cauchy sequences

**Theorem:** $(a_n)$ convergent $\;\Rightarrow\; (a_n)$ Cauchy

\pause

**Proof:** assume $a = \lim a_n$

For all $\epsilon>0$ there exists $N \in \mathbb{N}$ such that
$$\begin{aligned}
n \geq N    & \quad\Rightarrow\quad |a_n - a| < \tfrac{1}{2}\epsilon \\[6mm]
\pause m, n \geq N & \quad\Rightarrow\quad |a_n - a_m|  = |(a_n - a) - (a_m - a)| \\[3mm]
&                       \hspace{16mm} \leq |a_n-a| + |a_m-a| \\[3mm]
&                       \hspace{16mm} < \epsilon
\end{aligned}$$

---

## Cauchy sequences

**Lemma:** $(a_n)$ Cauchy $\;\Rightarrow\; (a_n)$ bounded

\pause

**Proof:** for $\epsilon=1$ there exists $N \in \mathbb{N}$ such that
$$\begin{aligned}
n,m \geq N & \Rightarrow |a_n - a_m| < 1 \\[1mm]
\pause n \geq N & \Rightarrow |a_n - a_N| < 1 \quad\text{(fix $m = N$)} \\[1mm]
\pause & \Rightarrow \big||a_n|-|a_N|\big| < 1 \\[1mm]
\pause & \Rightarrow |a_n|-|a_N|< 1 \\[1mm]
\pause & \Rightarrow |a_n| < 1 + |a_N|
\end{aligned}$$

\pause

For $M = \max\big\{|a_1|,|a_2|,\dots,|a_{N-1}|, 1+|a_N|\big\}$ we have
$$
|a_n| \leq M \quad\text{for all } n \in \mathbb{N}
$$

---

## Cauchy sequences

**Theorem:** $(a_n)$ Cauchy $\;\Rightarrow\; (a_n)$ convergent

\pause

**Proof:**

Lemma $\;\Rightarrow\;$ $(a_n)$ is bounded

Bolzano--Weierstrass $\;\Rightarrow\;$ $(a_n)$ has a convergent subsequence $(a_{n_k})$,
let $a = \lim a_{n_k}$

---

## Cauchy sequences

**Proof (ctd):** for all $\epsilon>0$ there exists $N\in\mathbb{N}$ s.t.
$$
n,m \geq N \quad\Rightarrow\quad |a_n-a_m|< \tfrac{1}{2}\epsilon
$$

\pause

Fix an index $n_k \geq N$ such that $|a_{n_k} - a| < \tfrac{1}{2}\epsilon$, then
\pause $$\begin{aligned}
n \geq N \quad\Rightarrow\quad |a_n - a| & = |a_n - a_{n_k} + a_{n_k} - a| \\[3mm]
& \leq |a_n-a_{n_k}| + |a_{n_k}-a| \\[3mm]
& < \epsilon
\end{aligned}$$

---

# Series

## Properties of series

**Definitions:**

- infinite **series**: $\displaystyle \sum_{k=1}^\infty a_k = a_1 + a_2 + a_3 + \cdots$
- $n$-th **partial sum**: $s_n = a_1 + a_2 + \dots + a_n$
- **convergence**: $\displaystyle \sum_{k=1}^\infty a_k = A \;\stackrel{\text{def}}{\Longleftrightarrow}\; \lim s_n = A$

---

## Algebraic limit theorem

**Theorem:** if $\sum_{k=1}^\infty a_k = A$ and $\sum_{k=1}^\infty b_k = B$ then

1. $\sum_{k=1}^\infty ca_k = cA$ for all $c\in\mathbb{R}$
2. $\sum_{k=1}^\infty (a_k + b_k) = A+B$

**Proof:** apply analogous theorem for sequences to partial sums

---

## Cauchy criterion

**Theorem:** the following statements are equivalent

1. $\sum_{k=1}^\infty a_k$ converges
2. for all $\epsilon>0$ there exists $N\in\mathbb{N}$ s.t.
   $$
   n > m \geq N \quad\Rightarrow\quad |a_{m+1} + a_{m+2} + \dots + a_n| < \epsilon
   $$

\pause

**Proof:** note that $|s_n-s_m| = |a_{m+1} + \dots + a_n|$

Statement 1 $\;\Leftrightarrow\;$ $(s_n)$ converges $\;\Leftrightarrow\;$ $(s_n)$ Cauchy $\;\Leftrightarrow\;$ Statement 2

---

## Cauchy criterion

**Example:** $\displaystyle \sum_{k=1}^\infty\frac{1}{k}$ diverges

\pause

For any $m \in \mathbb{N}$ and $n = 2m$ we have
$$\begin{aligned}
|a_{m+1} + a_{m+2} + \dots + a_n|
& = \frac{1}{m+1} + \frac{1}{m+2} + \dots + \frac{1}{2m} \\[4mm]
& > \frac{m}{2m} \\[4mm]
& = \frac{1}{2}
\end{aligned}$$
Hence, the Cauchy criterion fails

---

## Necessary condition for convergence

**Theorem:** $\sum_{k=1}^\infty a_k$ converges $\;\Rightarrow\;$ $\lim a_k = 0$

\pause

**Proof:** let $\epsilon>0$ be arbitrary

There exists $N\in \mathbb{N}$ such that
$$\begin{aligned}
n > m \geq N & \quad\Rightarrow\quad |a_{m+1} + a_{m+2} + \dots + a_n|<\epsilon \\[10mm]
n = m+1 \text{ and } m \geq N  & \quad\Rightarrow\quad |a_{m+1}| < \epsilon
\end{aligned}$$

---

## Necessary condition for convergence

**Theorem:** $\sum_{k=1}^\infty a_k$ converges $\;\Rightarrow\;$ $\lim a_k = 0$

**Warning:** the converse is **NOT** true!

Counter example:
$$
\lim \frac{1}{k} = 0
\qquad\text{but}\qquad
\sum_{k=1}^\infty \frac{1}{k}
\quad\text{diverges}
$$

---

## Necessary condition for convergence

**Note:** the previous theorem also gives a **test for divergence**

**Example:** the series
$$
\sum_{k=1}^\infty (-1)^{k+1}\cdot\frac{k+1}{2k} = 1 - \frac{3}{4} + \frac{4}{6} - \frac{5}{8} + \frac{6}{10} - \dots
$$
diverges since **$\lim a_k$ does not exist**

---

## Comparison test

**Theorem:** if $0 \leq a_k \leq b_k$ for all $k\in\mathbb{N}$, then

1. $\sum_{k=1}^\infty b_k$ converges $\;\Rightarrow\;$ $\sum_{k=1}^\infty a_k$ converges
2. $\sum_{k=1}^\infty a_k$ diverges $\;\Rightarrow\;$ $\sum_{k=1}^\infty b_k$ diverges

\pause

**Proof:**
$$\begin{aligned}
|a_{m+1} + a_{m+2} + \dots + a_n| & = a_{m+1} + a_{m+2} + \dots + a_n \\[2mm]
& \leq b_{m+1} + b_{m+2} + \dots + b_n \\[2mm]
& = |b_{m+1} + b_{m+2} + \dots + b_n|
\end{aligned}$$
Apply the Cauchy criterion for series

---

## Comparison test

**Example:** $\displaystyle \sum_{k=1}^\infty \frac{1}{k!}$ converges

\pause

For $k\geq 4$ we have
$$
k! \geq k^2 \quad\Rightarrow\quad \frac{1}{k!} \leq \frac{1}{k^2}
$$

Apply comparison test:
$$
\sum_{k=1}^\infty \frac{1}{k^2} \;\text{ converges}
\quad\Rightarrow\quad
\sum_{k=1}^\infty \frac{1}{k!} \;\text{ converges}
$$

---

## Alternating series test

**Theorem:** assume
- $0 \leq a_{k+1} \leq a_k$ for all $k\in\mathbb{N}$
- $\lim a_k = 0$

then the **alternating series** $\sum_{k=1}^\infty (-1)^{k+1}a_k$ converges

\pause

**Proof:** consider the partial sums
$$
s_n = a_1 - a_2 + a_3 - \dots + (-1)^{n+1}a_n
$$

---

## Alternating series test

**Proof (ctd):** the partial sums form nested intervals:
$$
I_n = [s_{2n}, s_{2n-1}]
\quad\Rightarrow\quad
I_1 \supseteq I_2 \supseteq I_3 \supseteq \cdots
$$

NIP $\;\Rightarrow\;$ there exists $s\in\mathbb{R}$ such that $s \in I_n$ for all $n \in \mathbb{N}$

---

## Alternating series test

**Proof (ctd):** let $\epsilon>0$ be arbitrary

Choose $N \in \mathbb{N}$ such that $a_{2N} < \epsilon$, then
$$\begin{aligned}
n \geq 2N & \Rightarrow s, s_n \in I_N = [s_{2N}, s_{2N-1}] \\[4mm]
\pause & \Rightarrow |s-s_n| \leq s_{2N-1}-s_{2N} \\[4mm]
\pause & \Rightarrow |s-s_n| \leq a_{2N} \\[4mm]
\pause & \Rightarrow |s-s_n| < \epsilon
\end{aligned}$$

---

## Alternating series test

**Example:**
$\displaystyle\sum_{k=1}^\infty \frac{(-1)^{k+1}}{k} = 1 - \frac{1}{2} + \frac{1}{3} - \frac{1}{4} + \cdots$
converges

This follows from the alternating series test:
$$
a_k = \displaystyle\frac{1}{k}
\quad\text{satisfies}\quad
0\leq a_{k+1} \leq a_k
\quad\text{and}\quad
\lim a_k = 0
$$

---

## Absolute vs. conditional convergence

**Theorem:** $\sum_{k=1}^\infty |a_k|$ converges $\;\Rightarrow\;$ $\sum_{k=1}^\infty a_k$ converges

\pause

**Proof:** note that
$$
0 \leq a_k + |a_k| \leq 2|a_k| \quad\text{for all}\quad k \in \mathbb{N}
$$

\pause

Comparison Test $\;\Rightarrow\;$ $\sum_{k=1}^\infty \big(a_k + |a_k|\big)$ converges

\pause

Apply Algebraic Limit Theorem:
$$
\sum_{k=1}^\infty a_k = \sum_{k=1}^\infty \big(a_k + |a_k|\big) - \sum_{k=1}^\infty |a_k|
\quad\text{converges}
$$

---

## Absolute vs. conditional convergence

**Definition:** $\sum_{k=1}^\infty a_k$ is called
- **absolutely convergent** if $\sum_{k=1}^\infty |a_k|$ converges
- **conditionally convergent** if it converges but $\sum_{k=1}^\infty |a_k|$ diverges

\pause

**Examples:**
- $\displaystyle\sum_{k=1}^\infty \frac{(-1)^{k+1}}{k^2}$ converges absolutely
\pause
- $\displaystyle\sum_{k=1}^\infty \frac{(-1)^{k+1}}{k}$ converges conditionally

---

# Special series

## Geometric series

**Definition:** a **geometric series** is of the form
$$
\sum_{k=0}^\infty ar^k = a + ar + ar^2 + ar^3 + \cdots
$$

**Note:** the first index is $k=0$

---

## Geometric series

Partial sums:
$$\begin{aligned}
s_n  & = a + ar + ar^2 + ar^3 + \cdots + ar^{n-1} \\[3mm]
\pause rs_n & = \quad\;\;\; ar + ar^2 + ar^3 + \cdots + ar^{n-1} + ar^n \\[3mm]
\pause (1-r)s_n & = a(1-r^n)
\end{aligned}$$

\pause

For $|r| < 1$ we have:
$$
\lim s_n
=
\lim \frac{a(1-r^n)}{1-r}
=
\frac{a}{1-r}
$$

---

## Geometric series

**Example:** we have $0.999\ldots = 1$

\pause

This follows from
$$\begin{aligned}
0.999\dots
& = \sum_{k=1}^\infty \frac{9}{10^k} \\[2mm]
\pause & = \frac{1}{10} \sum_{k=0}^\infty 9\left(\frac{1}{10}\right)^k \\[2mm]
\pause & = \frac{1}{10}\cdot \frac{9}{1-1/10} \;\; = \;\; 1
\end{aligned}$$

---

## Telescoping series

**Definition:** **telescoping series** are of the form
$$
\sum_{k=1}^\infty a_k = \sum_{k=1}^\infty (b_k - b_{k+1})
$$

\pause

Successive terms cancel each other:
$$\begin{aligned}
s_n & = a_1 + a_2 + a_3 + \cdots + a_n \\[2mm]
& = (b_1 - b_2) + (b_2 - b_3) + (b_3 - b_4) + \cdots + (b_n - b_{n+1}) \\[2mm]
& = b_1 - b_{n+1}
\end{aligned}$$

The series converges $\; \Leftrightarrow \; (b_n)$ converges

---

## Telescoping series

**Example:**
$\displaystyle\sum_{k=1}^\infty \frac{1}{k(k+1)} = \frac{1}{2} + \frac{1}{6} + \frac{1}{12} + \frac{1}{20} + \cdots = 1$

\pause

Solution:
$$\begin{aligned}
s_n & = \sum_{k=1}^n \left(\frac{1}{k} - \frac{1}{k+1}\right) \\[3mm]
\pause & = \left(1 - \frac{1}{2}\right) + \left(\frac{1}{2} - \frac{1}{3}\right) + \cdots + \left(\frac{1}{n} - \frac{1}{n+1}\right) \\[3mm]
& = 1 - \frac{1}{n+1} \to 1
\end{aligned}$$

---

## Telescoping series

**Example:**
$\displaystyle\sum_{k=1}^\infty \frac{1}{k^2+7k+12} = \frac{1}{4}$

\pause

Solution:
$$\begin{aligned}
\frac{1}{k^2+7k+12} & = \frac{1}{(k+3)(k+4)} \;\; = \;\; \frac{1}{k+3} - \frac{1}{k+4} \\[6mm]
\pause s_n & = \left(\frac{1}{4} - \frac{1}{5}\right) + \left(\frac{1}{5} - \frac{1}{6}\right) + \cdots + \left(\frac{1}{n+3} - \frac{1}{n+4}\right) \\[3mm]
& = \frac{1}{4} - \frac{1}{n+4} \to \frac{1}{4}
\end{aligned}$$
