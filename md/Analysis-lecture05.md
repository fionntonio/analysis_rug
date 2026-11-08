---
title: "Analysis"
author: "Marcello Seri, m.seri@rug.nl"
date: "Lecture 5"
---

Topics:
- Abbott §3.2. Open and closed sets

Formalization: [`Topology.v`](docs/rocq/RUG.Analysis.Topology.html)

Tutorial: [Tutorial 5](#tutorials/tutorial-5)

---

# Open sets

## Motivation

**Closed interval** (endpoints included):
$$
[a,b] = \big\{x \in \mathbb{R} \,:\, a \leq x \leq b\big\}
$$

**Open interval** (endpoints not included):
$$
(a,b) = \big\{x \in \mathbb{R} \,:\, a < x < b\big\}
$$

How to define open and closed for *arbitrary* sets?

---

## Open sets

**Definition:** $O\subseteq\mathbb{R}$ is **open** if

$$
\forall\,a \in O \quad\exists\,\epsilon>0 \quad\text{s.t.}\quad V_\epsilon(a) \subseteq O
$$

Recall: $V_\epsilon(a) = \{x \in \mathbb{R} \,:\, |x-a|<\epsilon\} = (a-\epsilon,a+\epsilon)$

**Note:** the empty set $\varnothing$ is open by definition

---

## Open sets

**Example:** the interval $(c,d)$ is open

\pause

Take $x\in (c,d)$ arbitrary

\pause

Take $\epsilon=\min\{|x-c|,|x-d|\}$, then $V_\epsilon(x)\subseteq (c,d)$

\pause

**Example:** the interval $[c,d)$ is **NOT** open

For $x=c$ no $\epsilon>0$ works

---

## Open sets

**Example:** $\mathbb{Q}$ is **NOT** open

Take $\epsilon>0$ arbitrary

Take $n \in \mathbb{N}$ such that $\displaystyle\frac{1}{n} < \frac{\epsilon}{\sqrt{2}}$
and set $x = \displaystyle \frac{\sqrt{2}}{n}$

Then $x \in V_\epsilon(0)$ but $x\notin\mathbb{Q}$

---

## Unions and intersections

**Theorem:**

1. Unions of **arbitrary** collections of open sets are open
2. Intersections of **finite** collections of open sets are open

\pause

**Proof (1):** let $O = \bigcup_{i\in I} O_i$ with each $O_i$ open

\pause

$x \in O \;\Rightarrow\; x \in O_i$ for some $i \in I$

\pause

There exists $\epsilon>0$ such that $V_\epsilon(x)\subseteq O_i \subseteq O$

---

## Unions and intersections

**Theorem:**

1. Unions of **arbitrary** collections of open sets are open
2. Intersections of **finite** collections of open sets are open

\pause

**Proof (2):** let $O = O_1 \cap O_2 \cap \dots \cap O_n$ with each $O_i$ open

\pause

$x \in O \;\Rightarrow\; x \in O_i$ for all $i=1,\dots,n$

\pause

For all $i=1,\dots,n$ there exists $\epsilon_i>0$ such that $V_{\epsilon_i}(x)\subseteq O_i$

\pause

For $\epsilon=\min\{\epsilon_1,\dots,\epsilon_n\}$ we have $V_\epsilon(x)\subseteq O_i$ for all $i=1,\dots,n$

---

## Unions and intersections

**Warning:** the intersection of infinitely many open sets **NEED NOT BE** open!

Counter example:
$$\begin{aligned}
O_n &= \left(-\frac{1}{n},\frac{1}{n}\right) \quad\text{is open for all } n\in\mathbb{N} \\[5mm]
\bigcap_{n=1}^\infty O_n &= \{0\} \quad\text{is NOT open}
\end{aligned}$$

---

# Closed sets

## Isolated points

**Definition:** $a \in A$ is an **isolated point** of $A\subseteq\mathbb{R}$ if

$$
\exists\,\epsilon>0 \quad V_\epsilon(a)\cap A = \{a\}
$$

\pause

**Example:** $a=1$ is an isolated point of $A = \displaystyle\left\{\frac{1}{n} \,:\, n\in\mathbb{N}\right\}$

For $0 < \epsilon < \tfrac{1}{2}$ we have $V_\epsilon(1) \cap A = \{1\}$

*[Exercise: show that *all* points of $A$ are isolated]*

---

## Limit points

**Definition:** $x \in \mathbb{R}$ is a **limit point** of $A\subseteq\mathbb{R}$ if

$$
\forall\,\epsilon>0 \quad V_\epsilon(x) \text{ intersects } A \text{ in some point \textbf{other} than } x
$$

**Note:** limit points of $A$ **may** or **may not** belong to $A$!

---

## Limit points

**Example:** $x=0$ is a limit point of
$A = \displaystyle\left\{\frac{1}{n} \,:\, n\in\mathbb{N}\right\}$

\pause

Take $\epsilon>0$ arbitrary

Take $n\in\mathbb{N}$ such that $\displaystyle\frac{1}{n} < \epsilon$

Then $\displaystyle\frac{1}{n} \in V_\epsilon(0) \cap A$

**Note:** $0 \notin A$!

---

## Limit points

**Theorem:** the following statements are equivalent:

1. $x$ is a limit point of $A$
2. There exists a sequence $(a_n)$ in $A$ such that
   $$
   a_n \neq x \quad\forall\,n\in\mathbb{N}\quad\text{and}\quad x = \lim a_n
   $$

\pause

**Proof (1 $\Rightarrow$ 2):** let $n\in\mathbb{N}$ and set $\epsilon=1/n$

There exists $a_n \in V_\epsilon(x) \cap A$ with $a_n \neq x$

Note that $|a_n-x| < \epsilon = \displaystyle\frac{1}{n}$

---

## Limit points

**Theorem:** the following statements are equivalent:

1. $x$ is a limit point of $A$
2. There exists a sequence $(a_n)$ in $A$ such that
   $$
   a_n \neq x \quad\forall\,n\in\mathbb{N}\quad\text{and}\quad x = \lim a_n
   $$

\pause

**Proof (2 $\Rightarrow$ 1):** for all $\epsilon>0$ there exists $N\in\mathbb{N}$ such that
$$
n \geq N \quad\Rightarrow\quad |a_n - x| < \epsilon
$$

In particular, $a_N \in V_\epsilon(x)$

By assumption $a_N \neq x$ and $a_N \in A$

---

## Limit points

**Example:** $x=0$ and $x=1$ are limit points of $A=(0,1)$

For $x=0$ take $a_n = \displaystyle\frac{1}{2n}$

For $x=1$ take $a_n = \displaystyle\frac{n}{n+1}$

**Exercise:** prove the same result by means of the definition

---

## Closed sets

**Definition:** a set is **closed** if it contains its limit points

**Moral:** you can't leave a closed set by taking limits
(see next Theorem)

---

## Closed sets

**Theorem:** the following statements are equivalent:

1. $F$ is closed
2. Every Cauchy sequence in $F$ has its limit in $F$

\pause

**Proof (1 $\Rightarrow$ 2):** let $(a_n)$ be a Cauchy sequence in $F$

$x = \lim a_n$ exists; now consider two cases:

\pause

- $x \neq a_n$ for all $n \in \mathbb{N} \;\Rightarrow\; x$ is a limit point of $F\;\Rightarrow\; x\in F$

  \pause

- $x = a_n$ for some $n \in \mathbb{N} \;\Rightarrow\; x \in F$ holds trivially

---

## Closed sets

**Theorem:** the following statements are equivalent:

1. $F$ is closed
2. Every Cauchy sequence in $F$ has its limit in $F$

**Proof (2 $\Rightarrow$ 1):** let $x$ be a limit point of $F$

\pause

$x = \lim a_n$ with $a_n \in F$ and $a_n \neq x$ for all $n\in\mathbb{N}$

\pause

$(a_n)$ convergent $\;\Rightarrow\;$ $(a_n)$ Cauchy $\;\Rightarrow\;$ $x\in F$ by assumption

---

## Closed sets

**Example:** $[c,d]$ is closed

\pause

Let $x$ be a limit point of $[c,d]$

$x = \lim x_n$ for some sequence $(x_n)\subseteq [c,d]$

$c \leq x_n \leq d$ for all $n\in\mathbb{N}$

Order limit theorem $\;\Rightarrow\; c \leq x \leq d \;\Rightarrow\; x \in [c,d]$

---

## Closure

**Definition:** the **closure** of $A$ is defined as
$$
\overline{A} = A \cup \{\text{all limit points of } A\}
$$

**Theorem:** $\overline{A}$ is closed

\pause

**Proof:** show that
$$
x \text{ limit point of } \overline{A}
\quad\Leftrightarrow\quad
x \text{ limit point of } A
$$

---

## Closure

**Proof ($\Rightarrow$):**

$\overline{A} = A \cup L \quad\text{with}\quad L = \{\text{limit points of } A\}$

\pause

$$\begin{aligned}
x \text{ limit point of $\overline{A}$} &\Rightarrow \forall\,\epsilon>0 \quad \exists\,y \in V_\epsilon(x)\cap\overline{A} \quad y \neq x \\
\pause & \quad \textit{(note: either } y \in A \textit{ or } y \in L\textit{)} \\[3mm]
\pause (1)\quad y \in A &\Rightarrow x \text{ is a limit point of $A$} \\[3mm]
\pause (2)\quad y \in L &\Rightarrow \forall\,\delta>0 \quad \exists\, z \in V_\delta(y) \cap A \quad z \neq y \\
\pause & \quad \textit{(note: } V_\delta(y) \subseteq V_\epsilon(x)\setminus\{x\} \textit{ for } \delta \textit{ small enough)} \\[3mm]
\pause &\Rightarrow x \text{ is a limit point of $A$}
\end{aligned}$$

---

## Closure

**Example:** if $A = (0,1)$ then $\overline{A} = [0,1]$

All points of $A$ are limit points

Also $x=0$ and $x=1$ are limit points

If $x < 0$ or $x > 1$ then $x$ is **NOT** a limit point of $A$ (exercise!)

---

## Closure

**Example:** $\overline{\mathbb{Q}} = \mathbb{R}$

\pause

Take $x \in \mathbb{R}$ and $\epsilon>0$ arbitrary

$\mathbb{Q}$ is dense in $\mathbb{R}$: there exists $r \in \mathbb{Q}$ such that $x < r < x+\epsilon$

Hence, $r \in V_\epsilon(x)\cap\mathbb{Q}$ and $r\neq x$

So each $x\in\mathbb{R}$ is a limit point of $\mathbb{Q}$

---

# Relation open/closed

## Complements

**Theorem:**

1. $O$ open $\Leftrightarrow O^c$ closed
2. $F$ closed $\Leftrightarrow F^c$ open

**Proof:** see book

---

## Open and closed are not mutually exclusive

**Warning:** sets are not like doors!

- $(0,1]$ and $\mathbb{Q}$ are neither open nor closed
- $\mathbb{R}$ and $\varnothing$ are both open and closed

---

## Unions and intersections

**Theorem:**

1. Unions of **finite** collections of closed sets are closed
2. Intersections of **arbitrary** collections of closed sets are closed

\pause

**Proof (1):**
$$\begin{aligned}
F_1,\dots,F_n \text{ closed}
&\Rightarrow F_1^c,\dots,F_n^c \text{ open} \\[3mm]
&\Rightarrow F_1^c\cap\dots\cap F_n^c \text{ open} \\[3mm]
&\Rightarrow (F_1^c\cap\dots\cap F_n^c)^c \text{ closed} \\[3mm]
&\Rightarrow F_1\cup\dots\cup F_n \text{ closed}
\end{aligned}$$

---

## Unions and intersections

**Theorem:**

1. Unions of **finite** collections of closed sets are closed
2. Intersections of **arbitrary** collections of closed sets are closed

\pause

**Proof (2):**
$$\begin{aligned}
F_i \text{ closed for all } i \in I
&\Rightarrow F_i^c \text{ open for all } i \in I \\[2mm]
&\Rightarrow \phantom{\big(}\bigcup_{i\in I} F_i^c \text{ open} \\
&\Rightarrow \big(\bigcup_{i\in I} F_i^c\big)^c \text{ closed} \\
&\Rightarrow \phantom{\big(}\bigcap_{i\in I} F_i \text{ closed}
\end{aligned}$$

---

## Unions and intersections

**Warning:** the union of infinitely many closed sets **NEED NOT BE** closed!

Counter example:
$$\begin{aligned}
F_n &= \left[-\frac{n}{n+1},\frac{n}{n+1}\right] \quad\text{is closed for all } n\in\mathbb{N} \\[5mm]
\bigcup_{n=1}^\infty F_n &= (-1,1) \quad\text{is NOT closed}
\end{aligned}$$
