---
title: "Analysis"
author: "Marcello Seri, m.seri@rug.nl"
date: "Lecture 6"
---

Topics:
- Abbott §3.3. Compact sets

Formalization: [`Topology.v`](docs/rocq/RUG.Analysis.Topology.html), [`Compactness.v`](docs/rocq/RUG.Analysis.Compactness.html)

Tutorial: [Tutorial 6](#tutorials/tutorial-6)

---

# Recap: open and closed sets

## Open sets

**Definition:** $O\subseteq\mathbb{R}$ is **open** if

$$
\forall\,a \in O \quad\exists\,\epsilon>0 \quad\text{s.t.}\quad V_\epsilon(a) \subseteq O
$$

Recall: $V_\epsilon(a) = \{x \in \mathbb{R} \,:\, |x-a|<\epsilon\} = (a-\epsilon,a+\epsilon)$

---

## Closed sets

**Definition:** $F\subseteq\mathbb{R}$ is **closed** if $F$ contains its limit points

**Theorem:** the following statements are equivalent:
1. $F$ is closed
2. Every Cauchy sequence in $F$ has its limit in $F$

---

## Relation between open and closed

**Theorem:**
1. $O$ open $\Leftrightarrow O^c$ closed
2. $F$ closed $\Leftrightarrow F^c$ open

**Warning:** sets can be
- neither open nor closed
- both open and closed

---

# Compact sets

## Sequential definition

**Definition:** $K\subseteq\mathbb{R}$ is **compact** if

*every* sequence in $K$ has a convergent subsequence

whose limit is contained in $K$

---

## Sequential definition

**Example:** every finite set is compact

\pause

Let $K = \{a_1,a_2,\dots,a_p\}$

Let $(x_n) \subseteq K$ be arbitrary

Without loss of generality: $x_n = a_1$ for infinitely many $n \in \mathbb{N}$

Take $(x_{n_k})$ such that $x_{n_k} = a_1$ for all $k \in \mathbb{N}$

$\lim x_{n_k} = a_1 \in K$

---

## Sequential definition

**Example:** $[a,b]$ is compact

\pause

Let $(x_n) \subseteq [a,b]$ be arbitrary

$(x_n)$ is bounded

B--W Theorem $\;\Rightarrow\; (x_n)$ has a convergent subsequence $(x_{n_k})$

Let $x = \lim x_{n_k}$

Order Limit Theorem: $a \leq x_{n_k} \leq b$ for all $k \;\Rightarrow\; a \leq x \leq b$

---

## Sequential definition

**Example:** $(0,1]$ is NOT compact

Take $x_n = \displaystyle\frac{1}{n} \in (0,1]$

Every subsequence $(x_{n_k})$ satisfies $\lim x_{n_k} = 0$, but $0 \notin (0,1]$

\pause

**Example:** $\mathbb{R}$ is NOT compact

$x_n = n$ has no convergent subsequence

---

## Characterization of compact sets

**Theorem:** $K\subseteq\mathbb{R}$ compact $\;\Leftrightarrow\; K$ closed and bounded

\pause

**Proof ($\Rightarrow$):**

Assume $K$ is NOT bounded

There exists $(x_n) \subseteq K$ with $|x_n| > n$ for all $n\in\mathbb{N}$

$(x_n)$ has no convergent subsequence

Contradiction!

---

## Characterization of compact sets

**Theorem:** $K\subseteq\mathbb{R}$ compact $\;\Leftrightarrow\; K$ closed and bounded

**Proof ($\Rightarrow$):**

Let $x$ be a limit point of $K$ *[to prove: $x\in K$]*

\pause

There exists $(x_n)\subseteq K$ such that $x = \lim x_n$

\pause

$K$ compact $\;\Rightarrow\;$ there exists a subsequence $(x_{n_k})\to y\in K$

\pause

$(x_{n_k}) \to x$ as well $\;\Rightarrow\;$ $x=y\in K$

---

## Characterization of compact sets

**Theorem:** $K\subseteq\mathbb{R}$ compact $\;\Leftrightarrow\; K$ closed and bounded

**Proof ($\Leftarrow$):**

Let $(x_n) \subseteq K$

$K$ bounded $\;\Rightarrow\; (x_n)$ is bounded

\pause

B--W Theorem $\;\Rightarrow\;$ $(x_n)$ has a convergent subsequence

\pause

Let $x = \lim x_{n_k}$

\pause

$K$ closed $\;\Rightarrow\; x \in K$

---

## Characterization of compact sets

**Example:** every finite set is compact

Let $K = \{a_1,a_2,\dots,a_p\}$

$K$ is bounded:
$$
x \in K \;\Rightarrow\; |x| \leq M = \max\{|a_1|,\dots,|a_p|\}
$$

$K$ is closed: assume that $a_1 < a_2 < \dots < a_p$ then
$$
K^c = (-\infty,a_1)\cup(a_1,a_2)\cup\dots\cup(a_p,\infty) \text{ is open}
$$

---

## Characterization of compact sets

**Example:** $K = \{1/n \,:\, n\in\mathbb{N}\} \cup \{0\}$ is compact

\pause

$K$ is bounded: $|x| \leq 1$ for each $x \in K$

\pause

$K$ is closed:
- if $x < 0$ or $x>0$, then $x$ is not a limit point of $K$ (exercise!)
- $x=0$ is a limit point of $K$ which is contained in $K$

---

## Generalization of the NIP

**Theorem:** assume that $K_n\neq\varnothing$ is compact for all $n \in \mathbb{N}$ and
$$
K_1 \supseteq K_2 \supseteq K_3 \supseteq \cdots
$$
Then $\bigcap_{n=1}^\infty K_n$ is nonempty

**Proof:** see book

---

# Open covers

## Open covers

**Definition:** let $A\subseteq\mathbb{R}$

and assume that the sets $O_\lambda \subseteq \mathbb{R}$, where $\lambda \in \Lambda$, are open

We call the sets $O_\lambda$ an **open cover** for $A$ if
$$
A \subseteq \bigcup_{\lambda \in \Lambda} O_\lambda
$$

**Does every open cover have a finite subcover?**

---

## Open covers

**Example:** possible open covers for $A = (0,1)$:

- $O_1 = (0,\tfrac{1}{2})$ and $O_2 = (\tfrac{1}{3}, 5)$

  \pause

- $O_n = (-\tfrac{n}{10}, \tfrac{n}{10}), \; n \in \mathbb{N}$ has a finite subcover!

  \pause

- $O_a = (\tfrac{1}{a},2), \; a \geq 1$ does **NOT** have a finite subcover!

---

## Characterization of compact sets

**Theorem:** $K$ cpt. $\Leftrightarrow$ any open cover for $K$ has a finite subcover

\pause

**Proof ($\Rightarrow$):**

Let $O_\lambda$, $\lambda \in \Lambda$, be an open cover for $K$ **without** finite subcover

Take a bounded, closed interval $J_1\supseteq K$

\pause

Halving process: construct $J_n$ be closed intervals s.t.
- $J_1 \supseteq J_2 \supseteq J_3 \supseteq \cdots$
- $K\cap J_n$ can **NOT** be covered by finitely many $O_\lambda$'s

*[Note: $\text{Length}(J_n) = \text{Length}(J_1)/2^{n-1} \to 0$]*

---

## Characterization of compact sets

**Theorem:** $K$ cpt. $\Leftrightarrow$ any open cover for $K$ has a finite subcover

**Proof ($\Rightarrow$):**

$K\cap J_n$ compact for all $n\in\mathbb{N} \;\Rightarrow\; \bigcap_{n=1}^\infty (K\cap J_n) \neq \varnothing$

\pause

There exists $x \in K$ such that $x \in J_n$ for all $n$

\pause

$x \in O_\lambda$ for some $\lambda \in \Lambda$ and let $\epsilon>0$ such that $V_\epsilon(x)\subseteq O_\lambda$

\pause

There exists $N \in \mathbb{N}$ such that $\text{length}(J_N) < \epsilon$

\pause

Hence, $K \cap J_N \subseteq J_N \subseteq V_\epsilon(x) \subseteq O_\lambda$. Contradiction!

---

## Characterization of compact sets

**Theorem:** $K$ cpt. $\Leftrightarrow$ any open cover for $K$ has a finite subcover

**Proof ($\Leftarrow$):**

$O_n = (-n,n)$, $n \in \mathbb{N}$, is an open cover for $K$

\pause

$K \subseteq O_1 \cup O_2 \cup \dots \cup O_N = (-N, N)$ for some $N \in \mathbb{N}$

Therefore, $K$ is bounded

---

## Characterization of compact sets

**Theorem:** $K$ cpt. $\Leftrightarrow$ any open cover for $K$ has a finite subcover

**Proof ($\Leftarrow$):**

Let $y$ be a limit point of $K$

There exists $(y_n) \subseteq K$ with $y = \lim y_n$. Assume $y \notin K$

\pause

Let $x \in K$ and $O_x = V_\epsilon(x)$ with $\epsilon = \tfrac{1}{2}|x-y|$

The sets $O_x$, where $x \in K$, form an open cover for $K$

---

## Characterization of compact sets

**Theorem:** $K$ cpt. $\Leftrightarrow$ any open cover for $K$ has a finite subcover

**Proof ($\Leftarrow$):**

There exist $x_1,\dots,x_n \in K$ such that $K \subseteq O_{x_1} \cup \dots \cup O_{x_n}$

\pause

Pick $N \in \mathbb{N}$ such that $|y_N - y| < \min\big\{\tfrac{1}{2}|x_i-y| \,:\, i=1,\dots,n\big\}$

\pause

Hence, $y_N \notin O_{x_1} \cup \dots \cup O_{x_n}$. Contradiction!

---

## Characterization of compact sets

**Theorem (Heine--Borel):** Let $K \subseteq \mathbb{R}$

The following statements are equivalent:
1. $K$ is compact
2. $K$ is closed and bounded
3. Any open cover for $K$ has a finite subcover

---

## Open covers

**Example:** every finite set is compact

Let $K = \{a_1,a_2,\dots,a_p\}$

Let $O_\lambda$, where $\lambda \in \Lambda$, be an open cover for $K$

There exist $\lambda_1,\dots,\lambda_p \in \Lambda$ such that $a_k \in O_{\lambda_k}$

Therefore, $K \subseteq O_{\lambda_1} \cup \dots \cup O_{\lambda_p}$

---

## Open covers

**Example:** $K = \{1/n \,:\, n\in\mathbb{N}\} \cup \{0\}$ is compact

Let $O_\lambda$, where $\lambda \in \Lambda$, be an open cover for $K$

\pause

$0 \in O_{\lambda_0}$ for some $\lambda_0 \in \Lambda$ and $V_\epsilon(0) \subseteq O_{\lambda_0}$ for some $\epsilon > 0$

\pause

Pick $N\in \mathbb{N}$ such that $1/N < \epsilon$

\pause

$1/n \in V_\epsilon(0) \subseteq O_{\lambda_0}$ for all $n \geq N$

\pause

Pick $\lambda_1,\dots,\lambda_{N-1}$ such that $1/n \in O_{\lambda_n}$ for $n < N$
