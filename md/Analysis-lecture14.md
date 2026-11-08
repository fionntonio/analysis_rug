---
title: "Analysis"
author: "Marcello Seri, m.seri@rug.nl, adapted from slides by Alef Sterk"
date: "Lecture 15"
---

Topics:
- Abbott §7.4: properties of integrals
- Abbott §7.5: the fundamental theorem of calculus

Formalization: [`Integration.v`](docs/rocq/RUG.Analysis.Integration.html), [`FTC.v`](docs/rocq/RUG.Analysis.FTC.html)

Tutorial: [Tutorial 14](#tutorials/tutorial-14)

---

## A useful lemma

**Lemma:**
$$
x \leq y + \epsilon \quad\forall\,\epsilon > 0
\quad\Rightarrow\quad
x \leq y
$$

\pause

**Proof:** assume $x > y$

Taking $0 < \epsilon < x-y$ gives
$$
y + \epsilon < y + (x-y) = x
$$
Contradiction!

---

# Properties of integrals

## The split property

**Theorem:** let $f : [a,b] \to \mathbb{R}$ be bounded and $c \in (a,b)$, then
$$
f \text{ integrable on } [a,b]
\quad\Leftrightarrow\quad
f \text{ integrable on } [a,c] \text{ and } [c,b]
$$

In that case
$$
\int_a^b f = \int_a^c f + \int_c^b f
$$

---

## The split property

**Proof ($\Rightarrow$):** let $\epsilon>0$ and pick a partition $P$ of $[a,b]$ s.t.
$$
U(f,P)-L(f,P) < \epsilon
$$

\pause

Let $P_c = P \cup \{c\}$ then
$$
U(f,P_c)-L(f,P_c) < \epsilon
$$

\pause

Then $Q = P_c \cap [a,c]$ is a partition of $[a,c]$ and
$$
m := \# \text{intervals in } Q < n := \# \text{intervals in } P_c
$$

---

## The split property

**Proof ($\Rightarrow$, ctd):** $m < n$ implies
$$\begin{aligned}
U(f,Q) - L(f,Q)
& = \sum_{k=1}^{m} (M_k - m_k)(x_k-x_{k-1}) \\[3mm]
\pause & \leq \sum_{k=1}^{n} (M_k - m_k)(x_k-x_{k-1}) \\[3mm]
\pause & = U(f,P_c) - L(f,P_c) \\[3mm]
& < \epsilon
\end{aligned}$$

Conclusion: $f$ is integrable on $[a,c]$

*Proof for $[c,b]$ is similar*

---

## The split property

**Proof ($\Leftarrow$):** let $P_1$ and $P_2$ be partitions of $[a,c]$ and $[c,b]$ s.t.
$$
U(f,P_i) - L(f,P_i) < \tfrac{1}{2}\epsilon, \qquad i=1,2
$$

\pause

Then $P = P_1 \cup P_2$ is a partition of $[a,b]$ and
$$\begin{aligned}
U(f,P) & = U(f,P_1) + U(f,P_2) \\[3mm]
\pause L(f,P) & = L(f,P_1) + L(f,P_2) \\[3mm]
\pause U(f,P) - L(f,P) & < \tfrac{1}{2}\epsilon + \tfrac{1}{2}\epsilon \;\; = \;\; \epsilon
\end{aligned}$$

Conclusion: $f$ is integrable on $[a,b]$

---

## The split property

**Proof ($\Leftarrow$, ctd):** let $\epsilon$ and $P_1,P_2$ be as before
$$\begin{aligned}
\int_a^b f & \leq U(f,P) \\[3mm]
\pause & < L(f,P) + \epsilon \\[3mm]
\pause & = L(f,P_1) + L(f,P_2) + \epsilon \\[3mm]
\pause & \leq \int_a^c f + \int_c^b f + \epsilon \\[8mm]
\pause \int_a^b f & \leq \int_a^c f + \int_c^b f
\end{aligned}$$

---

## The split property

**Proof ($\Leftarrow$, ctd):** let $\epsilon$ and $P_1,P_2$ be as before
$$\begin{aligned}
\int_a^c f + \int_c^b f
& \leq U(f,P_1) + U(f,P_2) \\[3mm]
\pause & < L(f,P_1) + L(f,P_2) + \epsilon \\[3mm]
\pause & = L(f,P) + \epsilon \\[3mm]
\pause & \leq \int_a^b f + \epsilon \\[8mm]
\pause \int_a^c f + \int_c^b f & \leq \int_a^b f
\end{aligned}$$

---

## The split property

**Definition:** if $f$ is integrable on $[a,b]$ then
$$
\int_a^b f = -\int_b^a f
\qquad\text{and}\qquad
\int_c^c f = 0 \quad\text{for all } c \in [a,b]
$$

**Corollary:** regardless of the order of $a,b,c$ we have
$$
\int_a^b f = \int_a^c f + \int_c^b f
$$

---

## Algebraic properties

**Theorem:** if $f,g$ are integrable on $[a,b]$ then

1. $f+g$ integrable and $\displaystyle\int_a^b (f+g) = \int_a^b f + \int_a^b g$
2. $kf$ integrable and $\displaystyle\int_a^b kf = k\int_a^b f$ for all $k\in\mathbb{R}$

**Proof:** see book

---

## Order properties

**Theorem:** if $f$ is integrable on $[a,b]$ then
$$
m \leq f(x) \leq M \quad\Rightarrow\quad m(b-a) \leq \int_a^b f \leq M(b-a)
$$

\pause

**Proof:** for all partitions $P$ of $[a,b]$
$$
L(f,P) \leq \int_a^b f \leq U(f,P)
$$
\pause Taking $P = \{a,b\}$ gives
$$\begin{aligned}
U(f,P) & = (b-a)\cdot \sup\{f(x)\,:\, x\in[a,b]\} \;\; \leq \;\; M(b-a) \\[3mm]
\pause L(f,P) & = (b-a)\cdot \inf\{f(x)\,:\, x\in[a,b]\} \;\;\; \geq \;\; m(b-a)
\end{aligned}$$

---

## Order properties

**Theorem:** if $f,g$ are integrable on $[a,b]$ then
$$
f(x) \leq g(x) \quad\text{for all } x\in [a,b] \quad\Rightarrow\quad \int_a^b f \leq \int_a^b g
$$

\pause

**Proof:** since $0 \leq g(x) - f(x)$ for all $x \in [a,b]$ we have

$$
0 \cdot (b-a) \leq \int_a^b (g-f)
\Rightarrow 0 \leq \int_a^b g - \int_a^b f
$$

---

## Order properties

**Theorem:** if $f$ is integrable on $[a,b]$ then $|f|$ is integrable and
$$
\left|\int_a^b f\right| \leq \int_a^b |f|
$$

\pause

**Proof:** let $P$ be any partition of $[a,b]$ and
$$\begin{aligned}
M_k   & = \sup\{f(x)\,:\, x\in[x_{k-1},x_k]\} \\[3mm]
m_k   & = \inf\{f(x)\,:\, x\in[x_{k-1},x_k]\} \\[3mm]
\pause M_k' & = \sup\{|f(x)|\,:\, x\in[x_{k-1},x_k]\} \\[3mm]
m_k' & = \inf\{|f(x)|\,:\, x\in[x_{k-1},x_k]\}
\end{aligned}$$

**Claim:** $M_k'-m_k' \leq M_k - m_k$

---

## Order properties

**Proof (ctd):** for all $\epsilon>0$ there exist $y,z \in [x_{k-1},x_k]$ s.t.
$$\begin{aligned}
M_k' - \tfrac{1}{2}\epsilon & < |f(y)| \\[3mm]
m_k' + \tfrac{1}{2}\epsilon & > |f(z)| \\[6mm]
\pause M_k'-m_k' -\epsilon & < |f(y)| - |f(z)| \\[2mm]
\pause & \leq |f(y)-f(z)| \\[2mm]
\pause & \leq M_k - m_k \\[6mm]
\pause M_k'-m_k' & \leq M_k - m_k
\end{aligned}$$

---

## Order properties

**Proof (ctd):** let $P$ be any partition of $[a,b]$ then
$$\begin{aligned}
U(|f|,P) - L(|f|,P)
& = \sum_{k=1}^n (M_k' - m_k')(x_k-x_{k-1}) \\[4mm]
& \leq \sum_{k=1}^n (M_k - m_k)(x_k-x_{k-1}) \\[4mm]
& = U(f,P) - L(f,P)
\end{aligned}$$

Hence, $f$ integrable $\;\Rightarrow\; |f|$ integrable

---

## Order properties

**Proof (ctd):**
$$\begin{aligned}
-|f(x)| \leq f(x) \leq |f(x)| & \Rightarrow -\int_a^b |f| \leq \int_a^b f \leq \int_a^b |f| \\[5mm]
& \Rightarrow \left|\int_a^b f\right| \leq \int_a^b |f|
\end{aligned}$$

---

# Fundamental theorem of calculus

## The fundamental theorem

**Theorem (FTC part 1):** assume that

1. $f$ is integrable on $[a,b]$
2. $F$ is differentiable on $[a,b]$ and
   $$F'(x) = f(x) \qquad\forall\,x \in [a,b]$$

Then
$$
\int_a^b f = F(b) - F(a)
$$

---

## The fundamental theorem

**Proof:** let $P$ be any partition of $[a,b]$
$$\begin{aligned}
F(b)-F(a)
& = \sum_{k=1}^n \big[F(x_k)-F(x_{k-1})\big] \\[1mm]
\pause & \stackrel{\text{MVT}}{=} \sum_{k=1}^n f(t_k)(x_k-x_{k-1}) \qquad t_k \in (x_{k-1},x_k) \\[1mm]
\pause & \leq \sum_{k=1}^n M_k(x_k-x_{k-1}) \\[1mm]
\pause & = U(f,P) \\[5mm]
\pause F(b)-F(a) & \geq L(f,P) \qquad \text{by similar proof}
\end{aligned}$$

---

## The fundamental theorem

**Proof:** let $P$ be any partition of $[a,b]$, then
$$
L(f,P) \leq F(b) - F(a) \leq U(f,P)
$$

\pause

Taking sup/inf over all partitions gives
$$
L(f) \leq F(b) - F(a) \leq U(f)
$$

\pause

Since $f$ is integrable it follows that
$$
L(f) = U(f) = F(b) - F(a)
$$

---

## The fundamental theorem

**Theorem (FTC part 2):** let $f$ be integrable on $[a,b]$ and define
$$
F(x) = \int_a^x f(t)\,dt \qquad\text{where}\quad x \in [a,b]
$$

Then

1. $F$ is uniformly continuous on $[a,b]$
2. if $f$ is **continuous** at $c$, then $F$ is differentiable at $c$ and
   $$F'(c) = f(c)$$

---

## The fundamental theorem

**Proof (1):** since $f$ is integrable on $[a,b]$ there exists $M>0$ s.t.
$$
|f(x)| \leq M \qquad\forall\,x \in [a,b]
$$

\pause

If $x,y \in [a,b]$ with $x \geq y$, then
$$\begin{aligned}
|F(x) - F(y)|
& = \left|\int_y^x f(t)\,dt\right| \\[3mm]
\pause & \leq \int_y^x |f(t)|\,dt \\[3mm]
\pause & \leq M |x-y|
\end{aligned}$$

For given $\epsilon>0$ take $\delta=\epsilon/M$

---

## The fundamental theorem

**Proof (2):** for $x\neq c$ we have

$$\begin{aligned}
\frac{F(x)-F(c)}{x-c}-f(c)
& = \frac{1}{x-c}\int_c^x f(t)\,dt - f(c) \\[7mm]
\pause & = \frac{1}{x-c}\int_c^x f(t)-f(c)\,dt
\end{aligned}$$

---

## The fundamental theorem

**Proof (2):** let $\epsilon>0$ be arbitrary and pick $\delta>0$ s.t.
$$
|x-c| < \delta \quad\Rightarrow\quad |f(x)-f(c)| < \epsilon
$$

\pause

Since $|t-c| \leq |x-c| < \delta$ it follows that
$$\begin{aligned}
\left|\frac{F(x)-F(c)}{x-c}-f(c)\right|
& = \frac{1}{|x-c|}\left|\int_c^x f(t)-f(c)\,dt\right| \\[5mm]
\pause & \leq \frac{1}{|x-c|} \cdot |x-c|\cdot \epsilon \\[5mm]
& = \epsilon
\end{aligned}$$

---

## The fundamental theorem

**Example:** let
$f(x) = \begin{cases} 1 & \text{if } x \neq 1 \\ 0 & \text{if } x = 1 \end{cases}$

$f$ is integrable on $[0,2]$ and define $F(x) = \displaystyle\int_0^x f(t)\,dt$

**Common mistake:** $F'(1) = f(1) = 0$

FTC2 **NOT** applicable because $f$ is not continuous at $x=1$!

---

## The fundamental theorem

**Example (ctd):** write $f(x) = 1 + g(x)$ where
$$
g(x) = \begin{cases} \phantom{-}0 & \text{if } x \neq 1 \\ -1 & \text{if } x = 1 \end{cases}
$$

\pause

**Exercise:** show that $g$ is integrable and
$$
\int_0^x g(t)\,dt = 0 \qquad \forall\,x\in[0,2]
$$

\pause

Hence,
$$
F(x) = \int_0^x 1 + g(t)\,dt = \int_0^x 1\,dt + \int_0^x g(t)\,dt = x
$$

In particular, $F'(1)=1 \neq f(1)$!
