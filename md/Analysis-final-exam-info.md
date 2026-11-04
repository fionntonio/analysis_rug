---
title: "Information for the final exam"
author: "Marcello Seri / m.seri@rug.nl / adapted from slides by Alef Sterk"
date: "Bonus slides"
---

Topics:
- some tips for the exam

---

## Only show up if you intend to make the exam

Questions and answers will be on Brightspace after grading

Just picking up exam questions is pointless

---

## Structure of the exam

| Problem | Points | | Chapter |
|---|---|---|---|
| Problem 1 | (15 points) | $\leftrightarrow$ | Chapter 1 |
| Problem 2 | (15 points) | $\leftrightarrow$ | Chapter 2 |
| Problem 3 | (15 points) | $\leftrightarrow$ | Chapter 3 |
| Problem 4 | (15 points) | $\leftrightarrow$ | Chapter 4 and 5 |
| Problem 5 | (15 points) | $\leftrightarrow$ | Chapter 5 |
| Problem 6 | (15 points) | $\leftrightarrow$ | Chapter 6 and 7 |

Disclaimer: correspondences are approximate and the number of exercises may differ...

---

## General tips

- White sheets = scrap paper, lined sheets = final work
- Write your name and student number on each page
- Start by reading all questions
  Decide which question you want to do first
- Time management: spend roughly 15 minutes per question
- Formulate answers in a concise manner
  (exam problems do not require 2-page answers)
- Follow the hints when given
- Doing 4 problems well is better than doing 6 problems poorly

---

## Definitions versus theorems/lemma's

**Definition:** $s\in\mathbb{R}$ is called the least upper bound of $A\subseteq\mathbb{R}$ if

- $s$ is an upper bound for $A$
- if $b$ is any upper bound for $A$ then $s \leq b$

**Lemma:** if $s$ is an upper bound for $A$ then

$$
s = \sup A
\quad\Leftrightarrow\quad
\forall\,\epsilon>0 \quad \exists \, a\in A\quad \text{s.t.} \quad s-\epsilon < a
$$

Do not state the *lemma* if we ask for the *definition*!

---

## How to formulate a theorem

Always state both the assumptions and conclusions

**Example:** if $A_1$, $A_2$, and $A_3$ hold (assumptions),
then $C$ holds (conclusion)

**Example:** if $A_1$, $A_2$, and $A_3$ hold (assumptions),
then $C_1$ holds if and only if $C_2$ holds (conclusion)

---

## How to formulate a theorem

**Example:** formulate the Mean Value Theorem

**Wrong:** $\displaystyle \frac{f(b) - f(a)}{b-a} = f'(c)$

**Correct:** if the function $f : [a,b]\to\mathbb{R}$ is continuous on $[a,b]$ and differentiable on $(a,b)$, then there exists $c \in (a,b)$ such that

$$
\frac{f(b) - f(a)}{b-a} = f'(c)
$$

---

## How to refer to a theorem

By its NUMBER (but this is hard to remember)

Either give the NAME (e.g. Mean Value Theorem, Algebraic Continuity Theorem, Order Limit Theorem etc.)

Or formulate the CONTENTS (see previous slide)

When applying a theorem, always check that the conditions are satisfied!

---

## Standard limits

$$\begin{aligned}
\lim_{n\to\infty} \frac{1}{n^p} & = 0 \quad\text{for all}\quad p>0 \\[4mm]
\lim_{n\to\infty} \frac{1}{n!} & = 0  \\[4mm]
\lim_{n\to\infty} \frac{n^k}{n!} & = 0 \quad\text{for all}\quad k>0  \\[4mm]
\lim_{x\to \infty} e^{-x} & = 0\\[4mm]
\lim_{x\to 0} \frac{\sin(x)}{x} & = 1
\end{aligned}$$

---

## Standard functions that are continuous/differentiable

$$\begin{aligned}
& & \text{polynomials} \\[2mm]
& & e^x \\[2mm]
& & \ln(x) \\[2mm]
& &  \sin(x) \\[2mm]
& & \cos(x) \\[2mm]
& & \tan(x) \\[2mm]
& & \arctan(x)
\end{aligned}$$

---

## Use theorems whenever possible

**Example:**
$f(x) = \begin{cases} x e^{-1/x^2} & \text{if } x \neq 0 \\ 0 & \text{if } x = 0 \end{cases}$

Proving that $f$ is continuous on $\mathbb{R}$ by just using the definition is doomed to fail...

Instead do this:
- Prove continuity at $c=0$ by the definition
  (or sequential characterization)
- Use Algebraic Continuity Theorem for $c\neq 0$

---

## Two fundamental inequalities in analysis

Triangle inequality:

$$
\big|x+y\big| \leq \big|x\big| + \big|y\big|
$$

Reverse triangle inequality:

$$
\big||x|-|y|\big| \leq \big|x-y\big|
$$

---

## Induction is not always needed

**Example:** for all $n\in\mathbb{N}$ we have
$\displaystyle\sum_{k=1}^n\frac{1}{k(k+1)} = \frac{n}{n+1}$

Induction is just one possibility...

But it can be done quicker:

$$
\sum_{k=1}^n\frac{1}{k(k+1)}
=
\sum_{k=1}^n \left(\frac{1}{k} - \frac{1}{k+1}\right)
=
1-\frac{1}{n+1} = \frac{n}{n+1}
$$

---

## Two ways to prove continuity at a point

1. **Definition:** $f : I \to \mathbb{R}$ is continuous at $c$ if and only if

   $$
   \forall\,\epsilon>0 \quad\exists\,\delta>0 \quad\text{such that}\quad |x-c|<\delta \;\;\Rightarrow\;\; |f(x)-f(c)|<\epsilon
   $$

2. **Theorem:** $f : I \to \mathbb{R}$ is continuous at $c$ if and only if

   $$
   \lim f(x_n) = f(c)
   \quad\text{for all sequences } (x_n) \quad\text{such that}\quad \lim x_n = c
   $$

The easiest method can vary from situation to situation!

---

## Three ways to prove compactness of a set

1. Definition
2. Closed and bounded
3. Every open cover has a finite subcover

The easiest method can vary from situation to situation!
