---
layout: page
title: Induction
nav_order: 3
has_children: false
has_toc: false
parent: Induction 
grand_parent: Notes
---

## Recursion for proofs 

We revert to using $0$ for zero and $n+1$ for $s(n)$. 

Recursion allows us to build functions with domain $\mathbb{N}$ 
by knowing 
- $f(0)$ and 
- $f(n+1)$ given $f(n)$ 

_Induction_ allows us to construct proofs in a similar fashion. 

**Theorem** (Principle of Induction). Let $P(n)$ be a predicate 
on $n \in \mathbb{N}$. Assume that 
- We have a proof of $P(0)$ and 
- Given any $n$, we can prove $P(n) \to P(n+1)$

Then we can prove $\forall n,~ P(n)$.

{% proof %}
Let 
$$
X = \lbrace n \in \mathbb{N} \mid P(n) \rbrace 
$$
In other words, $X$ is the subset of $\mathbb{N}$ consisting 
exactly of the $n \in \mathbb{N}$ where we can prove $P(n)$. 

Then $0 \in X$ and if $n \in X$, we have $n+1 \in X$. From 
the final axiom for $\mathbb{N}$, we have $\mathbb{N} = X$. 
In other words, we can prove $P(n)$ for all $n$. 
{% endproof %}

The _base case_ of induction is the proof of $P(0)$ and 
the _induction step_ is the proof of $\forall~ n, P(n) \to 
P(n+1)$. 

Here is a proof in Lean. 
{% highlight lean %}
theorem induction {P : Nat → Prop} (base : P 0) 
  (ind : ∀ n, P n → P (n+1)) (m : Nat) : P m := 
    match m with 
    | 0 => base 
    | n+1 => ind n (induction base ind n)  
{% endhighlight %}

We use recursion to use the proof for `n` given by 
`induction base ind n` to handle the induction step. 

**Example**. Let's prove that 
$$
\sum_{i=0}^n i = \frac{n(n+1)}{2} 
$$
for all $n$. 

To apply induction, we need to prove two things: 
- Base case: the statement is true for $n=0$
- Induction step: if the statement is true for $n$, then 
it is also true for $n+1$. 

Once we do this, we can apply to induction and conclude 
that the statement is true for all $n$. 

We treat the base case: $n=0$. Then the left-hand side is 
$$
\sum_{i=0}^0 i = 0 
$$
and the right-hand side is 
$$
\frac{0 \cdot 1}{2} = 0 
$$
which are equal. 

Next we do the induction step. Assume we know that 
$$
\sum_{i=0}^n i = \frac{n(n+1)}{2} 
$$
We want to show that 
$$
\sum_{i=0}^{n+1} i = \frac{(n+1)(n+2)}{2}
$$
We note that 
$$
\sum_{i=0}^{n+1} i = \sum_{i=0}^n i + (n+1) 
$$
Using the induction hypothesis, we have 
$$
\sum_{i=0}^{n+1} i = \frac{n(n+1)}{2} + (n+1) 
$$
Getting a common denominator and simplifyin we get 
$$
\frac{n(n+1)}{2} + (n+1) = \frac{n(n+1) + 2(n + 1)}{2} = 
\frac{(n+1)(n+2)}{2} 
$$
which finishes the induction step. Appealing to induction, we 
can conclude that 
$$
\sum_{i=0}^n i = \frac{n(n+1)}{2}
$$
for all $n$.

Let's see how this looks in Lean.
{% highlight lean %}
-- We import results on Nat beyond those in Lean core
import Std.Data.Nat.Lemmas 

-- Here is a recursive definition of our sum
def LinearSum (n : Nat) : Nat := 
  match n with 
  | 0 => 0 
  | n+1 => n+1 + LinearSum n 

theorem linear_sum (n : Nat) : LinearSum n = n*(n+1) / 2 := by 
  -- We first show it suffices to prove the result with 
  -- denominators cleared 
  suffices h : 2*(LinearSum n) = n*(n+1) by  
    rw [←h,Nat.mul_comm]
    -- The simplifier simp can often help where rw doesn't
    let h : 0 < 2 := by simp 
    exact Eq.symm (Nat.mul_div_cancel (LinearSum n) h) 
  -- Now our goal is 2*(LinearSum n) = n*(n+1) and 
  -- we can use the induction tactic to prove it 
  induction n with 
  -- We handle the base case
  | zero => rw [Nat.zero_mul]; rfl 
  -- We then do the induction step where  
  -- hn : 2 * LinearSum n = n * (n + 1) and our 
  -- goal is 2 * LinearSum (Nat.succ n) = 
  -- Nat.succ n *  (Nat.succ n + 1)
  | succ n hn => 
    conv => lhs; simp [LinearSum] 
    rw [Nat.mul_add,hn,←Nat.add_mul] 
    conv => lhs; rw [Nat.mul_comm,Nat.add_comm 2 n]
{% endhighlight %}

We have the following variant of induction where the base case 
does not have to be zero. 

**Corollary**. Let $P(n)$ be a predicate on $n \in \mathbb{N}$ 
and $n_0 \in \mathbb{N}$. Assume that 
- we have a proof of $P(n_0)$ and 
- for any $n \geq n_0$, we can prove $P(n) \to P(n+1)$. 

Then we can prove $\forall n \geq n_0, P(n)$. In other words, $P(n)$ 
is true for all $n \geq n_0$. 

{% proof %}
Set $Q(n) := P(n+n_0)$. Then our conditions translate into $Q(0)$ is 
true and $Q(n) \to Q(n+1)$ is true for all $n$. Using induction, 
we conclude that $Q(n)$ is true for all $n$. But then $P(n+n_0)$ is 
true for all $n$ or $P(n)$ is true $n \geq n_0$. 
{% endproof %}

**Example**. For all $n \geq 3$, we have $3n \leq n^2$. 

Note that while the conlusion is true for $n=0$ it is defintely not true to $n
= 1,2$. 

We start with the base case of $n_0 = 3$. The left-hand side is 
$ 3 \cdot 3 = 9$ as is the right hand side. Thus the base case is 
true.

Now we assume $n \geq 3$ and that $3n \leq n^2$ and try to show that $3(n+1)
\leq (n+1)^2$. 
We can expand the right-hand side as $(n+1)^2 = n^2 + 2n + 1$ and the left-hand 
side as $3n + 3$. From the induction hypothesis, we know that $3n \leq n^2$. 
Thus, 
$$
3(n+1) = 3n + 3 \leq n^2 + 3 
$$
Now if $3 \leq 2n + 1$ we get 
$$
3(n+1) \leq n^2 + 3 \leq n^2 + 2n + 1 = (n+1)^2
$$
and get our desired conclusion. 

We need to prove that $3 \leq 2n + 1$ for all $n \geq 3$. To do this, we 
use induction! The base case is $n = 3$ where the right-hand side is $7$ 
which is greater than $3$. Assume that $3 \leq 2n + 1$. Then 
$$
3 \leq 2n + 1 \leq 2n + 1 + 2 = 2(n+1) + 1 
$$
Appealing to induction, we can conclude $3n \leq n^2$ for all $n \geq 3$. 
