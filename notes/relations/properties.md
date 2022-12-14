---
layout: page
title: Useful properties
nav_order: 2
has_children: false
has_toc: false
parent: Relations 
grand_parent: Notes
---

## Properties of relations

Looking at the examples from [before]({% link notes/relations/basic.md %}), 
we can identify some useful properties can satisfy. 

**Definition**. Let $\sim$ be a relation. 
We say that $\sim$ is _reflexive_ if 
$$
\forall~ x, x \sim x 
$$
In other words, every $x$ is related to itself. If $R_\sim$ is the 
subset corresponding to $\sim$, then reflexivity is equivalent to 
$$
\Delta_U \subseteq R_\sim
$$
We say that $\sim$ is _irreflexive_
$$
\forall~ x, x \not \sim x
$$

Equality is reflexive as is divisibility. But $ < $ is irreflexive. 

**Definition**. Let $\sim$ be a relation. 
We say that $\sim$ is _symmetric_ if 
$$
\forall~ x,y, x \sim y \to y \sim x  
$$
In other words, if $x$ is related to $y$, then $y$ is also related to $x$.

We say that $\sim$ is _antisymmetric_ if 
$$
\forall~ x,y, x \sim y \to y \sim x \to x=y
$$
So if both $x$ is related $y$ and $y$ is related to $x$, then in fact 
they have to be equal.

We say that $\sim$ is _asymmetric_ if 
$$
\forall~ x,y, x \sim y \to x \not \sim y 
$$

Again equality is symmetric but divisibility. 
Both $ \leq $ and $\subseteq$ are examples of antisymmetric relations. 
Strict less than $ < $ is asymmetric. 

Note that any relation that is symmetric and antisymmetric is very close to 
equality. In particular if $x \sim y$ then we must have $x = y$. 

**Definition**. Let $\sim$ be a relation. We say that $\sim$ is 
_transitive_ if 
$$
\forall~ x,y,z, x \sim y \to y \sim z \to x \sim z
$$
In other words, if $x$ is related to $y$ and $y$ is related to $z$, then 
we know that $x$ is related to $z$. 

Equality, divisibility, and $ < $ are all transitive. 

**Definition**. We say that $\sim$ is _total_ if 
$$
\forall~ x,y, x \sim y \lor y \sim x
$$
Total relations are ones where we can compare every pair, one way 
or another.

So $=$ and $\subseteq$ are rarely total but $\leq$ is total. 

These notions are interrelate. Assuming some can imply others or their 
negations. For example, 

**Lemma**. If a relation is total, then it is reflexive. 

{% proof %}
Assume $\sim$ is a total relation. 
Since $\sim$ is total, we know that either $x \sim x$ or $x \sim x$ for 
any $x$. But either branch is exactly what we want. 
{% endproof %}

This looks like 
{% highlight lean %}
theorem total_refl { R : ?? ??? ?? ??? Prop } (h : Total R) : 
  Reflexive R := fun a => eq_or (h a a) where 
    eq_or {P : Prop} (h : P ??? P) : P := by cases h; repeat assumption 
{% endhighlight %}
in Lean. A `where` keyword allows you to introduce unknown results and 
use them if you provide their definition and proof after the where 
statement. 

Let's look at some specific properties of division. Recall that, for two 
natural numbers (or integers) $n$ and $m$, $n \mid m$ means there exists 
some $c \in \mathbb{N}$ (or $\mathbb{Z}$) with $m = cn$.

Let's show that this is reflexive, anti-symmetric, and transitive. 
{% highlight lean %}
def Divides (a b : Nat) : Prop := ??? c, b = c*a 
infix:60 " | " => Divides

theorem div_refl : Reflexive Divides := by
  -- take some number a 
  intro a 
  -- we know that a = 1*a 
  have : a = 1*a := Eq.symm (Nat.one_mul a)
  -- exists takes the witness and looks for the proof in 
  -- the context to close the goal 
  exists 1

theorem div_antisym : AntiSymmetric Divides := by
  -- take two numbers a and b and assume that a | b and b | a
  intro a b h??? h??? 
  -- extract the multiples and proofs of equality 
  have ???c???,h?????? := h??? 
  have ???c???,h?????? := h??? 
  -- we break it into the case where a = 0 and a ??? 0
  by_cases h : a = 0
  -- we can write h??? : b = c??? * a using a = 0 to get b = 0 
  ?? rw [h,Nat.mul_zero,???h] at h??? 
    exact Eq.symm h??? 
  -- we use basic facts about natural numbers to show that 
  -- c??? and c??? are both 1
  ?? rw [h???,???Nat.mul_assoc,Nat.mul_comm] at h??? 
    conv at h??? => lhs ; rw [???Nat.mul_one a] 
    have : 1 = c??? * c??? := Nat.mul_nonzero_cancel h h???
    have : c??? = 1 := (Nat.prod_eq_one (Eq.symm this)).right 
    rw [this,Nat.one_mul a] at h??? 
    exact Eq.symm h??? 

theorem div_trans : Transitive Divides := by 
  -- we have a,b,c with a | b and b | c
  intro a b c h??? h??? 
  -- we extract the witnesses 
  have ???d???,h?????? := h??? 
  have ???d???,h?????? := h??? 
  -- we get c = (d???*d???)*a 
  rw [h???,???Nat.mul_assoc] at h??? 
  exists d???*d??? 
{% endhighlight %}

We can find facts about $\mathbb{N}$ in the namespace `Nat` and 
we will see how $\mathbb{N}$ is defined and how facts like these 
are proven soon. (In fact, some of these results don't exist at 
the moment ????.) 

**Example**. Let's take the set $\lbrace 0,1,2 \rbrace$ and 
construct relations satisfying some, and not other, properties 
above. 
- $R = \varnothing$ is irreflexive, symmetric, antisymmetric, asymmetric, and transitive. 
It is not reflexive or total. 
- $R = \lbrace (0,0) \rbrace$. This is symmetric, 
antisymmetric, and transitive. It is not reflexive, irreflexive, asymmetric, 
or total.
- $R = \lbrace (0,1), (1,0) \rbrace$. This is irreflexive and symmetric. 
It is not reflexive, irreflexive, antisymmetric, asymmetric, transitive, 
or total.
- $R = \lbrace (0,1), (1,2) \rbrace$. This is irreflexive, antisymmetric, 
and asymmetric. It is not reflexive, symmetric, transitive, or total.
- $R = \lbrace (0,1), (1,2), (2,0) \rbrace$ is irreflexive, antisymmetric, 
asymmetric, and total. It is not reflexive, symmetric, or transitive. 
- $R = \lbrace (0,0), (0,1), (1,2), (2,0) \rbrace$ is antisymmetric but is 
not reflexive, irreflexive, symmetric, asymmetric, transitive, or total. 
- $R = \lbrace (0,0), (0,1), (1,0), (1,1) \rbrace$ is symmetric and transitive 
but is not reflexive, irreflexive, antisymmetric, asymmetric, or total. 
- $R = \lbrace (0,0), (0,1), (1,0), (1,1), (1,2), (2,0), (2,2) \rbrace$ is 
reflexive and total. It is not irreflexive, symmetric, antisymmetric, 
asymmetric, or transitive. 

