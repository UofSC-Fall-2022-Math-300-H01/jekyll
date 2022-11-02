---
layout: page
title: Partial and total orders
nav_order: 3
has_children: false
has_toc: false
parent: Relations 
grand_parent: Notes
---

## Using relations to order 

We have seen some relations that convey a notion of size. 
On $\mathbb{R}$ (and its subsets), we have $<,\leq$. If 
$x < y$, then we think of $y$ as a bigger number than $x$. 

For sets, subset containment $X \subseteq Y$ is similar. If 
$X \subseteq Y$, then every $x \in X$ is also an element of 
$Y$. Thus, $Y$ has more elements than $X$. 

Such ordering relations can be quite useful. As such, we 
make two definitions. 

**Definition**. Let $\prec$ be a relation on $X$. We say 
that $\prec$ is a _partial order_ if it is 
- reflexive 
- antisymmetric 
- and transitive. 
If $X$ has a partial order, we call it a _poset_. 

It is a _total order_ if it is 
- total 
- antisymmetric
- and transistive. 

In the context of partial and total orders, we will use the 
symbol $\prec$. 

As we [saw]({% link notes/relations/properties.md %}), total implies 
reflexive. Thus, 

**Lemma**. 
- Any total order is a partial order. 
- A partial order that is total is a total order. 

We can define partial and total orders in Lean using a structure that 
bundles up the three defining properties. 
{% highlight lean %}
structure PartialOrder (R : α → α → Prop) where
  refl : Reflexive R 
  antisymm : AntiSymmetric R 
  trans : Transitive R 

structure TotalOrder (R : α → α → Prop) where 
  total : Total R 
  antisymm : AntiSymmetric R 
  trans : Transitive R 
{% endhighlight %}

Our work [previously]({% link notes/relations/properties.md %}) lets us 
prove that $a \mid b$ is a partial order on $\mathbb{N}$. 

{% highlight lean %}
theorem div_partial_order : PartialOrder Divides := 
  ⟨div_refl, div_antisym, div_trans⟩  
{% endhighlight %}

It is not a total order however because | is not a total relation. For example, 
$2 \nmid 3$ and $3 \nmid 2$. 

Other familiar examples of partial orders are:
- Sets with $\subseteq$
- $\mathbb{R}$ (or $\mathbb{Z}$ or $\mathbb{N}$) with $\leq$
- Any set with $=$ is a partial order. 

Of these, only $\leq$ on $\mathbb{R}$ is a total order. 

A partial order allows to ask about largest and smallest elements. 

**Definition**. Let $(X, \prec)$ be a poset. A _least element_ $\bot$ 
is an element of $X$ such that 
$$
\forall~ x, \bot \prec x
$$
A _greatest element_ $\top$ is an element of $X$ such that 
$$
\forall~ x, x \prec \top
$$

**Examples**. 
- Let $X$ be a set. Then the poset $(\mathcal P(X),\subseteq)$ has 
$\varnothing$ as a least element and $X$ as a greatest element.
- The poset $(\mathbb{N},\mid)$ has $1$ as a least element and $0$ 
as a greatest element.

**Example**. The totally ordered set $(\mathbb{Z},\leq)$ has neither a 
least or a greatest element. In general, $\bot$ and $\top$ need not exist 
for a poset. 

**Lemma**. Least elements are unique as are greatest elements. 

{% proof %}
Assume we have two least elements $\bot, \bot^\prime$. Then since 
$\bot$ is least, we have $\bot \prec \bot^\prime$. Since $\bot'$ is 
least, we have $\bot^\prime \prec \bot$. From antisymmetry, we get 
$\bot = \bot^\prime$. An analogous argument works for uniqueness of 
greatest elements. 
{% endproof %}

**Lemma**. Let $(X, \prec)$ be a poset with least element $\bot$ and 
greatest element $\top$. If $\bot = \top$, then $X = \lbrace \bot \rbrace$. 

{% proof %}
Let $x \in X$. Then $\bot \prec x$ and $x \prec \top = \bot$. Using antisymmetry, 
we have $x = \bot$. 
{% endproof %}

Suppose we have a poset $(X,\prec)$. Then we can make a new 
set $X_b := X \cup \lbrace -\infty \rbrace$ with a relation $\prec_b$ 
where 
$$ 
R_{\prec_b} = R_\prec \cup \lbrace -\infty \rbrace \times X_b \subset X_b \times X_b
$$
is the subset of related pairs of $\prec_b$. In other words, we all the 
previous relations of $\prec$ hold and the new element $-\infty$ satisfies 
$-\infty \prec_b x$ for all $x$ (including $x = -\infty$). 

Similarly, we can adjoin a greatest element $\infty$. We denate that as $X^t$. 

**Lemma**. Let $(X,\prec)$ be a poset. Then $(X_b,\prec_b)$ 
is a poset with least element $-\infty$. Similarly, $(X^t,\prec^t)$ 
is a poset with greatest element $\infty$. 

{% proof %}
Let's check that $(X_b,\prec_b)$ is a poset. The proof for $(X^t,\prec^t)$ 
is analogous so we omit it.

We check reflexivity. If $x \in X$, then $x \prec_b x = x \prec x$ and we have 
$x \prec x$ since $\prec$ is reflexive. If $x = -\infty$, then by definition 
$-\infty \prec -\infty$. 

We check antisymmetry. Assume that $x \prec_b y$ and $y \prec_b x$. Either $x \in X$ or $x = -\infty$. 
If $x = \bot$, then we contradict the definition of $\prec_b$ unless $y = -\infty$ also. 
In the case $x,y \in X$, we know that $x = y$ from the assumed antisymmetry of 
$\prec$. 

Finally, we check transitivity. Assume that $x \prec_b y$ and $y \prec_b z$. 
If $z = -\infty$, then $y = -\infty$ by definition of $\prec_b$. But then $x = -\infty$ 
from the definition again. Thus, $x = -\infty \prec_b -\infty = z$. 

If $y = -\infty$, then $x = -\infty$ by definition of $\prec_b$. So $x=y \prec_b z$. 

If $x = -\infty$, then $x = -\infty \prec_b z$ by definition. 

The remaining case is where $x,y,z \in X$. But we have assumed that $\prec$ is 
transitive so $x = z$ in this case also. 

{% endproof %}

**Example**. If we take $(\mathbb{R},\leq)$ as our poset then $\mathbb{R}^b_t$ is often 
written as $[-\infty,\infty]$. 
