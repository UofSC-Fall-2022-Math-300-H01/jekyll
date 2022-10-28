---
layout: page
title: Basic ideas
nav_order: 1
has_children: false
has_toc: false
parent: Relations 
grand_parent: Notes
---

## Basics of relations

We already know what relations are. We saw then as part of 
predicate logic. 

**Definition**. A _relation_ is a binary predicate. So in Lean 
we would write 

{% highlight lean %}
variable (U : Type) 

variable (R : U → U → Prop) 
{% endhighlight %}

In sets, one usually defines a relation on elements of a 
set $X$ as a subset 
$$
R \subseteq X \times X
$$
The corresponding predicate is then 
$$
(x,x^\prime) \in R 
$$

We write $x R y$ to abbreviate that staement that $x$ is 
related by $R$ to $y$, the predicate is satisfied for 
the values $x$ and $y$. Often from the context, we will 
just write $x \sim y$.

The simple definition allows for a variety of examples. 

**Examples**
- We could simply take 
{% highlight lean %}
def R (x y : U) := fun x y => False
{% endhighlight %}
Since there is no proof of false, no pairs are even related. 
The corresponding subset of $U \times U$ is $\varnothing$. 
- At the other end of the extreme, we have 
{% highlight lean %}
def R (x y : U) := fun x y => True 
{% endhighlight %}
Here every pair $(x,y)$ is related. The corresponding subset 
of $U \times U$ is $U \times U$ itself. 
- Equality is perhaps the most familiar example of a 
relation. 
{% highlight lean %}
def R (x y : U) := fun x y => x = y 
{% endhighlight %}
The corresponding subset of $U \times U$ is called the _diagonal_ 
$$
\Delta_U := \lbrace (x,x) \in U \times U \mid x \in U \rbrace 
$$
- Lets take the natural numbers. Thanks to their rich structure 
there are many possible relations. We have the familiar relation 
based on size of integers: $n < m$ denotes that $n$ is less than 
$m$. Lean already knows about this 
{% highlight lean %}
variable (n m : Nat) 
#check n < m 
-- n < m : Prop
{% endhighlight %}
The subset of the $\mathbb{N} \times \mathbb{N}$ is just 
$$
R_{<,\mathbb{N}} := \lbrace (n,m) \mid n < m \rbrace
$$ 
If we identity $\mathbb{N} \times \mathbb{N}$ with the lattice 
points in the first quadrant of $\mathbb{R}^2$, then we can 
visualize $R_{<,\mathbb{N}$ as all the points above the line 
$y = x$. 
- We have the close cousin of $ < $ on $\mathbb{N}$ : $\leq$, less than 
or equal. We simply combined two relations we have seen above 
using an $\lor$
$$
n \leq m \leftrightarrow (n < m) \lor (n=m)
$$
Since have combined two relations using an or statement we get the 
union of their corresponding subsets 
$$
R_{\leq, \mathbb{N}} = \Delta_{\mathbb{N}} \cup R_{<,\mathbb{N}}
$$
- The previous example built a new relation from an old one using a 
particular logical connective. One can, of course, use the other 
connectives, $\to, \land, \neg$. For example, we have 
$$
x > y := \neg (x \leq y) 
$$
where the corresponding subset is $R_{\leq, \mathbb{N}}^c$, the 
complement. 
- We can also use arithmetic to build relations on natural numbers.
For example, we have divisibility $a \mid b$ if there exists some 
$c$ with $b = ac$.
- Similarly, we can use functions to build new relations from old ones. 
For example, let's take $ < $ on the real numbers $\mathbb{R}$ and 
the absolute value function $| \cdot | : \mathbb{R} \to \mathbb{R}$. 
Let's say that $x$ is related to $y$ if $|x| \leq |y|$. This gives a 
new relation which is equal to $x \in [-y,y]$. 

Looking at our examples, we say a variety of behaviors. For some, we 
have $x \sim x$ for all $x$, like $=$, but for others we don't, like 
$<$. For some we can always compare $x$ to $y$ or vice-versa; for others 
we can't.

There are a handful of natural properties we can impose on relations 
which we will discuss next.
