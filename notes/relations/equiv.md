---
layout: page
title: Equivalence relations
nav_order: 4
has_children: false
has_toc: false
parent: Relations 
grand_parent: Notes
---

## Like equality but not equal to it 

Another common type of relation is the following. 

**Definition**. An _equivalence relation_ is a relation $\cong$ 
that is 
- reflexive
- symmetric and 
- transitive 

The prototypical example of an equivalence relation is equality $=$. 
Here is another example prominent example. 

**Example**. Let $m \in \mathbb{Z}$. Given two integers $a,b$, we 
say $a$ is equivelant to $b$ _modulo_ $m$ if $m \mid b-a$. We 
write $a \equiv b \mod m$ to denote this relation. 

Let's check this is reflexive. To say that $a \equiv a \mod m$, we 
need, by definition, $m \mid a - a = 0$. But all integers divide $0$: 
$0 = 0 \cdot m$. So indeed this is reflexive. 

For symmetry, assume that $a \equiv b \mod m$. Then there is some 
$c$ with $b - a = cm$. We also have 
$$
a - b = -(b-a) = -(cm) = (-c)m 
$$
so we have $b \equiv a \mod m$. 

Now let's check transitivity. Assume that $a \equiv b \mod m$ and that 
$b \equiv c \mod m$. Unfolding the definitions, we have $d_1$ and 
$d_2$ with 
$$
b - a = d_1 m,~ c - b = d_2 m
$$
Then 
$$
c - a = c - b + b - a = d_1 m + d_2 m = (d_1+d_2)m 
$$ 
so $m \mid c -a$. 

Another example we have already seen. 

**Example**. Bijection of sets is an equivalence relation. For reflexivity, 
we use that the identity function $\operatorname{id}_X : X \to X$ is a 
bijection. 

Assume that $f : X \to Y$ is a bijection. Then we seen that we have an 
inverse $f^{-1} : Y \to X$ which is also a bijection. Thus, being in bijection 
is symmetric. 

Finally, given bijections $f: X \to Y$ and $g: Y \to Z$, the composition 
$g \circ f : X \to Z$ is a bijection giving transitivity. 

One last example from the beginning of class. 

**Example**. Bi-implication of proposition is an equivalence relation. We 
need to check 
- For all propositional formula $X$, we have $X \leftrightarrow X$. 
- If $X \leftrightarrow Y$, then $Y \leftrightarrow X$ for any pair of propositional formula. 
- Given $X, Y, Z$ with $X \leftrightarrow Y$ and $Y \leftrightarrow Z$, we have $X \leftrightarrow Z$. 

Here are the proofs in Lean 
{% highlight lean %}
variable (X Y Z : Prop) 

theorem biimp_refl : X ↔ X := ⟨fun h => h,fun h => h⟩ 

theorem biimp_symm (h : X ↔ Y) : Y ↔ X := ⟨h.mpr, h.mp⟩ 

theorem biimp_trans (h₁ : X ↔ Y) (h₂ : Y ↔ Z) : X ↔ Z := 
  ⟨h₂.mp ∘ h₁.mp, h₁.mpr ∘ h₂.mpr⟩ 
{% endhighlight %}

Very often, properties of interest are preserved by an equivalence relation. Mentally, we 
start to treat equivalent elements as equal even through they are not. 

But there is a construction by which equivalence becomes equality. 

**Definition**. Let $X$ be a set with an equivalence relation $\cong$. For $x$ in $X$, 
the _equivalence class_ of $x$ is
$$
[x] := \lbrace x^\prime \mid x \cong x^\prime \rbrace 
$$ 
In other words, $[x]$ is the set of elements that are equivalent to $x$. 

**Example**. Let's take $m = 2$ and consider the equivalence class of $0$ modulo $2$. 
Say $0 \equiv d \mod 2$ is just saying that $2 \mid d - 0 = d$. Thus, $d \in [0]$ 
if and only if $d$ is even. Similarly, $d \in [1]$ if and only if $d$ is odd. 

**Lemma**. $[x^\prime] = [x]$ if and only if $x \cong x^\prime$. 

{% proof %}
Assume that $[x^\prime] = [x]$ then $x^\prime \in [x^\prime]$ since $x^\prime \cong 
x^\prime$ from reflexivity of $\cong$. Then $x^\prime \in [x]$ so by definition 
$x \cong x^\prime$. 

Now assume that $x \cong x^\prime$. We have to show that $[x] = [x^\prime]$ as sets. 
Assume that $y \in [x]$. By definition, we have $x \cong y$. From reflexivity, we 
have $x^\prime \cong x$. Then transitivity tells us that $x^\prime \cong y$. So 
by definition $y \in [x^\prime]$. Now assume that $y \in [x^\prime]$. Then 
$x^\prime \cong y$ be definition. Using transitivity, we get $x \cong y$ and $y \in [x]$. 
Thus, $[x] = [x^\prime]$ as sets. 
{% endproof %}

Using the previous lemma, we learn that $[0]$ and $[1]$ are the only equivalence 
classes mod $2$. If $d$ is odd, then $[d] = [1]$. If $d$ is even, $[d] = [0]$. 

**Definition**. The _quotient_ by an equivalence relation $\cong$ is the set 
of equivalence classes of $\cong$:
$$
X/\cong := \lbrace [x] \mid x \in X \rbrace 
$$

The quotient comes with a _quotient function_
$$
\pi : X \to X/ \cong \\
x \mapsto [x]
$$

**Example**. Thus, $\mathbb{Z}/\equiv_2 = \lbrace [0],[1] \rbrace$. More generally, 
$$
\mathbb{Z}/\equiv_m = \lbrace [0], [1], [2], \ldots, [m-1] \rbrace
$$
Since any integers $a$ can be written as $a = r + qm$ for $0 \leq r < m$. Here 
$r$ is the remainder under division by $m$. 

**Example**. The quotient of `Prop` by `↔` is in bijection with the set of truth 
tables. This follows from completeness and soundness of propositional logic. 

The set $X/\cong$ satisfies a _universal property_ with respect to functions 
$f : X/\cong \to Y$. More precisely, we have the following theorem. 

**Theorem**. Let $(X,\cong)$ be a set with an equivalence relation. Then, for any 
function $f : X \to Y$ which satisfies the condition $x \cong x^\prime \to 
f(x) = f(x^\prime)$, we have a unique function $\overline{f} : X / \cong \to Y$ 
with $\overline{f} \circ \pi = f$. 

{% proof %}
First, we tackle uniqueness. Since $\pi$ is surjective, it has a right inverse. 
Thus, if $\overline{f} \circ \pi = \overline{f}^\prime \circ \pi$, we can compose 
with the right inverse to get $\overline{f} = \overline{f}^\prime$. Thus, the 
condition that $\overline{f} \circ \pi = f$ uniquely determines $\overline{f}$ 
_if_ it exists. 

To show existence, we "try" to define $\overline{f}([x]) = f(x)$. The essential 
problem here is that, as we have seen, we can have $[x] = [x^\prime]$, with 
$x \neq x^\prime$. So from this definition if $x \cong x^\prime$, we also have 
$\overline{f}([x]) = f(x^\prime)$. So we need to check that if $[x] = [x^\prime]$ 
that $\overline{f}([x]) = \overline{f}([x^\prime])$. If $[x] = [x^\prime]$, we know 
that $x \cong x^\prime$. By assumption we have $f(x) = f(x^\prime)$, but 
this says that
$$ 
\overline{f}([x]) = f(x) = f(x^\prime) = \overline{f}([x^\prime])
$$
and our attempt at a function is actually a well-defined function. 
{% endproof %}

The previous theorem says that composing with $\pi$ gives a bijection between 
the following two sets of functions
$$
\lbrace g : X/\cong \to Y \rbrace \overset{- \circ \pi}{\to} 
\lbrace f : X \to Y \mid f(x) = f(x^\prime) \text{ whenever } x \cong x^\prime \rbrace
$$
Thus, we can understand functions out of $X/\cong$ in terms of data that 
does not explicitly reference $X/\cong$ itself. This is what is meant by a 
universal property: the set of functions out of $X/\cong$ to $Y$ are all functions 
$X \to Y$ satisfies some condition. 
