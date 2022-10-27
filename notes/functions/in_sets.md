---
layout: page
title: Functions and sets 
nav_order: 4
has_children: false
has_toc: false
parent: Functions 
grand_parent: Notes
---

## Interactions between functions and sets

If we already know about sets, then we can actually construct 
functions directly. At first the definition looks a little strange. 

**Definition**. Let $X$ and $Y$ be sets. A _function_ $f : 
X \to Y$ is a subset 
$$
\Gamma \subseteq X \times Y 
$$
satisfying the condition 
$$
\forall~ x, \exists !~ (x',y) \in \Gamma, x = x' 
$$
In other words, in our subset of pairs, $\Gamma$, given an element 
$x \in X$, there is one and exactly one ordered pair of the form 
$(x,y)$. 

Given a function, $\Gamma_f$, we can define application of the 
function to an element $x \in X$ as 
$$
x \mapsto y 
$$ 
where $y$ is the unique element of $Y$ making $(x,y) \in \Gamma_f$ 
hold. 

Given a function of the familiar type $f : X \to Y$, we can make 
subset of $X \times Y$ as 
$$
\Gamma_f := \lbrace (x,f(x)) \mid x \in X \rbrace
$$
This is commonly called the _graph_ of $f$. 

Given a $f : A \to B$ and a subset $X \subseteq A$, we define a 
new subset of $B$. 

**Definition**. The _image_ of $X$ under the function $f$ is the 
set 
$$
f(X) := \lbrace b \mid \exists~ x \in X, f x = b \rbrace
$$

**Example**. If 
$$
f : \mathbb{N} \to \mathbb{N} \\
n \mapsto n^2
$$
is our function, then $f(\mathbb{N})$ is the set of natural numbers 
which are squares. 

If we instead start with a subset $Y \subseteq B$, then we can 
create a subset of $A$. 

**Definition**. The _pre-image_ (or _inverse image_) of $Y$ is the 
set 
$$
f^{-1}(Y) := \{ a \mid f(a) \in Y \}
$$

Coming back to our example of the squaring map, we would have 
$$
f^{-1}(\lbrace 0,1,2,3,4,5,6,7,8 \rbrace) = \{0,1,2\}
$$

**Lemma**. $f$ is surjective if and only if $f(X) = Y$. 

{% proof %}
Assume that $f$ is surjective. From the definition, we know 
that $f(X) \subseteq Y$. For the other direction, assume we 
have $y \in Y$. Since $f$ is surjective, there exists a $x \in X$ 
with $f(x) = y$. But, by definition of the image $X$ under $f$, 
this says $y \in f(X)$. 

Assume that $f(X) = Y$. To show that $f$ is surjective, we choose 
some $y \in Y$ and look for an $x$ with $f(x) = y$. But, by 
definition of the image, we know there is such an $x$. 
{% endproof %}

More generally, we get two statements describing what happens when 
we take images of pre-images and pre-images of images. 

**Lemma**. For any $Y$, we have  
$$
f(f^{-1} Y) \subseteq Y 
$$

{% proof %}
Let $b \in f(f^{-1} Y)$. We unfold the definitions to check this. 
Since $b \in f(f^{-1} Y)$, we have, by definition, there exists 
some $a \in f^{-1} Y$ such that $f(a) = b$. Since $a \in f^{-1} Y$, 
by definition, we have $f(a) \in Y$. Thus, $b = f(a) \in Y$. 
{% endproof %}

Note that this is not an equality in general. If we have an equality, 
then every element of $Y$ is in the image of $f$ applied to $f^{-1} Y$. 
In particular, it forces $f$ to surject onto $Y$. 

**Lemma**. For any $X$, we have  
$$
X \subseteq f^{-1}(f(X))
$$

{% proof %}
Again, this comes from chaining together the definitions. Assume that 
$a \in X$. Then $f(a) \in f(X)$. Thus, by definition, $a \in f^{-1}
(f(X))$. 
{% endproof %}

Again this is not always an equality. For example, lets taking our 
squaring map but now view it a function $\mathbb{Z} \to \mathbb{Z}$. 
If $X = \mathbb{N}$, then $f^{-1}(f(\mathbb{N})) = \mathbb{Z}$. 

Both images and pre-images behave well with respect to unions and 
intersections. We have

{% highlight lean %}

-- The union of inverse images is the inverse image of the union
theorem union_preimage (f : α → β) (Y Y' : Set β) : 
  f⁻¹ (Y ∪ Y') = f⁻¹ Y ∪ f⁻¹ Y' := by rfl 

-- The intersection of inverse images is the inverse image of 
-- the intersection 
theorem inter_preimage (f : α → β) (Y Y' : Set β) : 
  f⁻¹ (Y ∩ Y') = f⁻¹ Y ∩ f⁻¹ Y' := by rfl 

-- The union of images is the image of the union 
theorem union_image (f : α → β) (X X' : Set α) : 
  Image f (X ∪ X') = Image f X ∪ Image f X' := by 
    set_extensionality b 
    · intro h 
      have ⟨a,h'⟩ := h 
      cases h'.left with 
      | inl hl => exact Or.inl ⟨a,hl,h'.right⟩
      | inr hr => exact Or.inr ⟨a,hr,h'.right⟩ 
    · intro h 
      cases h with 
      | inl hl => 
        have ⟨a,h'⟩ := hl 
        exact ⟨a,⟨Or.inl h'.left,h'.right⟩⟩ 
      | inr hr => 
        have ⟨a,h'⟩ := hr 
        exact ⟨a,⟨Or.inr h'.left,h'.right⟩⟩ 

-- The image of the intersection is a subset of the 
-- intersection of the image
theorem inter_image (f : α → β) (X X' : Set α) : 
  Image f (X ∩ X') ⊆ Image f X ∩ Image f X' := by 
    intro b h 
    have ⟨a,h'⟩ := h 
    exact ⟨⟨a,⟨h'.left.left,h'.right⟩⟩,⟨a,⟨h'.left.right,h'.right⟩⟩⟩  
{% endhighlight %}

In general, $f (X \cap X') \neq f(X) \cap f(X')$. For example, take 
the unique function $f : \mathbb{Z} \to \lbrace 0 \rbrace$, $X$ the odd integers, 
and $X'$ the even integers. Then $X \cap X' = \varnothing $ but 
$f(X) \cap f(X') = \lbrace 0\rbrace$. 

## Being in bijection 

Saying that we have a bijection $f : A \to B$ is quite strong. For 
each element of $a$ there is exactly one element of $b$ and vice-versa. 
You go back and forth by apply $f$ or its inverse. While particular 
bijections can be highly non-trivial, we can still abstract them as a 
"change of labels" for a set.

**Example**. Let $R_m$ be the complex roots of the polynomial $z^m - 1$. 
The roots are of the form $e^{2 \pi \imath j/m}$ for $j = 0,\ldots,m-1$. Thus, 
there is a bijection between the set of $R_m$ and the set $[m] := \lbrace 
0, 1, \ldots, m-1 \rbrace$. 

One of this is very simple, $[m]$, while the other carries interesting 
algebraic information. 

**Definition**. We say $A$ and B$ are _in bijection_ if there exists a 
bijection $f : A \to B$. We write $A \cong B$ if $A$ and $B$ are in 
bijection. 

Even if $A \cong B$, there is, in general, not a single bijection nor a 
canonical choice for one. 

Let's look at self-bijections $\sigma : [m] \to [m]$. In general, 
if we have an injective function $f : [m] \to A$, then we have at least 
$m$ distinct (up to equality) elements of $A$. Now, if $A = [m]$, then 
we only have $[m]$ distinct elements to being with. Thus, $\sigma : [m] 
\to [m]$ is bijective if and only if it is injective. 

Similarly, if $\sigma : [m] \to [m]$ is surjective, then we have to have 
$m$ elements in $\sigma([m])$. But, for any function with domain $[m]$, 
the image can have at most $m$ elements since we only have $m$ elements 
to plug in to $f$. If we have exactly $m$ elements, then $\sigma$ must 
be injective. Each time $\sigma(i) = \sigma(j)$, with $i \neq j$, we drop 
the size of the image of by 1. Thus, $\sigma$ is bijective if and only if 
it is surjective. 

We have established the following result.

**Theorem**. (Pigeonhole Principle)  A function $f : X \to Y$ with $X, Y$ 
finite and of the same order is a bijection if and only if it is an injection 
if and only if it is a surjection. 

Similar logic gives the 

**Corollary**. If $f : X \to Y$ is a function between finite sets and $\|X\| < \|Y\|$, 
then $f$ is not surjective. If $|X| > |Y|$, then $f$ is not injective. 

The previous results tell us to recognize bijections between finite sets. 
We see that for $\sigma : [m] \to [m]$ to be a bijection. We have some 
value $\sigma(0)$. Then there is some value $\sigma(1) \neq \sigma(0)$. 
Then $\sigma(2) \neq \sigma(1)$ and $\neq \sigma(0)$ . . . Finally, leaving a 
unique choice for $\sigma(m)$.

So a self-bijection of $[m]$ is scrambling of the order of the numbers $0,1,2,\ldots,
m-1$. There are $m$ choices for the value of $0$, $m-1$ choices for $1$,. . ., 
$2$ choices for $m-2$, and a single choice for $m-1$. Thus, we have 
$$
m! := m(m-1)(m-2) \cdots 2 \cdot 1 
$$
unique self-bijections of $[m]$. Such self-bijections are called _permutations_. 

**Example**. Let's write down all the permutations of the set $[3]$. We 
as (possibly) disordered lists: 
$$
123, 132, 213, 312, 231, 321 
$$
The first entry of the list is the identity function. 

