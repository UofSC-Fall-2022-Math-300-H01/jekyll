---
layout: page
title: Properties of functions
nav_order: 2
has_children: false
has_toc: false
parent: Functions 
grand_parent: Notes
---

## Important properties of functions 

Here are two import properties a function can have. 

**Definition**. We say a function $f: A \to B$ is _injective_ 
if for all $a_1,a_2$ with $a_1 \neq a_2$ we have $f(a_1) \neq 
f(a_2)$. So formally, a function is injective if it satisfies 
$$
\forall a_1, a_2, a_1 \neq a_2 \to f(a_1) \neq f(a_2) 
$$

**Example**. The function 
$$
f : \mathbb{Z}  \to \mathbb{Z} \\
n  \mapsto n + 1
$$
is injective. For, if $f(n_1) = f(n_2)$, we have $n_1 + 1 = 
n_2 + 1$. Adding $-1$ to both sides, gives $n_1 = n_2$. 

In checking injectivity of the previous example, we encountered 
the contrapositive $f(a_1) = f(a_2) \to a_1 = a_2$ which is also 
often taken as the definition of injectivity. 

Here is a definition of injectivity and a proof of this example 
in Lean the natural numbers.  

{% highlight lean %}

def Injective (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂ 

def f (n : Nat) : Nat := n + 1

example : Injective f := by 
  -- assume we have two natural numbers and their images are equal 
  intro (n₁ : Nat) (n₂ : Nat) (h : f n₁ = f n₂)
  -- in the library defining the natural numbers we find the useful 
  -- fact that if n + k = m + k we know can conclude n = m. This 
  -- exactly what we want
  exact Nat.add_right_cancel h 
{% endhighlight %}

**Example**. The function 
$$
g : \mathbb{Z} \to \mathbb{Z} \\
n \mapsto n^2 - 3n + 2 
$$
is not injective since $g(1) = g(2) = 0$. 

We can show that $g$ is also not injective in the natural numbers in 
Lean. 

{% highlight lean %}
example : ¬ Injective g := by
  -- we assume that g is actually and try to reach an absurdity
  intro (n : Injective g) 
  -- we use rfl to compute and check equality 
  have : g 1 = g 2 := by rfl 
  -- applying the 
  have : 1 = 2 := n this  
  -- someone has already told Lean that n < n + 1 for all n 
  have o : 1 < 2 := Nat.lt_succ_self 1
  -- and they have also told Lean that n < m → ¬ (n = m) 
  exact Nat.ne_of_lt o this 
{% endhighlight %}

Injectivity can be viewed as saying $f: A \to B$ injects a copy of 
$A$ into $B$.

**Definition**. A function $f: A \to B$ is _surjective_ if, for any 
$b$ in $B$, there is some $a$ with $f(a) = b$. Formally, 
$$
\forall b, \exists a,  f(a) = b 
$$

Returning to our two examples above, we see $n \mapsto n+1$ is also 
surjective. Given $m \in \mathbb{Z}$, since $f(m-1) = m$, we have an 
element mapping to $m$. Thus, $f$ is surjective. If we change the 
domain and codomain to $\mathbb{N}$, $n \mapsto n + 1$ is no longer 
surjective

{% highlight lean %}
def Surjective (f : α → β) : Prop := ∀ b, ∃ a, f a = b 

example : ¬ Surjective f := by 
  intro (h : Surjective f)
  have ⟨m,g⟩ : ∃ n, n + 1 = 0 := h 0 
  -- we use that 0 is never equal to n + 1 for n : Nat
  exact Nat.succ_ne_zero m g  
{% endhighlight %}

The function $n \mapsto n^2$ is not surjective since there is no integer 
that solves $n^2 = -1$. 

Often one wants to understand the totality of $b$'s for which there is 
some $a$ such that $f(a) = b$. This is called the _range_ (or _image_) of 
$f$. Note the range and codomain are distinct in general. Indeed, 
$$
f : \mathbb{Z} \to \mathbb{Z} \\
n \mapsto n + 1
$$
is surjective to the range equals the codomain. But each integer is also 
a real number so the function 
$$
f : \mathbb{Z} \to \mathbb{R} \\
n \mapsto n + 1
$$ 
is also well-defined. Even though, as is common, we used the same notation 
for the two functions, they are _not_ equal as function because they 
have two different codomains.

We can think of a surjective function $f: A \to B$ as way of covering 
$B$ with $A$ using the rule $f$. 

We can combine the two notions in a single one. 

**Definition**. A function $f: A \to B$ is _bijective_ if it is both 
injective and surjective. In Lean, 

{% highlight lean %}
def Bijective (f : α → β) : Prop :=  Injective f ∧ Surjective f 
{% endhighlight %}



Our first example, $n \mapsto n+1$, is bijective. 

Bijectivity can be rephrased as 
$$
\forall b, \exists ! a, f(a) = b
$$
For any $b$, there is exactly one value $a$ satisfying $f(a) = b$. 

Injectivity, surjectivity, and bijectivity are preserved under composition 
in the following sense. 

**Theorem**. Let $f : A \to B$ and $g : B \to C$ be functions. 
- Suppose $f$ and $g$ are injective, Then $g \circ f$ is also injective. 
- Suppose $f$ and $g$ are surjective. Then $g \circ f$ is also surjective. 
- Suppose $f$ and $g$ are bijective. Then $g \circ f$ is also bijective. 

{% proof %}
Assume that $f$ and $g$ are injective. If $g(f(a_1)) = g(f(a_2))$, then since 
$g$ is injective we know that $f(a_1) = f(a_2)$. But since $f$ is injective, 
we have $a_1 = a_2$. Thus, $g \circ f$ is injective. 

Assume that $f$ and $g$ are surjective. Then for a $c$ there is some $b$ with 
$g(b) = c$ since $g$ is sujective. There is also some $a$ with $f(a) = b$ since 
$f$ is surjective. Thus, we have $a$ with $g(f(a)) = c$ and $g \circ f$ is 
surjective. 

Finally if both $f$ and $g$ are bijections, then, by definition, they are both 
injective and surjective. We have just shown that $g \circ f$ is then injective 
and surjective or is a bijection. 
{% endproof %}

We can also detect injectivity or surjectivity using a composition. 

**Theorem**. Let $f : A \to B$ and $g : B \to C$ be functions. 
- If $g \circ f$ is injective, then $f$ is injective. 
- If $g \circ f$ is surjective, then $g$ is surjective. 

Let's give a proof of this in Lean. 

{% highlight lean%}
theorem comp_inj (f : α → β) (g : β → γ) (h : Injective (g ∘ f)) : Injective f := by 
  -- assume we have two values with equal image 
  intro (a₁ : α) (a₂ : α) (h₁ :  f a₁ = f a₂)
  -- apply g to equal arguments yields equal outputs 
  have : g (f a₁) = g (f a₂) := congrArg g h₁ 
  exact h this 

theorem comp_surj (f : α → β) (g : β → γ) (h : Surjective (g ∘ f)) : Surjective g := by 
  -- take some and try to solve g b = c for some b 
  intro (c : γ) 
  -- take the a satisfying g (f a) = c and the proof of equality
  have ⟨a,h₁⟩ : ∃ a, g (f a) = c := h c 
  -- the b we want is f a and the same proof of equality works
  exact ⟨f a, h₁⟩ 
{% endhighlight %}

