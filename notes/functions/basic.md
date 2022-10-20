---
layout: page
title: Basic ideas
nav_order: 1
has_children: false
has_toc: false
parent: Functions 
grand_parent: Notes
---

## Basics of functions 

As we have seen Lean has built in types function `f : A → B`. 
We encountered these when dealing with implication in propositional/predicate
logic. Given propositions `P Q : Prop`, a term `h : P → Q` is a function 
that inputs proofs of `P` and outputs proofs of `Q`. 

Similarly, we modeled predicates as functions `P : U → Prop` which take terms 
of a general type `U` and output propositions. And a proof `h : ∀ x, P x` is 
function whose inputs are terms `x : U` and whose output at a given `x` is a 
proof of `P x`. 

The last incarnation is particularly instructive of the power of the existence 
of a function. For a general predicate `P`, there will be not be a proof of 
`∀ x, P x`. In other words, we will not be able to make a well-defined function. 

The Lean notation and the mathematical notation for a function coincide: 
`f : A → B`. Here `A` is called the _domain_ of `f` and `B` is called the 
_codomain_ of `f`. In other words, the domain of a function is the type of 
its inputs and the codomain is the type of outputs. 

Mathematically, it is useful to approach to construction of a function with 
more an artistic mentality. Often we will make a function that where the output
seemingly depends on more data than the given inputs and then provide a 
proof that the extra data, while not extraneous, does not change the output 
when it changes. Checking this is usually called checking that a function is 
_well-defined_. 

**Example**. Suppose $x \in \mathbb{R}$ is a real number. Consider 
the function 
$$ 
x \mapsto \sqrt{x}
$$
Where $\sqrt{x}$ satisfies $(\sqrt{x})^2 = x$. Is this a well-defined function? 
For any input from $\mathbb{R}$, we need to be able to evaluate this function 
into a _single_ output. 

Problem #1: if $x < 0$, then there are _no_ (real number) solutions to $y^2 = x$. 
Thus, this proposed function cannot be evaluated for $x < 0$. We would say 
that this is not well-defined for $x < 0$.

Problem #2: Let's assume that $x \geq 0$. We now have another problem. If 
$x > 0$, then there are _two_ choices for $\sqrt{x}$, a positive one and a 
negative one. Thus this is also not a well-defined function for $x>0$. 

To fix this, we impose some additional conditions. First, the domain of 
$\sqrt{x}$ is not all of $\mathbb{R}$. It is all real numbers satisfying 
$x \geq 0$. The square root function, 
as it appeared in your calculus class, is then the _positive_ solution to the 
equation $y^2 = x$ for a given input $x > 0$ and is, of course, $0$ if $x=0$. 

In Lean, we cannot write a non-well-defined function - the type checker will 
yell at us. Suppose you are handed a type `U` and are asked for some function 
`f : U → U`. What can you do? You can hand back the input as the output. 

**Definition**. The _identity function_ is the function whose output is 
equal to input, i.e. $x \mapsto x$. 

The identity function depends on the type of `x`. Let's see it in Lean. 

{% highlight lean %}
variable (α : Type) 

#check @id α  --  id : α → α
{% endhighlight %}

With more information about the input type we can generally make more 
functions. 

{% highlight lean %}
variable (α β : Type)

-- if we take a product term we can project onto each component 
def proj (z : α × β) := z.1 

#check proj α β -- proj α β : α × β → α
{% endhighlight %}

As we can see projection for product types is also built in already using 
`z.1`,`z.2` or `z.fst,z.snd`.

Let's get even more specific. Lean knows about natural numbers and all 
the usual arithmetic operations we can apply to them. The name for $\mathbb{N}$ 
in Lean is `Nat`. 

{% highlight lean %}
def f : Nat → Nat := fun n => 2*n^3 + 4*n + 3

#eval f 5 -- 273
{% endhighlight %}

The command `#eval` calls a more efficient (but less type-safe) evaluation 
program to compute the application of `f`.

## Chaining functions 

One of the most powerful aspects of functions is the ability to chain them 
together, one after another after another... 

If we have `f : A → B`, `g: B → C`, then we can take an input `a`, feed it 
into `f` as `f a`, and then feed that into `g` as `g (f a)`. The result 
is the _composition_ of `f` and `g`. 

**Definition**. Given functions $f : A \to B$ and $g : B \to C$, the 
_composition_ of $g$ and $f$ is the function 
$$
a \mapsto g(f(a))
$$
The composition is denoted as $g \circ f$ and is typed in Lean
as `Function.comp` and is abbreviated as `\circ`. 
Note that composing is only possible if the codomain of $f$ equals 
the domain of $g$. 

Let's see some examples in Lean. 

{% highlight lean %}
def f : Nat → Nat := fun n => 2*n^3 + 4*n + 3
def g (n : Nat) : Nat := n^2 + 1 

#check g ∘ f  -- g ∘ f : Nat → Nat 
#eval f 1 -- 9 
#eval g (f 1)  -- 82 
#eval (g ∘ f) 1 -- 82

-- note that the order of composition is essential 
#eval f (g 1) -- 27 
{% endhighlight %}

In general $g \circ f \neq f \circ g$ even if both compositions are well-defined 
so functional composition is _non-commutative_. It is associative however.  

**Theorem**. Composition of functions is an associative operation. In other words, 
if $f: A \to B$, $g : B \to C$, and $h : C \to D$ are three functions, then 
$$ 
(h \circ g) \circ f = h \circ (g \circ f) 
$$

{% proof %}
Two functions $f_1,f_2$ are equal if they have the same domains and codomains and 
if for any element $x$ of the domain we have $f_1(x) = f_2(x)$. More plainly, 
two functions are equal if 
- they take in the same types of inputs 
- they give back the same type of outputs and 
- for any input, they evaluate to the same output

So to prove this we assume we have some $a$ from $A$ and evaluate both sides. 
The left-hand side is by definition 
$$
((h \circ g) \circ f)(a) = (h \circ g)(f(a)) = h(g(f(a)))
$$
The right-hand side is 
$$
(h \circ (g \circ f))(a) = h((g \circ f)(x)) = h(g(f(a)))
$$
These are equal so the functions are equal. 
{% endproof %}

What does the proof of associativity look like in Lean?

{% highlight lean %}
variable (α β γ δ : Type) 
variable (f : α → β) (g : β → γ) (h : γ → δ) 

theorem Assoc : (h ∘ g) ∘ f = h ∘ (g ∘ f) := by 
  apply funext
  -- the goal is now 
  -- ⊢ ∀ (x : α), Function.comp (h ∘ g) f x = Function.comp h (g ∘ f) x
  intro a 
  rfl 
{% endhighlight %}

Here `funext` is a (more robust) version of the proposition 
$$
\forall f_1,f_2 : A \to B, f_1 = f_2 \leftrightarrow (\forall a, f_1(a) = f_2(a)) 
$$
and stands for _functional extensionality_ (similar to set extensionality). 

Notice also that `rfl` closed the goal `Function.comp (h ∘ g) f x = Function.comp 
h (g ∘ f) x` even though it is not immediately of the form `t = t`, i.e. something is 
equal to itself. This is due to the fact that `rfl` can also reduce terms to their 
more basic form, just like we did in our own pen-and-paper proof of associativity of 
functional composition. 

The identity function plays a special rule in composition - composing with it does 
nothing. Or stated at more high-level: composition with an identity function is 
also an identity function but now for functions: $f \mapsto f$. 

{% highlight lean %}
variable (α β : Type) 
variable (f : α → β) 

theorem comp_id : f ∘ (@id α) = f := by 
  apply funext 
  intro x 
  rfl 

theorem id_comp : (@id β) ∘ f = f := by 
  apply funext 
  intro x 
  rfl 
{% endhighlight %}

Another useful consequence of functional extensionality is that if $f = g$ then 
$f(x) = g(x)$ for any $x$. We could extract this result from `funext` each time 
we want to use it but that is not very ergonomic. Instead, the result is already 
built into Lean as `congrFun`. 

{% highlight lean %}
variable (α β : Type) 
variable (f₁ f₂ : α → β) 

example (h : f₁ = f₂) (a : α) : f₁ a = f₂ a := by 
  exact congrFun h a  
{% endhighlight %}

The contrapositive of this statement is useful. 

{% highlight lean %}
variable (α β : Type) 
variable (f₁ f₂ : α → β) 

example (h : ∃ a, f₁ a ≠ f₂ a) : f₁ ≠ f₂  := by 
  intro n 
  have ⟨a,h₁⟩ := h 
  have : f₁ a = f₂ a := congrFun n a 
  exact h₁ this 
{% endhighlight %}

