---
layout: page
title: Inverses 
nav_order: 3
has_children: false
has_toc: false
parent: Functions 
grand_parent: Notes
---

## Hitting the undo button 

A natural question to ask about a process is whether it can be undone. We can ask the 
same about a function. 

**Definition**. A _left inverse_ to a function $f: A \to B$ is a function $g : B \to A$ 
such that $g \circ f = \operatorname{id}_A$. Here $\operatorname{id}_A$ is the 
identity function on $A$ so this can rewritten as $g(f(a)) = a$ for all $a$. 

To define a left inverse in Lean, we confront an new problem: we really need to pieces 
of mathematical data: for the function $g : B \to A$ and then the proof that $g \circ f = 
\operatorname{id}$. We can bundle those two things together into a single `structure`. 

{% highlight lean %}
structure LeftInverse (f : α → β) where 
  to_fun : β → α  
  invl : to_fun ∘ f = id 

def TheFun (g : LeftInverse f) : β → α := g.to_fun 
example : g.to_fun ∘ f = id := g.invl
{% endhighlight %}

Given a `(g : LeftInverse f)`, we can access the function `β → α` as `g.to_fun` and 
the proof that `g.to_fun ∘ f = id` using `g.invl`. To construct a `LeftInverse`, we 
need to supply both pieces of data

{% highlight lean %}
def IdInv : LeftInverse (@id α) := ⟨id,by rfl⟩ 
{% endhighlight %}

It also helpful to define single proposition which is true if $f$ has a left inverse. 

{% highlight lean %}
def HasLeftInv (f : α → β) : Prop := Nonempty (LeftInverse f) 
{% endhighlight %}

Here `Nonempty α` is proposition that states there is actually some term of type `α`.

**Definition**. A _right inverse_ to $f$ is a function $h : B \to A$ such that $f \circ h = 
\operatorname{id}_B$. Of course, if $h$ is a right inverse for $f$, then $f$ is 
also a left inverse for $h$. 

**Definition**. An _inverse_ to $f$ is a function that is simultaneously a left and right inverse to 
$f$. 

Possession of inverses and injectivity/surjective are tied closely together. 

**Theorem**. If $f$ has a left inverse, then $f$ is injective. 

{% proof %}
Assume we have $a_1,a_2$ with $f(a_1) = f(a_2)$ and let $g$ be a left-inverse of $f$. 
Then, we can apply $g$ to both sides of the equality $f(a_1) = f(a_2)$ to get 
$$
a_1 = g(f(a_1)) = g(f(a_2)) = a_2
$$
and see that $f$ is injective. 
{% endproof %} 

Here is a proof in Lean. 

{% highlight lean %}
theorem has_left_inv_injective (f : α → β) (h : HasLeftInv f) : Injective f := by 
  -- Introduce a pair of arguments and the assumption that 
  -- f evaluates to the same on them 
  intro (a₁:α) (a₂:α) (l₁: f a₁ = f a₂)
  -- Break up the existence of a left-inverse into a function and a proof it is a
  -- left inverse
  have ⟨g,l₂⟩ := h 
  -- A calculation block allows us to more efficiently perform equality manipulations
  calc
    a₁ = id a₁        := by rfl -- these reduce to an equality 
    _  = (g ∘ f) a₁   := Eq.symm (congrFun l₂ a₁) -- we apply equal functions 
    _  = (g ∘ f) a₂   := congrArg g l₁ -- we apply a function to equal arguments
    _  = id a₂        := congrFun l₂ a₂ -- we apply equal functions to same value again
    _  = a₂           := by rfl -- done
{% endhighlight %}

Similarly, if we have right inverse, then we are surjective. As a corollary, we
get the following statement. 

**Corollary**. If $f$ has both a right and left inverse, then $f$ is a bijection. 

In fact if $f$ has both a left and right inverse, then they have to be equal. 

{% highlight lean %}
theorem left_inv_right_inv_eq { f : α → β } (g : LeftInverse f) (h : RightInverse f) : 
  g.to_fun = h.to_fun := by
    apply funext 
    intro (b: β) 
    calc 
        g.to_fun b = g.to_fun (f (h.to_fun b))  := 
          congrArg g.to_fun (Eq.symm (congrFun h.invr b)) 
        _    = h.to_fun b                       := 
          congrFun g.invl (h.to_fun b)  

theorem inv_unique (f : α → β) (g : Inverse f) (h : Inverse f) : 
  g.to_fun = h.to_fun := by 
    calc 
      g.to_fun = (InvtoLeftInv g).to_fun    := by rfl  
      _        = (InvtoRightInv h).to_fun   := 
        left_inv_right_inv_eq (InvtoLeftInv g) (InvtoRightInv h)   
      _        = h.to_fun                   := by rfl 
{% endhighlight %}

## More nonconstructive tools

We saw about that if $f$ has a left inverse, then it is injective. The converse is also 
true allowing for new nonconstructive tools. 

**Theorem**. Suppose $f: A \to B$ is injective and $A$ is nonempty. Then $f$
has a left inverse. 

{% proof %}
We first make our candidate left inverse function $g: B \to A$. Pick some $b$ from $B$. 
The idea is to split the definition of $g(b)$ into two cases depending on whether 
there exists some $a$ with $f(a) = b$ or not. To do so, we know that $A$ is nonempty 
so we can pick some junk value $a_0$ for use. Then, we "define" $g$ as 
$$ 
g(b) = \begin{cases} a &\text{where $a$ is \textit{some} value satisfying $f(a) = b$} \\
a_0 &\text{if there is no such solution to $f(a) = b$} \end{cases}
$$
Nothing so far depended on the assumption that $f$ is injective. But we haven't checked 
that $g$ is, in fact, a left inverse. From the definition, we know that $g(f(a)) = a'$ 
where $a'$ is some value satisfying $f(a') = f(a)$. Since $f$ is injective, we can 
conclude that $a = a'$ and that we indeed have a left inverse. 
{% endproof %}

So why the quotes around "define" there. It seems reasonable to assume we can pick a value 
from a nonempty set for each value $b$ where there is one. But this is not a consequence 
in set theory and requires additional axiom: the Axiom of Choice.

Let's see what this looks like in Lean where we see the use of choice. 

{% highlight lean %}
-- this definition constructs the g in the proof above. It is marked noncomputable 
-- because Lean cannot make a computer program out of it 
noncomputable def Section (f : α → β) (l : Nonempty α) : β → α := by 
  intro (b:β)
  have a₀ : α := Classical.choice l 
  -- propDecicable tells Lean is ok that that we may not actually be able check 
  -- using a computer program the condition in the following if, then statement 
  have : Decidable (∃ a, f a = b) := Classical.propDecidable (∃ a, f a = b) 
  exact if h : ∃ a, f a = b then Classical.choose h else a₀ 

theorem inj_has_left_inv (f : α → β) (l : Nonempty α) (h : Injective f) : HasLeftInv f := by 
  -- let is like have except it allows for better computation
  let g : β → α := Section f l 
  -- suffices changes the goal to u and shows we can close if we have u using ⟨g,u⟩
  suffices u : g ∘ f = id from ⟨g,u⟩
  apply funext 
  intro (a:α) 
  -- exists is a helper technique for establishing existential statements 
  have (v : ∃ x, f x = f a) := by exists a 
  -- dif_pos is a helper result that says the result of the if, then is what we expect 
  -- when the if condition is true
  have (w : g (f a) = Classical.choose v) := dif_pos v   
  calc 
    g (f a) = Classical.choose v  := w 
    _       = a                   := h (Classical.choose_spec v)
{% endhighlight %}

