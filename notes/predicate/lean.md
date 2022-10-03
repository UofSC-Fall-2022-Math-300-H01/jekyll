---
layout: page
title: Lean 
nav_order: 6
has_children: false
has_toc: false
parent: Predicate logic
grand_parent: Notes
---

## Predicate logic in Lean

Like with propositional logic, Lean has the rules of 
predicate logic embedded within it.

As we discussed, predicates are analogous to functions which 
output propositions. We can declare predicates in Lean as '

{% highlight lean %}
variable (α : Type)

variable (A : α → Prop)
variable (B : α → α → Prop)
{% endhighlight %}

A new subtlety is `variable (α : Type)`. In predicate logic, 
we have domain of discourse, which is the source of values for the 
input variables of our predicates. In Lean, we have to declare that we 
have some source of inputs of our predicates. This notation tells 
Lean that we have something `α` whose type is the generic `Type`. 

Then `A` is a predicate on a single variable and `B` is one on two 
variables. 

We can understand $\forall x~ A(x)$ as saying that no matter what 
the value of $x$ is we have a proof of $A(x)$. In this way, we 
can think of a proof of $\forall x~ A(x)$ as a _function_ whose 
inputs are $x$'s and whose outputs are proofs of $A(x)$. 

In Lean, this is how `∀` is understood. For example, if we 
look at 
{% highlight lean %}
variable (P Q : Prop) 
theorem not_true : P \to Q := sorry 
#check not_true 
{% endhighlight %}
we will see
{% highlight lean %}
not_true : ∀ (P Q : Prop), P → Q
{% endhighlight %}
Given any pair of propositions `P` and `Q`, the "theorem" `not_true` 
produces a (sorried) proof of `P → Q`. Lean represents this using a 
`∀`. 

Since `∀` is implemented via as a function, the introduction and 
elimination rules are familiar. 

{% highlight lean %}
variable (α : Type) 
variable (A : α → Prop) 

example : ∀ (x:α), A x → A x := fun x (h : A x) => h 

example (y : α) (h : ∀ x, A x) : A y := h y 
{% endhighlight %}

Next, let's look at the existential quantifier `∃`. 

{% highlight lean %}
variable (α : Type) 

#check @Exists α 
-- @Exists α : (α → Prop) → Prop

#check @Exists.intro α
-- @Exists.intro α : ∀ {p : α → Prop} (w : α), p w → Exists p

#check @Exists.elim α 
-- @Exists.elim α : ∀ {p : α → Prop} {b : Prop}, 
-- (∃ x, p x) → (∀ (a : α), p a → b) → b
{% endhighlight %}

Given a domain of discourse `α` and a predicate `A : α → Prop`, the 
existential quantification `∃ x, A x` is a proposition. This is what 
`Exists` models. 

Then, we have our introduction and elimination rules for `∃` built in to 
`Exists`. Existential introduction takes 
- a domain of discourse `α` (which Lean tries to infer from the context),
- a predicate `p : α → Prop` (inferred if possible),
- and a value `(w : α)`

and yields a function 
that converts proofs of the proposition to `p w` to an existentially 
quantified proposition. 

Elimination will take 
- a domain of discourse `α` (inferred),
- a predicate `p` (inferred),  
- a proposition `b`, 
- a proof of `∃ x, p x`, 
- a proof of `∀ (a : α), p a → b` (ie a function with inputs `a` and a proof 
of `p a` and output a proof of `b`), 

and will return a proof of `b`. If we have some value where `p` is true and 
for any value `p x` implies `b`, then we can conclude `b`. 

Here are simple example uses. 

{% highlight lean %}
variable (α : Type)
variable (A : α → Prop)

example (x:α) (h:P x) : ∃ y, P y := Exists.intro x h 

example (h : ∃ y, ¬ P y) :  ¬ (∀ x, P x) := by 
  intro (g : ∀ x, P x)
  apply Exists.elim h 
  intro (a : α) 
  intro (l : ¬ P a)   
  exact l (g a) 
{% endhighlight %}

Next, we have equality, $=$. 

{% highlight lean %}
variable (α : Type)

#check @Eq α 
--  @Eq : α → α → Prop
{% endhighlight %}

Equality at its most basic level is a special named predicate on two variables. 
But, we remember it satisfies some properties. Firstly, reflexivity, symmetry, 
and transistivity. These becomes ways to build equality. 

{% highlight lean %}
variable (α : Type) 

#check @Eq.refl α 
-- @Eq.refl α : ∀ (a : α), a = a

#check @Eq.symm α
-- @Eq.symm α : ∀ {a b : α}, a = b → b = a

#check @Eq.trans α 
-- @Eq.trans α : ∀ {a b c : α}, a = b → b = c → a = c
{% endhighlight %}

There are also substitution rules for equality, one involving function application 
and one for predicates. 

{% highlight lean %}
variable (α β : Type) 

#check @Eq.subst α 
--  @Eq.subst α : ∀ {motive : α → Prop} {a b : α}, a = b → motive a → motive b

example (P : α → Prop) (x y : α) (e : x = y) (h : P x) : P y := Eq.subst g h  

#check @congrArg
--  @congrArg α β : ∀ {a₁ a₂ : α} (f : α → β), a₁ = a₂ → f a₁ = f a₂

example (f : α → α) (x y : α) (h : x = y) : f x = f y := congrArg f h 
{% endhighlight %}




