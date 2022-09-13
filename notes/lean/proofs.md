---
layout: page
title: More rules and proofs
nav_order: 4
has_children: false
has_toc: false
parent: Lean  
grand_parent: Notes
---

## Conjunction 

To build a proof of $A \land B$, we needs proofs of $A$ and $B$. 
In Lean, this is accomplished by `And.intro`. 
{% highlight lean %}
example : (a : A) (b : B) : A ∧ B := And.intro a b
{% endhighlight %}

For elimination, we use `And.left` and `And.right` to extract 
proofs from `A ∧ B`. 
{% highlight lean %}
example : (h : A ∧ B) : A := And.left h 
example : (h : A ∧ B) : B := And.right h 
{% endhighlight %}

## Disjunction 

For the or-introduction rules, we have 
{% highlight lean %}
example : (a : A)  : A ∨ B := Or.inl h 
example : (b : B)  : A ∨ B := Or.inr h 
{% endhighlight %}

For $\lor$-elimination we need  
three things : 
1. $A \lor B$
2. A proof $A \vdash C$
3. A proof $B \vdash C$
Let's see what it looks like in Lean. 
{% highlight lean %}
#check Or.elim 
-- ∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
{% endhighlight %}
So to use `Or.elim` we need three proofs: 
1. `r : A ∨ B` 
2. `p : A → C`
3. `q : B → C`

Let's see a one direction of a commutativity of `∨` in Lean 
and at the same time get some sense of how to build up a proof in 
steps. Often Lean can "fill in" arguments from the context. You 
can ask it by placing a `_`. Let's see what happens here. 
{% highlight lean %}
example (h : A ∨ B) : B ∨ A := Or.elim h _ _  
{% endhighlight %}
The infoview might look something like 
{% highlight lean %}
don't know how to synthesize placeholder for argument 'right'
context:
A B : Prop
h : A ∨ B
⊢ B → B ∨ A

don't know how to synthesize placeholder for argument 'left'
context:
A B : Prop
h : A ∨ B
⊢ A → B ∨ A
{% endhighlight %}

Lean is asking for our proofs of `B → B ∨ A` and `A → B ∨ A`. 
Remember that the are functions that turn any proof of `B` into a 
proof of `B ∨ A` and the same with `A` to `B ∨ A`. We can 
fill in the proof by providing such functions using or eliminations. 

{% highlight lean %}
example (h : A ∨ B) : B ∨ A := 
  Or.elim h (fun (a:A) => Or.inr a) (fun (b:B) => Or.inl b)
{% endhighlight %}

## Bi-implication 

We can eliminate a bi-implication into two implications. 
{% highlight lean %}
example (h : A ↔ B) : A → B := Iff.mp 
example (h : A ↔ B) : B → A := Iff.mpr
{% endhighlight %}

Here `mp` stands for "Modus ponens" and `mpr` for the "reverse". 

To introduce a bi-implication, we need proofs of `A → B` and 
`B → A`. 
{% highlight lean %}
#check Iff.intro -- ∀ {a b : Prop}, (a → b) → (b → a) → (a ↔ b)
{% endhighlight %}

## Some examples

{% highlight lean %}
example (h : A → B ∧ C) : A → C := fun (a : A) => And.right (h a)
{% endhighlight %}

{% highlight lean %}
example : A ∧ B → A ∨ B := fun (p : A ∧ B) => Or.inl (And.left p)
{% endhighlight %}

{% highlight lean %}
example  (h : A ∧ B) : B ∧ B := And.intro (And.right h) (And.right h)
{% endhighlight %}
