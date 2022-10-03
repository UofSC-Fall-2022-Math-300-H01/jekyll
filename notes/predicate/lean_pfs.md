---
layout: page
title: Proofs in Lean 
nav_order: 7
has_children: false
has_toc: false
parent: Predicate logic
grand_parent: Notes
---

## Examples 

Let's do some examples of predicate logic proofs in Lean 
to get comfortable with the new syntax and also introduce a 
few more useful tactics.

First, we prove that `∀ (x : α), P x → ∃ (y : α), P y`.  

{% highlight lean %}
example (α : Type) : ∀ (x : α), P x → ∃ (y : α), P y := by 
  intro (a : α)
  intro (h : P a)
  exact ⟨a, h⟩ 
{% endhighlight %}

From out previous discussion, we would expect the final line 
to be `exact Exists.intro a h`. Lean has a shorthard notation 
for intro rules. We can use French quotes (typed \< \>) to 
construct the term. Similarly, if we wanted an `And.intro a b`, 
we could `⟨a, b⟩`. Like most notation it makes thing easier to 
write but can also make it harder to read. 

Let's look at the proof showing we can exchange quantifiers in 
one direction.

{% highlight lean %}
variable (α : Type) 
variable (C : α → α → Prop) 

example : Type) : (∃ (x:α), ∀ (y:α), C x y) → ∀ (v:α), ∃ (u:α), C u v := by 
  intro h v
  -- introduce h : ∃ x, ∀ (y : α), C x y and v : α
  apply Exists.elim h
  -- we supply the existential statement and Lean now asks for a proof of
  -- ⊢ ∀ (a : α), (∀ (y : α), C a y) → ∃ u, C u v
  intro g f  
  -- we introduce f : ∀ (y : α), C g y and g : α 
  apply Exists.intro
  -- we have new goals ⊢ C ?w v and ⊢ α
  exact f v 
  -- this solves the first and Lean then infers the second
{% endhighlight %}

Note that we can introduce multiple terms just by including a spaced 
list of labels for them. 

Next, if there does not exist a value making the predicate true, we can 
conclude it is false for all values. 
{% highlight lean %}
variable (α : Type)
variable (P : α → Prop)

example : (¬ ∃ y, P y) → ∀ x, ¬ P x := by 
  intro h a n 
  exact h ⟨a,n⟩ 
{% endhighlight %}

Below we have another example of giving proofs using quantifiers. 

{% highlight lean %}
variable (α : Type)
variable (P Q : α → Prop)

example : (∀ x, P x → ¬ Q x) → ¬ ∃ y, P y ∧ Q y := by 
  intro h n 
  apply Exists.elim n 
  intro a g 
  -- Here g : P x ∧ Q x 
  exact h a g.left g.right 
  -- Lean lets us use the shorthand g.left for And.left g and similarly 
  -- g.right for And.right g
{% endhighlight %}

Let's do a basic example using functions and equality. 

{% highlight lean %}
variable (α : Type)
variable (P : α → Prop)

example (f : α → α) (x y : α) (h₁ : x = y) (h₂ : P (f x)) : P (f y) := by 
  rw [←h₁]
  -- the goal is now P (f x)
  assumption 
{% endhighlight %}

There a few things to notice in this proof. First, we have `rw [←h₁]` with the 
backwards ←. Lean's convention for rewriting using `x=y` is to search for 
occurrences of `x` and replace them with `y`. If we tried `rw [h₁]`, then 
Lean would return an error 

{% highlight lean %}
tactic 'rewrite' failed, did not find instance of the pattern in the target 
expression  
{% endhighlight %}

Lean allows you to rewrite hypotheses in addition to goals but you need to 
specify the assumption to target. The following proof is also valid.

{% highlight lean %}
example (f : α → α) (x y : α) (h₁ : x = y) (h₂ : P (f x)) : P (f y) := by 
  rw [h₁] at h₂
  -- now h₂ is P (f y)
  assumption
{% endhighlight %}

This tells Lean to look for `x`'s in `h₂` and replace them with `y`'s. In 
both cases, the _assumption_ tactic tells Lean: one of the goals is an 
established fact in the context, figure out which and close the goal. 

You can also feed Lean multiple terms to use for rewriting as a list. 

{% highlight lean %}
variable (α : Type)
variable (x y z : α)
variable (P : α → Prop)

example (h₁ : x = y) (h₂ : z = x) (f : α → α) : f y = f z := by 
  rw [← h₁, h₂] 
{% endhighlight %}


