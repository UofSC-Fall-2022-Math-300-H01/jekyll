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
  apply Exists.elim h 
  intro g f 
  apply Exists.intro 
  exact f v 
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

