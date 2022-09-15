---
layout: page
title: Negation and RAA 
nav_order: 5
has_children: false
has_toc: false
parent: Lean  
grand_parent: Notes
---

## Negation 

Let's see how Lean understands negation. 

{% highlight lean %}
variable (A : Prop)
#reduce ¬ A -- A → False
{% endhighlight %}

The command `#reduce` tells Lean to try to peel away notation and write 
things in a more basic form. So Lean-speak for 
not of a formula are functions that take proofs of `A` to proofs of 
`False`. With this in mind, $\neg$-elimination is another instance 
of function application.

{% highlight lean %}
example (A : Prop) (a : A) (n : ¬ A) : False := n a  
{% endhighlight %}

If `¬ A` means `A → False`, then negation introduction looks very similar 
to implication introduction. 

{% highlight lean %}
variable {A : Prop} 
theorem totallyProvenTheorem (a : A) : False := sorry 
example : ¬ A := totallyProvenTheorem a 
{% endhighlight %}

**Example**. Let's prove the formula `(A → B) → (¬ B → ¬ A)`. 

{% highlight lean %}
variable (A B : Prop)
example : (A → B) → (¬ B → ¬ A) := 
  fun (f : A → B) => fun (h : ¬ B) => fun(a : A) => h (f a) 
{% endhighlight %}
Tilting our heads to the side, we can read this as constructing a 
function which inputs 
- A function `f` taking proofs of `A` to proofs of `B`
- A function `h` taking proofs of `B` to proofs of `False`
- A proof `a` of `A`

From `f a` we get a proof of `B`. Applying `h` gives us a proof of 
`False`. Thus, our output is a proof of `False`. Since Lean views 
`¬ A` as `A → False`, it accepts this construction.

Repeatedly writing the `fun =>` is a little tedious. Thankfully, 
Lean accepts notation more closely adhering to our sense of 
multivariate functions. 
{% highlight lean %}
variable (A B : Prop)
example : (A → B) → (¬ B → ¬ A) := 
  fun (f : A → B) (h : ¬ B) (a : A) => h (f a) 
{% endhighlight %}

Recall that we can prove anything from `False`. In Lean, this is 
{% highlight lean %}
variable (A : Prop) 
#check @False.elim
-- False.elim : False → A
{% endhighlight %}
Appending `@` forces Lean to make explicit some arguments it usually 
infers from the context. (And makes nicer messages to copy.)

## Proof by contradiction

Recall that proof by contradiction (or reducito ad absurdum) allows us to 
conclude $A$ from $\neg A \vdash \bot$. In Lean this is called 
`Classical.byContradiction`. 

{% highlight lean %}
variable (A : Prop)
#check @Classical.byContradiction A
-- Classical.byContradiction : (¬A → False) → A 
{% endhighlight %}

We can eliminate double negation using this in Lean.
{% highlight lean %}
variable (A : Prop)
example : ¬ ¬ A → A := 
  fun (h : ¬ ¬ A) => Classical.byContradiction (fun (n : ¬ A) => h n) 
{% endhighlight %}
Note that ``fun (n : ¬ A) => h n`` is function that takes proofs of `¬ A` to 
proofs of `False`. Applying `byContradiction` to this yields a proof of `A` 
as we want.

We also have access to the law of the excluded middle built in. 
{% highlight lean %}
#check Classical.em
-- Classical.em : ∀ (p : Prop), p ∨ ¬p
{% endhighlight %}

**Example**. Let's prove the converse of the previous example `(¬ B → ¬ A) → (A → B)`.

{% highlight lean %}
example : (¬ B → ¬ A) → (A → B) := 
  Or.elim (Classical.em B) 
    (fun (b : B) (_ : A) => b) 
    (fun (n : ¬ B) (a : A) => False.elim (h n a)) 
{% endhighlight %}
Notice how Lean just "figured out" that we wanted to eliminate `False` into `B`.
