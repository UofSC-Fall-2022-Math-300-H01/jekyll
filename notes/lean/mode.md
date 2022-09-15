---
layout: page
title: Interactive mode	
nav_order: 6
has_children: false
has_toc: false
parent: Lean  
grand_parent: Notes
---

## Game mode

All the proofs we have seen so far have been a little hard for a 
person to read. As mentioned, Lean can serve as an _interactive_ 
theorem prover. There is more interactive mode to write proofs called 
_tactic mode_. Tactic mode also allows us to structure our 
proofs in more human-readable form.

To enter tactic mode, we add the keyword `by` after the `:=` like 
so. 
{% highlight lean %}
example : False := by  
{% endhighlight %}
In the Infoview pane, you will see something like 
{% highlight lean %}
▶ 1 goal
⊢ False
{% endhighlight %}

You can `sorry` this and notice that `Goals accomplished 🎉` appears 
for the goal state; though Lean still gives a warning that we are using `sorry`. 

Inside tactic mode, you can use tactics. Each tactic is a built-in helper 
function for constructing a proof. Let's look at some in an example step 
by step. 

Suppose we wanted to prove the formula `(A → B ∧ C) → (A → B) ∧ (A → C)`. We 
start with 
{% highlight lean %}
example : (A → B ∧ C) → (A → B) ∧ (A → C) := by 
{% endhighlight %}
and the infoview provides the current state
{% highlight lean %}
A B C: Prop
⊢ (A → B ∧ C) → (A → B) ∧ (A → C)
{% endhighlight %}
We have assumptions `A B C` which are propositions and our goal is 
`(A → B ∧ C) → (A → B) ∧ (A → C)`.

Next we would normally start with `fun (h : A → B ∧ C) =>`. In tactic mode, 
we can use the tactic `intro`. When our goal is of the for `X → Y`, `intro h` 
will introduce an assumption `h : X` and change our goal to `Y`. Here
{% highlight lean %}
example : (A → B ∧ C) → (A → B) ∧ (A → C) := by 
  intro h 
{% endhighlight %}
and the infoview provides the current state
{% highlight lean %}
A B C: Prop
h : A → B ∧ C
⊢ (A → B) ∧ (A → C)
{% endhighlight %}
While Lean can infer the type of `h` from the goal, it is good practice 
to provide the type yourself. When you disagree with Lean, then its good chance 
to check your understanding.

Next we want to make proofs of `A → B` and `A → C`. Previously, we would 
jam that into an `And.intro` making the resulting expression dense. The tactic 
`have` allows us to introduce new assumptions into the context if we provide proofs. 
{% highlight lean %}
example (A B C : Prop) : (A → B ∧ C) → (A → B) ∧ (A → C) := by 
  intro (h : A → B ∧ C)
  have (f : A → B) := fun (a:A) => And.left (h a)
  have (g : A → C) := fun (a:A) => And.right (h a)
{% endhighlight %}
and the infoview provides the current state
{% highlight lean %}
A B C: Prop
h : A → B ∧ C
f: A → B
g: A → C
⊢ (A → B) ∧ (A → C)
{% endhighlight %}

Now just need to combine `f` and `g` with `And.intro`. Since `And.intro f g` is 
_exactly_ our goal. We use the `exact` tactic to tell Lean. 
{% highlight lean %}
example (A B C : Prop) : (A → B ∧ C) → (A → B) ∧ (A → C) := by 
  intro (h : A → B ∧ C)
  have (f : A → B) := fun (a:A) => And.left (h a)
  have (g : A → C) := fun (a:A) => And.right (h a)
  exact And.intro f g
{% endhighlight %}
The infoview celebrates with us: `Goals accomplished 🎉`. 

Another useful tactic is called `apply`. It applies a function to the goal to 
get a new goal. For example, 
{% highlight lean %}
example (a : A) (b : B) : A ∧ B := by 
  apply And.intro 
{% endhighlight %}
gives 
{% highlight lean %}
case left
a: A
b: B
⊢ A
case right
a: A
b: B
⊢ B
{% endhighlight %}
in the infoview. We can tackle each `case`. 
{% highlight lean %}
example (a : A) (b : B) : A ∧ B := by 
  apply And.intro 
  case left => exact a 
  case right => exact b
{% endhighlight %}

To simplify proofs with or elimination, Lean has the tactic `cases`. 
{% highlight lean %}
example (h : A ∨ B) : B ∨ A := by 
  cases h with 
  | inl a => exact Or.inr a
  | inr b => exact Or.inl b
{% endhighlight %}
Each line labelled with `|` is a case of or elimination. `inl` tells 
Lean you are taking the left branch of the or while `inr` is the right. 

