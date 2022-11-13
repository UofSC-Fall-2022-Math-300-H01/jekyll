---
layout: page
title: Other inductive types
nav_order: 5
has_children: false
has_toc: false
parent: Induction 
grand_parent: Notes
---

## Behind the curtain 

`Nat` is not alone. Inductive constructions 
can model a vast amount of mathematics. 

We can create the propositions `True` and `False` 
using them. 
{% highlight lean %}

inductive False : Prop where 

inductive True : Prop where 
  | intro 

{% endhighlight %}

As you can see both `False` and `True` are more 
basic than `Nat`. With `False` you have *no* ways of 
building it. With `True`, you have exactly one: `intro`. 

When building a function `f : Nat → α`, recursion told 
us we needed to specify a value of `f` for each way 
we construct a `Nat`: one for `zero` and one for each `succ n`. 
What does recursion look like here? 

{% highlight lean %}
theorem False.elim {p : Prop} (no : False) : p := no.rec 
{% endhighlight %}

`False.elim` allows us to prove anything from a proof of 
a `False`. Why? Because when using recursion on `False`, 
there is nothing to recurse over. This is exactly the 
same reasoning that exhibits a function $\varnothing \to 
X$ for any set. (The `match` syntax expects terms so the 
proof uses the recursor `rec` underlying it.) 

We can also build `And` and `Or` using inductive types.
{% highlight lean %}
inductive And (p q : Prop) : Prop where 
  | intro (left : p) (right : q) 

inductive Or (p q : Prop) : Prop where 
  | inl (h : p)
  | inr (h : q) 
{% endhighlight %}

Here are proofs of `And.left` and `And.right`. 

{% highlight lean %}
theorem And.left {p q: Prop} (h : And p q) : p := 
  match h with 
  | intro left _ => left 

theorem And.right {p q: Prop} (h : And p q) : q := 
  match h with 
  | intro _ right => right 
{% endhighlight %}

`Or.elim` becomes just another name for recursion.
{% highlight lean %}
theorem Or.elim {p q r : Prop} (h : Or p q) (h₁ : p → r) 
  (h₂ : q → r) : r :=
    match h with 
    | inl h => h₁ h 
    | inr h => h₂ h 
{% endhighlight %}

As we know from shopping, lists are also built recursively. 
{% highlight lean %}
inductive List (α : Type) where 
  | nil 
  | cons (a : α) (as : List α) 
{% endhighlight %}

We start with an empty list `nil` and we build via `cons` 
our list by adding one thing, `a:α`, at a time. 
{% highlight lean %}
def ShoppingList : List String := 
  List.cons "nuts" (List.cons "cottage cheese" 
  (List.cons "grapes" List.nil))
{% endhighlight %}
As this is cumbersome, Lean allows for familiar notation 
for lists. 
{% highlight lean %}
def ShoppingList : List String := 
  ["nuts","cottage cheese","grapes"]
{% endhighlight %}
We have the `[]` for the empty list and `a::as` to append 
`a` to the list `as`. 

We can build useful functions on `List` using recursion 
{% highlight lean %}
def Length {α : Type} (l : List α) : Nat := 
  match l with 
  | [] => 0 
  | _::as => 1 + Length as

def Join {α : Type} (l₁ l₂ : List α) : List α := 
  match l₁ with 
  | [] => l₂ 
  | a::as => a :: Join as l₂ 
{% endhighlight %}

And we can prove results, like the additivity of length, 
under join. 
{% highlight lean %}
theorem join_add_len {α : Type} {l₁ l₂ : List α} : 
  Length (Join l₁ l₂) = Length l₁ + Length l₂ := by 
    match l₁ with 
    | [] => simp [Length,Join] 
    | a::as => simp[Length]; rw [join_add_len,Nat.add_assoc]
{% endhighlight %}

