---
layout: page
title: Proofs and our first rules
nav_order: 3
has_children: false
has_toc: false
parent: Lean  
grand_parent: Notes
---

## Proofs 

I said everything in Lean has a type. What is the type of a 
proof of a formula `X : Prop`? Let's call the proof `h`. 

Well, its type is `X` itself. In addition to being a term in 
the (big) type of `Prop`, `X` is itself a type whose terms 
are proofs of `X`.

We can of course declare we have a proof (without providing 
one) by saying
{% highlight lean %}
variable (A : Prop) 
variable (h : A)
{% endhighlight %}

But far more important for us is _producing_ proofs! 

Before we look at some basic examples, let's introduce two new 
keywords for Lean: `example` and `theorem`. Both of these tell 
Lean that we want to produce a proof for a particular proposition. 
Here are some examples:

{% highlight lean %}
variable (A : Prop) 
example : A := sorry 
theorem bigOne : A := sorry
{% endhighlight %}

The main difference between `example` and `theorem` is that `theorem` 
expects a name whereas `example` does not.

Each of these is telling Lean that I am going to provide a proof 
of `A`. This is why we end the statement with `: A`. It is informing 
Lean the type of the coming proof. 

The proof goes after `:=`. `sorry` is a special command 
that decreases the volume of the complaints from Lean that we 
did not actually provide a proof. If we remove `sorry`, we notice 
that the message is in red now: `unexpected end of input`. 

Messages like these from the infoview pane are meant to be helpful 
in constructing our proofs but they can be cryptic. A good rule is 
to step back a little and meditate on the error message in the 
context of the question. 

In general, we cannot produce a proof out of nothing except for 
situations. Even so, they are instructive to investigate. 

Suppose I want to establish $A \vdash A$. This is trivial in 
propositional logic: I have $A$ so I have $A$. How does this 
look in Lean?

For examples/theorems, we can put the assumptions on the left-hand 
side of the semi-colon. 

{% highlight lean %}
example (h : A) : A := sorry 
{% endhighlight %}

This reads as: "assume I have a proof `h` of `A` and I want to prove `A`".
A completed proof is:

{% highlight lean %}
example (h : A) : A := h 
{% endhighlight %}

You are providing the assumed proof of `A` as the desired proof of `A`.

A formula we can always prove is $\top$. In Lean, this proposition is called 
`True` and $\bot$ goes by `False`. 

The introduction rule for `True` comes in the form of a canonical proof 
called `true` of type `True`. 

## Implication elimination and introduction

Our rules of inference allowed us to build more complicated proofs from some 
basic steps. Each rule is encoded in Lean. Let's start by looking at the 
introduction and elimination rules for implication. 

Say we have `A B : Prop` and we want to prove `B` from `A → B` and `A`. This 
is done as 
{% highlight lean %}
variable (A B : Prop) 
example (f : A → B) (h : A) : B := f h
{% endhighlight %}

What is going on here? `h` is a proof of `A` as before and `f` is a proof 
of `A → B`. What is a proof of `A → B`? Well, one way to understand it is 
as a way to turn a proof of `A` into a proof `B`. We generally call such 
things _functions_. 

By placing `f h`, we are saying "feed `h` into `f` and use the output". A more 
common way to say it is that we _applied_ `f` to `h`. 

Application of `f` of `h` is how $\to$-elimination is implemented in Lean. 

Next we look at $\to$-introduction. For example, how would we finish the following?
{% highlight lean %}
variable (A : Prop)
example : A → A := sorry
{% endhighlight %}

This difference between this example and 
{% highlight lean %}
example (h : A) : A := h 
{% endhighlight %}
is the exactly the elimination rule for implication. 

We want to make a function `f : A → A` which mimics our intitution that given a 
proof `h : A` that we can output that given proof to get a proof of `A`. 

The syntax for doing so is seen below in the completed example. 
{% highlight lean %}
variable (A : Prop)
example : A → A := fun (h:A) => h
{% endhighlight %}
`fun` tells Lean that a function is coming `(h : A)` specifies the input (and its 
type). The arrow `=>` separates the input from the output.

Strictly speaking this is not the implication introduction rule but it plays an 
important part. 
{% highlight lean %}
variable {A B : Prop} 
theorem superProof (h : A) : B := sorry 
example : A → B := fun (h : A) => superProof h
{% endhighlight %}
We can treat the (nonexistent) proof of our theorem as a function. 

But you may have noticed the braces `{ A B : Prop }`. When we declare `(A : Prop)`, 
Lean adds it as an assumption to all examples/theorems in our file. So really 
superProof has the form 
{% highlight lean %}
theorem {A B : Prop} superProof (h : A) : B := sorry 
{% endhighlight %}
Using the parentheses `(A B : Prop)` tells Lean that I want `A` and `B` to also be (explicit) 
inputs to `superProof`. (When we saying `variable` to Lean, it really goes all out.)

Using the braces `{A B : Prop}` tells Lean "you figure out `A` and `B`" from the 
other information. Which is can do in the case of our example from the desired type is 
`A → B`. 
