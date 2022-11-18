---
layout: page
title: Lean's Int 
nav_order: 2
has_children: false
has_toc: false
parent: Integers 
grand_parent: Notes
---

## Two copies of Nat 

With our construction of $\mathbb{Z}$, we (eventually) get 
two copies of $\mathbb{N}$ one coming from the function
$$
i : \mathbb{N} \to \mathbb{Z}
$$
and the other from 
$$
j : \mathbb{N} \to \mathbb{Z}
$$

We can think of one copy of $\mathbb{N}$ as the non-negative 
integers and the other as the non-positive integers -- with 
their overlap being $0$. 

One can could imagine building an inductive type from this 
expressing that we have two ways to build an integer from a 
natural number. Indeed, that is what Lean does but a slight shift. 
The two copies of `Nat` in `Int` are the non-negative integers 
and the _strictly_ negative integers. 
{% highlight lean %}
inductive Int : Type where
  | ofNat   : Nat → Int
  | negSucc : Nat → Int
{% endhighlight %}

`negSucc n` should be viewed as `-n-1`. Lean gives the analog of 
$j$ above as 
{% highlight lean %}
def negOfNat : Nat → Int
  | 0      => 0
  | succ m => negSucc m
{% endhighlight %}

In Grothendieck construction of $\mathbb{Z}$, we got addition 
almost immediately since it was natural to add $\mathbb{N} \times 
\mathbb{N}$. In Lean, it requires a bit more book-keeping using 
successors when using `negSucc`.  
{% highlight lean %}
def add (m n : Int) : Int :=
  match m, n with
  | ofNat m,   ofNat n   => ofNat (m + n)
  | ofNat m,   negSucc n => subNatNat m (succ n)
  | negSucc m, ofNat n   => subNatNat n (succ m)
  | negSucc m, negSucc n => negSucc (succ (m + n))
{% endhighlight %}

On the other hand, perhaps multiplication looks simpler than the 
formula we had before. 
{% highlight lean %}
def mul (m n : Int) : Int :=
  match m, n with
  | ofNat m,   ofNat n   => ofNat (m * n)
  | ofNat m,   negSucc n => negOfNat (m * succ n)
  | negSucc m, ofNat n   => negOfNat (succ m * n)
  | negSucc m, negSucc n => ofNat (succ m * succ n)
{% endhighlight %}

