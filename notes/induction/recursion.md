---
layout: page
title: Recursion
nav_order: 2
has_children: false
has_toc: false
parent: Induction 
grand_parent: Notes
---

## Working with Peano $~\mathbb{N}$

We already know a good deal about the natural numbers from life 
but how do we work with Peano natural numbers. The answer 
is recursion. 

**Theorem**. Let $Y$ be a set. For all $y \in Y$ and 
$h : \mathbb{N} \times Y \to Y$, there is a unique function 
$f : \mathbb{N} \to Y$ such that $f(0) = y$ and $f(s(n)) = 
h(s(n),f(n))$ for all $n \in \mathbb{N}$. 

{% proof %}
For an natural number of the form $0$ or $s(n)$ for some 
other natural number where we know $f(n)$, we can define $f$ 
directly. 
$$
\begin{aligned}
f(0) & := y \\
f(s(n)) & := h(s(n),f(n)) \text{ whenever $f(n)$ is defined }
\end{aligned}
$$
Is this a definition for every $n \in \mathbb{N}$? 

Let 
$$
X := \lbrace n \in \mathbb{N} \mid f(n) \text{ is defined} \rbrace 
$$
Then $0 \in X$. And, if $n \in X$, then $s(n) \in X$ from 
the definition of $f$. Peano's last axiom says that $\mathbb{N} \subseteq 
X$. Of course, in this case, $X \subseteq \mathbb{N}$. So 
$X = \mathbb{N}$ and $f(n)$ is defined for all $n$. 

Now we turn to uniqueness of $f$. Assume we have two 
different functions $f,g : \mathbb{N} \to Y$ satisfying 
the conditions of the theorem and set 
$$
X := \lbrace n \in \mathbb{N} \mid f(n) = g(n)
$$
Then $0 \in X$ since $f(0) = y = g(0)$. Assume that 
$n \in X$, so $f(n) = g(n)$. Then, 
$$
f(s(n)) = h(s(n),f(n)) = h(s(n),g(n)) = g(s(n))
$$
so $s(n) \in X$. Thus, $\mathbb{N} = X$ as before and 
$f = g$. 
{% endproof %}

Now, let's see what this means and how 
to use it. The function $h$ allows for any way to combine the natural 
number $s(n)$ and value, we already know, for $f(n)$. 

**Example**. Suppose $Y = \mathbb{N}$. Let's take our initial 
value to $1$. And let $h(n,m) = nm$, the product of $n$ and $m$.

Then we want a function $f: \mathbb{N} \to \mathbb{N}$ which 
satisfies 
- $f(0) = 1$ and 
- $f(n+1) = (n+1)f(n)$ 

The function that satisfies this is the factorial $n \mapsto n!$. 
We write the value $n!$ purely in terms of $n$ alone:
$$
n! = n \cdot (n-1) \cdot (n-2) \cdot \cdots 2 \cdot 1 
$$
Writing function defined via recursion this way is called its 
_closed form_.

In Lean, we can build factorial as 
{% highlight lean %}
def Factorial (n : Nat) : Nat := 
  match n with 
  | 0 => 1 
  | m+1 => (m+1)*(Factorial m)
{% endhighlight %}
The `match n with` tells Lean consider the different ways we can get 
a natural number from its constructors. Either we have `0` or 
the number is a successor `n = m+1`. In each case, we have provided a 
value output by `Factorial`. 

We see also that Lean knows that `0` really means `zero` and `n+1` is 
`succ n`. We might also overlook that we used multiplication of 
natural numbers. Lean knows multiplication already but what did someone 
tell it. 
{% highlight lean %}
def Mult (n m : Nat) : Nat := 
  match n, m with 
  | _, 0 => 0 
  | _, m+1 => Mult n m + n  
{% endhighlight %}
We use $n(m+1) = nm + n$ to _define_ multiplication recursively. 

But now you might have noticed that we added terms of `Nat`. What is addition? 
{% highlight lean %}
def Plus : Nat → Nat → Nat 
  | n, Nat.zero => n 
  | n, Nat.succ m => Nat.succ (Plus n m) 
{% endhighlight %}
where we explicitly used `Nat.zero` and `Nat.succ`. 

You can find the actual definitions of addition and multiplication in `Nat` 
under `Nat.add` and `Nat.mul`. 

We can check that with our definition `Plus n 1 = Nat.succ n` for all `n`. 
{% highlight lean %}
theorem plus_one_eq_succ (n : Nat) : Plus n 1 = Nat.succ n := by rfl 
{% endhighlight %}

If we try the other order for adding one, you get the following error. 
{% highlight lean %}
theorem one_plus_eq_succ (n : Nat) : Plus 1 n = Nat.succ n := by rfl 
tactic 'rfl' failed, equality lhs
  Plus 1 n
is not definitionally equal to rhs
  Nat.succ n
{% endhighlight %}
Why is this? As a hint, we try to break it into the cases for constructing 
`n`. 
{% highlight lean %}
theorem one_plus_eq_succ (n : Nat) : Plus 1 n = Nat.succ n :=  
  match n with 
  | 0 => by rfl -- ok 
  | Nat.succ m => by rfl 
tactic 'rfl' failed, equality lhs
  Plus 1 (Nat.succ m)
is not definitionally equal to rhs
  Nat.succ (Nat.succ m)
{% endhighlight %}
If we look at the definition we have 
{% highlight lean %}
Plus 1 (Nat.succ m) = Nat.Succ (Plus 1 m)
{% endhighlight %}
These are not the same! But we can use the proof for case of `m` to 
finish. We rewrite the right-hand side of the goal using `Plus 1 m = 
Nat.succ m`. Then Lean sees defintional equality.  
{% highlight lean %}
theorem one_plus_eq_succ (n : Nat) : Plus 1 n = Nat.succ n :=  
  match n with 
  | 0 => by rfl 
  | Nat.succ m => by 
    conv => rhs rw[←one_plus_eq_succ m] 
{% endhighlight %}
This is the our first encounter with induction. 
