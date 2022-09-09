---
layout: page
title: Logical formulas 
nav_order: 2
has_children: false
has_toc: false
parent: Lean  
grand_parent: Notes
---

## Propositions in Lean  

The engine that makes Lean interactive theorem verifier and prover is 
the idea that every piece of data has a type. This include mathematical 
data. So the natural numbers have (are) a type `Nat` as are the real numbers. 
Individual natural numbers are called _terms_ of type `Nat`. To 
express this relationship, we write `5: Nat`. If you know a little set 
theory, it will be harmless to imagine replacing the semi-colon with an 
element symbol $\in$. 

Lean has type for propositions called `Prop`. We can think of this as the 
whole universe of possible propositions. A term of `Prop` is a individual 
proposition.

Suppose I have propositional variables $A,B,C$ in my logic. How do 
I tell Lean about them? We declare them as variables.

{% highlight lean %}
variable (A B C : Prop) 
{% endhighlight %}

A useful tool built into the system is the ability to check what 
Lean believes an expression means. 

{% highlight lean %}
variable (D : Prop)
#check D 
{% endhighlight %}

The window pane on the right hand side of the editor reports `D: Prop` 
which Lean reporting back that indeed it thinks `D` is a proposition. 

Next we can combine propositional variables into formulas.

## Connectives 

Let's see how each of our connectives, $\neg, \to, \lor, \land,$ and 
$\leftrightarrow$ are encoded in Lean. 

Here is negation 
{% highlight lean %}
variable (A : Prop)
#check ¬ A 
{% endhighlight %}
Lean tells that indeed `¬ A : Prop`. Note that ¬ is a Unicode symbol 
(like emoji). In general, we do not have those on our keyboard but 
the editor nows how to fill it in if we type `\neg` and hit the spacebar.

Unicode is pretty but we can also use standard (ASCII) characters to 
access negation. 
{% highlight lean %}
variable (A : Prop)
#check Not A 
{% endhighlight %}
will also report `¬ A : Prop`. 

We mentioned that everything in Lean has a type. What about Not? Checking 
it returns `Not : Prop → Prop`. If we interpret this (Unicode) arrow as 
an assignment, this makes sense. Given a formula `X`, `¬ X` is another one.

Next, we turn to implication, $\to$. It has the same Unicode arrow (
typeset as `\to`) 
{% highlight lean %}
variable (A B : Prop)
#check A → B
{% endhighlight %}
gives that `A → B : Prop`. 

For conjunction, $\land$, we have (at least) three notations that all 
work:
{% highlight lean %}
variable (A B : Prop)
#check A ∧ B
#check And A B 
#check A /\ B
{% endhighlight %}
Here `∧` is typed using `\and`. 

Next we have disjunction. 
{% highlight lean %}
variable (A B : Prop)
#check A ∨ B /- typed as \or -/
#check Or A B 
#check A \/ B
{% endhighlight %}
Note the text between `/- -/`. This tells Lean that to ignore the what is 
written. They are only comments and not commands.  

Finally, bi-implication.
{% highlight lean %}
variable (A B : Prop)
#check A ↔ B /- typed as \iff -/
#check Iff A B 
{% endhighlight %}

Aside from negation, all of the other connectives take in two formulas and 
yield a single one. So if you `#check Iff` you will get `Iff : Prop → Prop 
→ Prop`. What happens if you `#check ↔`? 
