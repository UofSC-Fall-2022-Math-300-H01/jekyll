---
layout: page
title: Examples 
nav_order: 5
has_children: false
has_toc: false
parent: Predicate logic
grand_parent: Notes
---

## Example proofs and non-proofs

With quantifiers, functions, and equality, we have a greater richness of 
expression. Since each of the symbols mimics standard rhetorical techniques, 
we still recognize some common patterns as encapsulated via provable formula.

## Order of quantifiers

Can we prove 
$$
 \forall y~ \exists x~ A(x,y) \to \exists x~ \forall y~ A(x,y)
$$
in general?

To approach this, it makes sense to try to find a simple model and figure it 
the statement is true. Let's take $\mathbb{N}$ and interpret $A(x,y)$ as 
$x=y$. Then, in natural language, the head of the implication says that for 
any number $y$ there is some other number $x$ such that $x=y$. This of course 
is always true! We can take our desired $y$ to be $x$. 

The tail of the implication says that there is a single number $x$ such that 
for every number $y$ we have $x=y$. This is clearly false as not all numbers are 
equal. 

Thus, this formula cannot be proven. We cannot exchange quantifiers 
thoughtlessly.

Is the other direction provable? Our initution from the particular in 
encouraging and in fact it is. 

{% eqn move_forall_past_exists %}
\begin{prooftree}
\infer0[\normalsize 1]{\exists x~ \forall y~ A(x,y)} 
\infer0[\normalsize 0]{\forall v~ A(u,v)} 
\infer1{A(u,v)}
\infer1{\exists u~ A(u,v)}
\infer2[\normalsize 0]{\exists u~ A(u,v)}
\infer1{\forall v~ \exists u~ A(u,v)}
\infer1[\normalsize 1]{\exists x~ \forall y~ A(x,y) \to 
\forall v~ \exists u~ A(u,v)}
\end{prooftree}
{% endeqn %}
We use new variable labels to make things clear. The intuition of the proof here 
says that we can the witness of the first existential quantifier as the witness of 
the second. 

We can freely exchange the same quantifiers. Below is a proof of 
$ \forall x~ \forall y~ A(x,y) \vdash \forall y~ \forall x~ A(x,y)$. 
{% eqn swap_foralls %}
\begin{prooftree}
\hypo{\forall x~ \forall y~ A(x,y)}
\infer1{\forall y~ A(x,y)}
\infer1{A(x,y)}
\infer1{\forall x~ A(x,y)}
\infer1{\forall y~ \forall x~ A(x,y)}
\end{prooftree}
{% endeqn %}

Similiarly, we can exchange existential quantifiers. 
{% eqn swap_existss %}
\begin{prooftree}
\hypo{\exists x~ \exists y~ A(x,y)}
\infer0[\normalsize 1]{\exists y~ A(x,y)}
\infer0[\normalsize 0]{A(x,y)}
\infer1{\exists u~ A(u,y)}
\infer2[\normalsize 0]{\exists u~ A(u,y)}
\infer1{\exists v~ \exists u~ A(u,v)}
\infer2[\normalsize 1]{\exists v~ \exists u~ A(u,v)}
\end{prooftree}
{% endeqn %}

Given this we often write $\forall x~ y$ in place of $\forall x~ \forall y~$ and 
$\exists x~ y$ for $\exists x~ \exists y$ to shorten notation. 

## Negation and quantifiers

We have seen how to exchange $\neg$ and other connectives like $\land$ and $\lor$. 

Let's try to understand $\neg (\exists x~ A(x))$. This is saying no matter what the 
value of $x$ is $A(x)$ should not be true. That looks much like $\forall x~ \neg 
A(x)$. This also comports with our analogy between $\forall$ and $\land$ and $\exists$ 
and $\lor$. Let's try to give a proof. 

{% eqn negation_of_existential %}
\begin{prooftree}
\infer0[\normalsize 3]{\neg \exists x~ A(x)}
\infer0[\normalsize 0]{A(x)}
\infer1{\exists x~ A(x)}
\infer2{\bot} 
\infer1[\normalsize 0]{\neg A(x)}
\infer1{\forall x~ \neg A(x)} 
\infer0[\normalsize 2]{\exists x~ A(x)}
\infer0[\normalsize 1]{A(u)}
\infer0[\normalsize 3]{\forall x~ \neg A(x)}
\infer1{\neg A(u)}
\infer2{\bot}
\infer2[\normalsize 1]{\bot}
\infer1[\normalsize 2]{\neg \exists u~ A(u)} 
\infer2[\normalsize 3]{\neg \exists x~ A(x) \leftrightarrow \forall x~ \neg A(x)}
\end{prooftree}
{% endeqn %}

Similarly, $\neg \forall x~ A(x) \leftrightarrow \exists x~ \neg A(x)$ is a valid formula. 
In fact, we have already been using this logical pattern in our arguments. It is usually 
called finding a _counter-example_. The counter-example being the witness to $\exists x~ 
\neg A(x)$.

## Quantifiers and con/disjunction 

From our analogy between $\forall$ and $\land$ and $\exists$ and $\lor$, we can guess at the 
behavior when quantifiers and con/disjunction interact. 

Indeed, the following are all valid formula. 
$$
\forall x~ (A(x) \land B(x)) \leftrightarrow \forall x~ A(x) \land \forall x~ B(x) \\
\exists x~ (A(x) \lor B(x)) \leftrightarrow \exists x~ A(x) \lor \exists x~ B(x) 
$$

