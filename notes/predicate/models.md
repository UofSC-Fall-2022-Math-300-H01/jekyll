---
layout: page
title: Soundness and completeness 
nav_order: 4
has_children: false
has_toc: false
parent: Predicate logic
grand_parent: Notes
---

## Models for predicate logic

Before we dive into proving statements in predicate logic, we 
equip ourselves with a useful tool to decide if a formula is 
_not_ provable. 

For propositional logic, we used truth assignments and truth 
tables as a quick tool to establish the lack of a proof. This 
was only possible because we established soundness of truth 
assignments: if we could establish $X \vdash Y$, then we know that 
$X \models Y$, ie every truth assignment that makes $X$ true will 
also make $Y$ true.

Propositions are simpler than predicates though. For predicate 
logic, the interpretations have more moving parts. Our domain of 
discourse, or source for inputs of the variables, needs to be 
assigned a concrete set of values. For example, we could consider 
$\mathbb{N}$ as our concrete set. Then, each function $f(x)$ 
should get assigned to a function whose inputs are from $\mathbb{N}$ 
and whose outputs lie in $\mathbb{N}$, like $f(x) = x+1$.

Each predicate $A(x)$ may be true for some numbers $x$ and 
false for others. Thus, we need to assign a set of values for 
which $A(x)$ is true and assign false for the others. For example, 
we could assign $A(x)$ to the set of even natural numbers. Meaning, 
$A(x)$ is true for $x$ even and false $x$ odd.

Remember that predicate logic is purely about symbolic manipulation 
respecting a set of rules. Through models, we imbue some meaning 
and familiarity to the symbols. 

Our rules for propogating truth and falsity through our familiar 
connectives $\to, \land, \lor, \neg, \leftrightarrow$. We need 
ways to assign values to $\forall$ and $\exists$. 

These are built into the motivations for these symbols. We declare 
that $\forall x~ A(x)$ evaluates to true if $A(x)$ is true for all 
values of $x$ in our model. It is false otherwise. For example, 
we if use $\mathbb{N}$ and interpret $A(x)$ to be $x > 5$. Then, 
$\forall x~ A(x)$ would evaluate to false. But if we interpret 
$A(x)$ to be $x^2-x \geq 0$ then we would get true. 

Similarly, $\exists x~ A(x)$ evaluates to true if there at least one 
value in our model making $A(x)$ true and is otherwise false. 

## Soundness 

With our more complex models, we can extend $X \models Y$ to 
predicate logic.

**Definition**. We say that a formula $Y$ is a _logical consequence_ 
of a formula $X$ if, in any model, whenever $X$ is true, then $Y$ is 
true. 

So to show that $X \not \models Y$ we just need to locate _one_ model 
where $X$ evaluates to true while $Y$ to value for some value. 

Predicate logic is _sound_ similar to propositional logic. 

**Theorem**. If $X \vdash Y$, then $X \models Y$. 

Like with propositional logic, this gives a powerful means to check 
that $X \not \vdash Y$: just find one model demonstrating $X \not 
\models Y$. 

## Completeness 

Amazingly, the converse of the previous theorem continues to hold. 

**Theorem**. If $X \models Y$, then $X \vdash Y$.

Completeness of predicate logic is more involved than that for propositional 
logic. It was first proven by Kurt Gödel in his 1929 thesis. We won't 
go into any details and will not use completeness in any way moving 
forward. But, hopefully, you are well equiped to appreciate the statement. 
