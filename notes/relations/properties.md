---
layout: page
title: Useful properties
nav_order: 2
has_children: false
has_toc: false
parent: Relations 
grand_parent: Notes
---

## Properties of relations

Looking at the examples from [before]({% link notes/relations/basic.md %}), 
we can identify some useful properties can satisfy. 

**Definition**. Let $\sim$ be a relation. 
We say that $\sim$ is _reflexive_ if 
$$
\forall~ x, x \sim x 
$$
In other words, every $x$ is related to itself. If $R_\sim$ is the 
subset corresponding to $\sim$, then reflexivity is equivalent to 
$$
\Delta_U \subseteq R_\sim
$$
We say that $\sim$ is _irreflexive_
$$
\forall~ x, \neg (x \sim x)
$$

Equality is reflexive as is divisibility. But $ < $ is irreflexive. 

**Definition**. Let $\sim$ be a relation. 
We say that $\sim$ is _symmetric_ if 
$$
\forall~ x,y, x \sim y \to y \sim x  
$$
In other words, if $x$ is related to $y$, then $y$ is also related to $x$.

Again equality is symmetric but divisibility and $ < $ is not. To 
capture the behavior of $ < $, we have the following notion.

**Definition**. We say that $\sim$ is _asymmetric_ if 
$$
\forall~ x,y, x \sim y \to y \sim x \to x=y
$$
So if both $x$ is related $y$ and $y$ is related to $x$, then in fact 
they have to be equal.

$ < $ and $\subseteq$ are examples of asymmetric relations. Note 
that any relation that is symmetric and asymmetric is very close to 
equality. In particular if $x \sim y$ then we must have $x = y$. 

**Definition**. Let $\sim$ be a relation. We say that $\sim$ is 
_transitive_ if 
$$
\forall~ x,y,z, x \sim y \to y \sim z \to x \sim z
$$
In other words, if $x$ is related to $y$ and $y$ is related to $z$, then 
we know that $x$ is related to $z$. 

Equality, divisibility, and $ < $ are all transitive. 
