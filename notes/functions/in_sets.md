---
layout: page
title: In set theory 
nav_order: 4
has_children: false
has_toc: false
parent: Functions 
grand_parent: Notes
---

## Building functions from sets 

If we already know about sets, then we can actually construct 
functions directly. At first the definition looks a little strange. 

**Definition**. Let $X$ and $Y$ be sets. A _function_ $f : 
X \to Y$ is a subset 
$$
\Gamma \subseteq X \times Y 
$$
satisfying the condition 
$$
\forall~ x, \exists !~ (x',y) \in \Gamma, x = x' 
$$
In other words, in our subset of pairs, $\Gamma$, given an element 
$x \in X$, there is one and exactly one ordered pair of the form 
$(x,y)$. 

Given a function, $\Gamma_f$, we can define application of the 
function to an element $x \in X$ as 
$$
x \mapsto y 
$$ 
where $y$ is the unique element of $Y$ making $(x,y) \in \Gamma_f$ 
hold. 

Given a function of the familiar type $f : X \to Y$, we can make 
subset of $X \times Y$ as 
$$
\Gamma_f := \lbrace (x,f(x)) \mid x \in X \brace
$$
This is commonly called the _graph_ of $f$. 



