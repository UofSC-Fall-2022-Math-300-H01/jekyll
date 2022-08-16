---
layout: page
title: Propositions and proofs 
nav_order: 1
has_children: false
has_toc: false
parent: First order logic
grand_parent: Notes
---

## Propositions

We start with the basic building blocks of first-order logic: *propositions*. 
The collection of propositions is simply a collection of symbols. Common 
ones are based on the Roman or Greek alphabets, e.g.
$$
 A, B, C ,\ldots \\
 \alpha, \beta, \gamma, \ldots 
$$
But we could just as easily using emoji for our symbols 
<center>
😉, 🤯, 🌭, . . . 
</center>
Right now, they have no meaning attached. 

Given a set of propositions, we next need rules to combine them into expressions. 

## Deduction 

The operations we use to combine expressions will reflect oft-occuring structures 
in human reason. But, we also need to model the common steps in deduction. Here there are 
two separate roles: *assumptions* we are given and *goals* we want to establish 
(if we can). 

In the written (or natural) language, you might see. 

**Example**. If $n$ and $m$ are even integers, then so is $n-m$. 

Recall here that the *integers* are 
$$
	\mathbb{Z} = \lbrace \ldots, -2,-1,0,1,2, \ldots \rbrace
$$

This could also be written as 

**Example**. Let $n$ and $m$ be even integers. The integer $n-m$ is also an even 
integer.

While the latter example is not written an explicit if-then the content is the same. 
Our set of assumptions is $n$ and $m$ are even integers while our goal is $n-m$ 
is an even integer. 

Let's write down a proof of these statements. We can represent as a table. 

| Assumptions | Goal | 
| --- | --- |
| $n, m$ even | $n-m$ is even |

Mathematics is well-known for compact (and difficult) notation. In a proof, it is 
often valuable to unfold the definitions into the statement they represent. We perform 
this operation on the assumptions. 

| Assumptions | Goal | 
| --- | --- |
| $n = 2c$ for some integer $c$ | $n-m$ is even |
| $m = 2d$ for some integer $d$ | | 

We also rewrite the goal in the same way. 

| Assumptions | Goal | 
| --- | --- |
| $n = 2c$ for some integer $c$ | $n-m = 2e$ for some integer $e$ |
| $m = 2d$ for some integer $d$ | | 

To achieve our goal, we want to exhibit the desired $e$ using the assumptions at hand. 
To make progress, we import another "known fact" into the assumptions context: 
distribution of multiplication over subtraction.

| Assumptions | Goal | 
| --- | --- |
| $n = 2c$ for some integer $c$ | $n-m = 2e$ for some integer $e$ |
| $m = 2d$ for some integer $d$ | | 
| $u(v-w) = uv-uw$ for all integers $u,v,w$ | | 

Now we can an apply distribution with $u = 2, v = c, w = d$ to gain another statement and 
finish. 

| Assumptions | Goal | 
| --- | --- |
| $n = 2c$ for some integer $c$ | $n-m = 2e$ for some integer $e$ |
| $m = 2d$ for some integer $d$ | | 
| $u(v-w) = uv-uw$ for all integers $u,v,w$ | | 
| $n - m = 2c - 2d = 2(c-d)$ | | 
| set $e = c-d$ | |
| $n -m = 2e$ | | 

While we modeled this proof as a table, it is notationally simpler to represent deduction 
from assumption $A$ to goal $B$ (with some intermediate steps) vertically. 

{% eqn proof_tree_example %}
\begin{prooftree}
\hypo{A} \infer1{\vdots} \infer1{B}
\end{prooftree}
{% endeqn %}

And we write $A \vdash B$ to indicate that we can prove the goal(s) $B$ given the assumption(s) $A$. 
