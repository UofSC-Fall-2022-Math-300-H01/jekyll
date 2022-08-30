---
layout: page
title: Propositional logic
nav_order: 1
has_children: true
parent: Notes
reading_estimate: true
---

## Symbolic and semantic

Human reason follows some basic patterns.

The truth of one statement is often connected to the 
truth of another statement. For example, let's take the 
following example.

**Example**. If it is cloudy outside, then I don't 
need my sunglasses. 

To understand the content of this course, the first 
thing we need to do is disentangle our thought a bit. 
There are two closely related but distinct facets of this 
example. 

There is the *truth* of the statement. Is it 
actually cloudy outside or not? Do I actually need sunglasses 
or not? Whether or not someone actually needs their 
sunglasses probably depends on the person and the 
level of cloudiness. 

In focusing on the truth of a statement, we care about 
the *semantics* of the proposition. 

Distinctly, we can also view this statement as built up 
from basic "atoms" using well-defined rules. 

In our semantic analysis, we already have broken it down into 
two separate statements that can either be truth or 
false in principal:

$A$. It is cloudy outside 

$B$. I don't need my sunglasses

Our example statement is built up from $A$ and $B$ via a 
if-then construction. It then makes sense to denote it 
by $A \Rightarrow B$. The fancy arrow $\Rightarrow$ 
stands in for the if-then. 

Thus, *symbolically* we have $A$ and $B$ and $\Rightarrow$ 
provides a way to connect them to make a new formal symbol
$$
A \Rightarrow B
$$

Symbolically, $A$ and $B$ have no infused meaning so why do we 
even consider this?

**Because symbolic manipulation can be incredibly powerful.** 
It can streamline human thought. It can be mechanized in a 
computer program. It can be converted in a game. 

For mathematicians, logical reasoning is especially important. 
When reasoning about intricate structures, it is incredibly easy to 
make a mistake. The history of mathematics is rich with such 
examples. 

To help minimize errors, mathematicians grounded their arguments
in logical deduction and fostered a culture of *rigorous proofs*. 
Let's look at a more mathematical example. 

Recall that
$$
\mathbb{N} = \lbrace 0,1,2,\ldots \rbrace
$$
is the set of *natural numbers*. A natural number $n$ is *even* if 
it can be written as $n = 2m$ for some other natural number $m$. 
A number is *odd* if is not *even*.

**Example**. Let $n$ be a natural number. If $n$ is even, then 
$n+1$ is odd. 
t
If we denote 

$A$. $n$ is even. 

$B$. $n+1$ is odd. 

then symbolically we can represent the statement as before 
$$
A \Rightarrow B
$$
But semantically this if very different than our cloudy/sunglasses 
example above. 

We start by introducing the basic structure of logical argument. 

