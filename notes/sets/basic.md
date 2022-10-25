---
layout: page
title: Basics 
nav_order: 1
has_children: false
has_toc: false
parent: Sets
grand_parent: Notes
---

## Sets and membership

We want to talk sensibly and precisely about collecitons 
of mathematical objects. The notion of a _set_ accomplishes 
this. 

Like when working with predicate logic, we first fix an 
universal repoository $\mathcal U$. Members of $\mathcal U$ 
are called _elements_. 

**Definition**. A _set_ $X$ is a (sub)collection of elements from 
$\mathcal U$. 

The basic operation we can perform given an element $x$ and a set 
$X$ is to ask whether $x$ is in $X$ or not, ie to check membership. 
We use the notation $x \in X$ for the predicate: $x$ is an element 
of $X$. And we use $x \not \in X$ for $\neg (x \in X)$. 

**Example**. Suppose we are talking about all the dogs that live 
in neighborhood at home. Then our universal set $\mathcal D$ is a giant 
list of every dog, perhaps identified by name. 

We can make new sets in a few ways. For example, 
$$
\text{Fritz}, \text{Herman}, \text{Sam}
$$
would form a set. We use special notation to indicate we are 
forming a set: curly braces $\lbrace ~ \rbrace$. So we would 
write the previous set of dogs 
$$
W := \lbrace \text{Fritz}, \text{Herman}, \text{Sam} \rbrace
$$
to indicate we are talking about a set of dogs. 

In building the set $W$, we explicitly listed out the members of the 
set. Depending on the time and page length, this might not be feasible 
in general. Suppose that all the stars of the Air Bud franchise 
lived in the neighborhood. Then, without confusion, we can label 
each lead golden retriever with corresponding movie. If I wanted a 
set consisting of all the stars of Air Bud. Often, we are bit 
lazier in writing down a set. For example 
$$
AB := \lbrace \text{Air Bud}, \text{Air Bud: Golden Retriever}, \ldots, 
\text{Santa Paws 2: The Santa Pups} \rbrace
$$
We wrote out the first few elements of the set and the last one 
and we expect people to infer the rest from context. People would 
know for instance that 
$$
\text{Air Buddy} \in AB
$$
and 
$$
\text{Lassie} \not \in AB
$$
(Admittedly, this works better when talking about more rigid things like numbers. 
Most people could guess that 
$$
\lbrace 1, 2, 3, \ldots, 9, 10 \rbrace 
$$
is the set of natural numbers between 1 and 10.)

The final common way to make a set is by specifying a condition that 
must hold as the condition for membership in that set. 
$$
D := \lbrace d \mid d \text{ is a weiner dog} \rbrace
$$
denotes the set consisting of dogs in our universal set (in the neighborhood) that 
are dachshunds. So $d \in D$ if and only if $d$ is a weiner dog. 

Perhaps $D$ is too large and we are only concerned with weiner dogs owned by 
my grandmother. 
$$
GD := \lbrace d \in D \mid d \text{ is owned by my grandma} \rbrace
$$
So $GD$ consists of the weiner dogs that are also owned by my grandmother. So 
to check the $d \in GD$ we would have to verify that both 
- $d$ is a weiner dog and 
- $d$ is my grandma's dog 

It turns out that 
$$
\text{Fritz} \in GD \\
\text{Herman} \in GD \\
\text{Sam} \in GD 
$$
and there are no other weiner dogs that my grandmother owns. Both $W$ and $GD$ 
consist of exactly the same collection of elements so they are equal sets 
$$
W = GD
$$

The equality is an incarnation of a general principle called _set extensionality_. 

**Set Extensionality**. Two sets $X$ and $Y$ are equal if and only if $X$ and $Y$ 
have the same elements. We can express this using a logical formula 
$$
X = Y \leftrightarrow \forall z~ (z \in X \leftrightarrow z \in Y) 
$$

Extensionality of sets provides the fundamental way of checking two sets are equal.

**Example**. Consider the two sets 
$$
X = \{2,3,5,7\} 
$$
and 
$$
Y = \{n \in \mathbb{N} \mid n \text{ is prime and } n < 10 \}
$$

The two sets are in fact equal. To show this, we prove that 
$$
\forall n~ (n \in X \leftrightarrow n \in Y)
$$
Remember to introduce a universal quantifier, we need to prove 
$n \in X \leftrightarrow n \in Y$ where $n$ is now free. 

To introduce a bi-implication, we need two proofs. One of $n \in X \to n \in Y$ and 
one of $n \in Y \to n \in X$. 

We first prove that $n \in X \to n \in Y$. To introduce an implication, we assume 
that $n \in X$ is true and check that $n \in Y$. So assume that 
$$
n \in X = \lbrace 2,3,5,7 \rbrace 
$$
We want to prove that $n \in Y$. The claim of membership $n \in Y$ is equivalent to 
$n$ satisfying the predicate 
$$
n \text{ is prime and } < 10 
$$
So to show that $n \in Y$ we check truth of the predicate. We can do this case by case. 
If $n = 2$, then $n$ is prime because the only natural number that divides it is $1$ 
and $n < 10$. If $n = 3$, then $n$ is prime and $n < 10$. If $n = 5$, then $n$ is prime 
and $n < 10$. If $n = 7$, then $n$ is prime and $n < 10$. Thus, if $n \in X$, then $n 
\in Y$. 

Next we assume that $n \in Y$ and our goal is to show that $n \in X$. Assume that 
$n \in Y$. This is the same as saying that $n$ is prime and $n < 10$. We know the list 
of natural numbers less that than $10$ is 
$$
0,1,2,3,4,5,6,7,8,9
$$
So far this is larger than $X$; it has $X$ but it also has more elements. We check 
which of these are prime to see which are elements are actually in $Y$. We go case 
by case. If $n = 0$, then $0 = 2 \cdot 0$, so $2 \mid 0$ and $0$ is not prime. 
If $n = 4$, then $4 = 2 \cdot 2$ so $4$ is not prime. If $n=6$, then $6 = 2 \cdot 3$ 
so $6$ is not prime. $8 = 2 \cdot 4$ so $8$ is not prime. $9 = 3 \cdot 3$ so $9$ 
is not prime. Thus, the only elements that could be in $Y$ are $2,3,5,7$, ie 
$n \in Y \to n \in X$. 

**Definition**. We say $X$ is a _subset_ of $X$ if $\forall x~ (x \in X \to x \in Y)$. 
In other words, every element of $X$ is also an element of $Y$. We write $X \subseteq 
Y$ is $X$ is a subset of $Y$. If $X \subseteq Y$ and $ X \not = Y$, then we write 
$X \subset Y$. 

Note that this means we can express extensionality as $X = Y$ if and only if $X \subseteq Y$ 
and $Y \subseteq X$.

Recall that $\mathbb{R}$ is the set of _real numbers_. These numbers are represented by 
points on an infinite line and should be familiar from calculus. (This is not a precise 
definition.)

**Example**. Consider the sets 
$$
[0,1] := \lbrace x \in \mathbb{R} \mid 0 \leq x \leq 1 \rbrace \\
(0,1] := \lbrace x \in \mathbb{R} \mid 0 < x \leq 1 \rbrace \\
\lbrack 0,1) := \lbrace x \in \mathbb{R} \mid 0 \leq x < 1 \rbrace \\
(0,1) := \lbrace x \in \mathbb{R} \mid 0 < x < 1 \rbrace 
$$

Then 
$$
[0,1] \supseteq (0,1] \supseteq (0,1) \\
\lbrack 0,1] \supseteq [0,1) \supseteq (0,1) \\
(0,1] \nsubseteq [0,1) \\
\lbrack 0,1) \nsubseteq (0,1]
$$
