---
layout: page
title: Groups
nav_order: 4
has_children: false
has_toc: false
parent: Integers 
grand_parent: Notes
---

## What are $~\mathbb{Z}~$ and $~\mathbb{Z}/m\mathbb{Z}~$ really? 

We make $\mathbb{Z}$ from $\mathbb{N}$ to have the benefit of 
undoing addition. Usually we think of subtraction as undoing 
addition but subtraction is just addition of negative numbers. 

To get to $\mathbb{Z}$, we take each $n \in \mathbb{N}$ and we 
"create" a new element $-n$ that is characterized by the property
$$
n + (-n) = 0 = (-n) + n
$$
We've seen how to do this via a quotient of $\mathbb{N} \times \mathbb{N}$ 
by an equivalence relation and via inductive types in Lean. 

The structure of $(\mathbb{Z},+)$ is a particular instance of a 
general notion of a _group_. 

**Definition**. A group is a triple of data $(G,\cdot,e)$ consisting 
of 
- a set $G$, 
- a binary operation $\cdot : G \times G \to G$, and 
- an element $e \in G$ 

which together satisfy the following conditions:
- $\cdot$ is associative: $a \cdot (b \cdot c) = (a \cdot b) \cdot c$
- evaluating $\cdot$ on $e$ is the identity function (on either 
side): $a \cdot e = e \cdot a = a$ 
- and there exists inverses: for each $a \in G$ there is some $b \in G$ 
with $a \cdot b = b \cdot a = e$. 

Often when $\cdot$ and $e$ are clear from the context we just use the 
underlying set $G$ to refer to a group. The element $e \in G$ is called 
the _identity element_ of $G$. 

**Example**. $\mathbb{Z}$ is a group under addition where $\mathbb{N}$ 
is not a group under addition. The defect with $\mathbb{N}$ is the lack 
of additive inverses which is rectified by passage to $\mathbb{Z}$. 

**Example**. $\mathbb{Z}/m\mathbb{Z}$ is group for all $m$ under 
modular addition. For associativity, we can use that for $\mathbb{Z}$: 
$$
[n] + ([m] + [k]) = [n] + [m+k] = [n+(m+k)] \\ = [(n+m)+k] = [n+m] + [k] = 
([n] + [m]) + [k] 
$$
The identity element of $\mathbb{Z}/m\mathbb{Z}$ is the equivalence class 
of $0$. 

We can see that $[-n]$ is the inverse to $[n]$ since 
$$
[n] + [-n] = [n+(-n)] = [0] = [(-n)+n] = [-n] + [n] 
$$
But in $\mathbb{Z}/m\mathbb{Z}$ there are more efficient choices for 
representative of the equivalence class of the inverse. For example, 
assume we start with $0 \leq n < m$. Then
$$
[n] + [m-n] = [m] = [0] = [m] = [m-n] + [n]
$$
so $m-n$ is another representative for $[-n]$ and it satisfies 
$0 < m - n \leq m$. 

**Example**. The integers are _not_ a group under multiplication because 
for a general $n \in \mathbb{Z}$, there is no $m$ with $nm = 1$. 

**Theorem**. Let $X$ be a set. Then the set of all self-bijections of 
$X$ is a group under composition. 

{% proof %}
We have seen that function composition is associative. 

The identity element is the identity function $\operatorname{id}_X$. 
Composition with the identity function returns the original function. 

We have already seen that $f: X \to X$ is a bijection if and only 
if it has a inverse $g: X \to X$, ie a function $g$ such that $g \circ 
f = f \circ g = \operatorname{id}$. So we have inverses. 
{% endproof %}

**Definition**. Let $X$ be a set. The _symmetric group_ on $X$, denoted 
$S_X$, is set of all self-bijections of $X$ under composition.  

**Example**. Let's take the symmetric group of the set $\lbrace 0,1,2,3\rbrace$. 
We can represent an element $f: \lbrace 0,1,2,3 \rbrace \to \lbrace 0,1,2,3 
\rbrace$ as a list 
$$
f \mapsto f(0) f(1) f(2) f(3) 
$$
without losing any information. Thus, $1032$ would be the function that swaps 
$0$ and $1$ and swaps $2$ and $3$. 

The symmetric group behaves a way that might be unexpected from the examples 
above. Let's compose $0321$ and $1023$ in the two orders: 
$$
0321 \circ 1023 = 3021 \\
1023 \circ 0321 = 1320 
$$
Note that $3021 \neq 1320$. In the symmetric group, the order of applying the 
group operation matters whereas in $\mathbb{Z}$ or $\mathbb{Z}/m\mathbb{Z}$ 
it doesn't. 

**Definition**. We say a group $G$ is a _commutative_ or _abelian_ if 
$a \cdot b = b \cdot a$ for all $a,b \in G$. 

If $X$ has more than two elements, then $S_X$ is never abelian.

The symmetric group is, as the name suggests, the group of symmetries of the 
underlying set. More generally, given a set with extra mathematical structure, it is 
very natural to consider the set of self-bijections that perserve the structure. 
These also form groups. 

**Example**. Let's consider functions $f : \mathbb{Z} \to \mathbb{Z}$ which 
preserve addition and satisfy $f(0) = 0$. Then, for positive $n$, since $n = 1 + 
\cdots + 1$, we have 
$$ 
f(n) = f(1 + \cdots + 1) = f(1) + \cdots + f(1) = nf(1) 
$$
For $-n$, we have 
$$
f(n) + f(-n) = f(n + (-n)) = f(0) = 0 
$$
so $f(-n) = -f(n)$ and $f$ is completely determined by the value $f(1)$. 

What can $f(1)$ be for $f$ to be a bijection? If $f(1) = 0$, then $f(n) = 0$ for all
$n$. Not so good. 

For $f$ to be surjective, we need to be able to write every integer as a multiple of 
$f(1)$. In other words, $f(1)$ has to divide $n$ for all $n \in \mathbb{Z}$. This 
forces $f(1) = \pm 1$. 

So the set of symmetries $\mathbb{Z}$ under addition is a two element set given by 
the identity function and the negative function $n \mapsto -n$. This is rather 
small compared to the symmetric group of $\mathbb{Z}$ the set which is infinite. 

There are the same number of symmetries of $(\mathbb{Z},+)$ as there are elements of 
the group $\mathbb{Z}/2\mathbb{Z}$: two. Are they the same group? 

On its face, the answer is no but there is a natural way to loosen equality. 

**Definition**. Let $G$ and $H$ be groups. An _homomorphism_ of groups is a 
function $\phi : G \to H$ such 
- $\phi(e_G) = e_H$ and 
- $\phi(a\cdot b) = \phi(a) \cdot \phi(b)$

An _isomorphism_ is a bijective homomomorphism. If $G = H$, we call an isomorphism 
an _automorphism_. 

Above we computed the automorphism group of $(\mathbb{Z},+)$. It is in fact 
isomorphic to $\mathbb{Z}/2\mathbb{Z}$ using the function 
$$
[0] \mapsto \operatorname{id}_{\mathbb{Z}} ~,~
[1] \mapsto (n \mapsto -n) 
$$
You should use the definitions above to check that this indeed is a homomorphism. 

Understanding the structure of groups is a fundamental pursuit throughout all 
of math. 
