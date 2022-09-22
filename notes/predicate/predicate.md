---
layout: page
title: Predicates, quantifiers, and equality
nav_order: 2
has_children: false
has_toc: false
parent: Predicate logic
grand_parent: Notes
---

## Families of propositions

In propositional logic, we start with variables, like $A,B,$ or $C$ 
as have been our defaults. These are meant to represent statements 
which can either be true or false. 

But, it is very common for a statement to depend on additional data 
before we can check its truth or falsity. For example, "the dog has 
four feet". Is this true or false? 

Well, it depends on which dog we are talking about. We can think of 
"dog" as a variable which when filled with a concrete dog makes the 
statement a proposition. 

A common, more mathematical, class of examples are statements of about 
numbers. Recall that the natural numbers $\mathbb{N}$ are $0,1,2,3,\ldots$. 

**Definition**. Given two natural numbers $n$ and $m$, we say $n$ 
_divides_ $m$ if there is some other natural number $c$ such that 
$$
m = cn 
$$
If $n$ divides $m$, we write $n \mid m$. If $n$ does not divide $m$, 
we write $n \nmid m$. 

For example, $2$ divides $4$ but $3$ does not divide $4$. 

The statement $m$ divides $n$ can be true or false depending on 
the values we have for $m$ and $n$. 

Another important possible property of a (natural) number. 

**Definition**. A natural number $p$ is _prime_ if 
- $p \neq 1$, i.e. $p$ is not $1$, and 
- whenever there is another natural number $d$ with $d \mid n$, then 
we must have $d = 1$ or $d = p$. 

So $13$ is prime but $15 = 3 \cdot 5$ is not because it is divisible by 
$3$ and $5$. 

The truth of the statement, $n$ is prime, depends on the value of $n$ 
itself.

In each of these examples, we have collection of variables, dogs or numbers, 
and statements whose truth are predicated on value of the variable. 

Predicate, or first order, logic is an extention of propositional logic 
meant to model these examples. The basic building blocks are called 
_predicates_ and usually denoted like $A(x), B(x,z)$, or $C(x_1,\ldots,x_n)$. 

Here $x$ and $A$ play different roles. The symbol $x$ is a stand in for 
our variables and $A$ is like a proposition but it depends on $x$ 
in general. One way to understand this semantically is as a function 
$A : \alpha \to \text{Prop}$ where $x \in \alpha$ is our collection of 
variables and $A$ is a function which hands back a proposition whenever 
an choice from $\alpha$ is inputed. 

If we have a regular old proposition, we can think of it a predicate that 
does not change as we vary the input. In this way, we can start to 
embed propositional logic in predicate logic. Continuing, we add it 
the familiar connectives. 

If $A(x,y)$ and $B(z)$ are predicates, then we make new formulas using 
- implication: $A(x,y) \to B(z)$ 
- negation: $\neg B(z)$
- conjunction: $A(x,y) \land B(z)$
- disjunction: $A(x,y) \lor B(z)$
- bi-implication: $A(x,y) \leftrightarrow B(z)$. 

Like with propositional logic, we can keep joining up formulas using these 
connectives to make bigger and bigger new formulas. 

## Functions 

We already saw that predicates can be viewed as functions taking values in 
propositions. But, predicate logic also allows actual (multi-variant) 
functions $f(x,y,z)$ whose inputes comes from domain of discourse and whose 
output is also in our domain discourse. 

For example, if we are talking about $\mathbb{N}$, we might want to consider 
the addition function
$$
\operatorname{Add} (n,m) = n + m 
$$
or multiplication 
$$
\operatorname{Mult}(n,m) = n\cdot m
$$

Given a function $f(x)$, we can make new predicates from an old ones $A(y)$ 
via substitution $A(f(x))$. 

## Quantifiers 

If we stopped here, our resulting logic would look like propositional logic 
with just a bigger set of propositions coming from varying the inputs. The 
richness of allowing propositions to depend on variables is that we can naturally 
ask about _which_ values make a predicate true. 

Which dogs have four legs? All of them? Some of them? None of them? 

To capture these sentiments, we introduce two new symbols into the game: 
- the universal quantifier: $\forall$
- the existential quantifier : $\exists$

The universal quantifier is commonly called a "for all" and the existential quantifier 
a "there exists". Before we gives the symbolic rules for writing our formulas 
in predicate logic using $\forall$ and $\exists$. Let's look at quantifying 
statements in the realm of numbers. 

**Definition**. A number $n$ is _even_ if $2 \mid n$ and is _odd_ if $2 \nmid n$. 

Clearly any number is either divisible by $2$ or not. So the following is a true 
statement: for all $n$, $n$ is even or $n$ is odd. 

We could look at the statement: for all $n$, $n$ is prime. This would be false as 
we have seen there are values of $n$, like $15$, that are not prime numbers. 

The following is true: there exists some $n$ such that $n$ is prime. Since $n=2$ is 
prime, we have at least one $n$ which is prime. 

Using for all, there exists, and their negations, we can capture our questions about 
the quantity of values making the predicate formula true. 

Given a predicate of the form $B(y,z)$ we say that $y$ and $z$ are _free variables_. 
We can attach to each free variable at most one quantifier. For example, 
$\exists y ~ \forall z~ B(y,z)$ is a valid new formula as are $\exists z~ B(y,z)$ 
or $\forall y~ \forall z~ B(y,z)$. Note that each quantifier comes with a variable 
label identifying the variable we are quantifying over. 

Once we quantify over a free variable, it becomes a _bound variable_. In general, given 
a formula in predicate logic with a free variable $x$ we can form a new formula 
by quantifying, using either $\forall$ or $\exists$, over it. 

## Equality 

Using different inputs vs the same can lead to very different statements. 

For example, $n$ is odd or $n$ is even vs $n$ is odd or $m$ is even. We can universally 
quantify over $n$ in the first one and get a true statement but not so with the second. 

We see being able to reason about inputs being the same or different is desired 
when our truth statement depend on those inputs. We therefore introduce one more new 
symbol: $=$, equality. 

We can use $=$ to make new predicates like $x = y$ or $\neg(x = y)$.  

Taking everything together we can make formula like:
- $\forall x~ \exists ~y (A(x,y) \to (x = y))$
- $\exists x~ \exists y~ \exists z~ (\neg(x = y) \land \neg(y=z) \land \neg(x=z) \land B(x,y,z))$ or 
- $\forall x~ (A(x,y) \to \exists z~ B(z))$

For convenience of write, we often bundle together multiple variables bound under the 
same quantifer. For example, we write $\exists x~ y$ when we mean $\exists x~ \exists y$. 

And we adopt standard conventions for implicit parentheses where $\exists$ and $\forall$ 
bind more closely that the previous binary quantifiers. 
