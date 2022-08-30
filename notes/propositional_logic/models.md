---
layout: page
title: Truth tables 
nav_order: 5
has_children: false
has_toc: false
parent: Propositional logic 
grand_parent: Notes
---

## What is truth anyway?

Previously we have been performing purely symbolic moves to generate our proofs. 
How does this relate to a given mathematics proof or debate topic? 

To motivate our rules we have often replaced our symbols $A,B,C,$... by 
actual statements, eg "the sun is out". 

"The sun is out" can either be true or false -- we just look outside. So at 
a very basic level this provides a way to assign either T or F to a propositional 
variable. We could of course willy-nilly assign T and F for each our 
propositional variables. But all of our connectives have familiar interpretation 
in the context of T/F values. 

- Not true better be false and vice-versa. So 
$$
\neg T \mapsto F \ , \ \neg F \mapsto T. 
$$
We can put this into a table:

| $A$ | $\neg A$ | 
| :---: | :---: | :---: |
| $T$ | $F$ |
| $F$ | $T$ |

This expresses the values of $\neg A$ given the values of $A$. 

- Suppose I know that $A \to B$ and we know that is $A$ is $T$. It would make a lot 
sense to conclude that $B$ should also be assigned $T$. But if we allow ourselves to 
look at possible assignments it makes sense to assign T/F values to each expression 
using T/F and $\to$. We can make another table where we list the values assigned to
$A$ along the first column and the values assigned to $B$ in the first row.

| $A$ | $B$ | $A \to B$ |
| :---: | :---: | :---: |
| $T$ | $T$ | $T$ |
| $T$ | $F$ | $F$ |
| $F$ | $T$ | $T$ |
| $F$ | $F$ | $T$ |

One can read this as saying the implication is itself is true if either assumption is 
false or both the assumption and conclusion are true. 
- We also have a table for $\land$ 

| $A$ | $B$ | $A \land B$ |
| :---: | :---: | :---: |
| $T$ | $T$ | $T$ |
| $T$ | $F$ | $F$ |
| $F$ | $T$ | $F$ |
| $F$ | $F$ | $F$ |

which says that $A \land B$ should only be true if both $A$ and $B$ are. 
- And we have a table for $\lor$ 

| $A$ | $B$ | $A \lor B$ |
| :---: | :---: | :---: |
| $T$ | $T$ | $T$ |
| $T$ | $F$ | $T$ |
| $F$ | $T$ | $T$ |
| $F$ | $F$ | $F$ |

which says $A \lor B$ is false only when both $A$ and $B$ are.
- We also want 
$$ \top \mapsto T \\ \bot \mapsto F $$

Using these rules, once we have a chosse of T/F, we can assign T/F to *any* 
propositional formula. Let's look at a more complicated formula. 

**Example**. Let's take the formula 
$$
 \neg A \lor B \to C \land \neg D
$$
and the truth assignment 
$$
A, C \mapsto T, \ B, D \mapsto F
$$

It convenient notation to "plug in" to the formula the values of $T$ and 
$F$. This gives
$$
 \neg T \lor F \to T \land \neg F
$$
Then use our rules above to simplify down to a single value. First 
the negation
$$
 F \lor F \to T \land T
$$
Then the $\lor$ and $\land$
$$
 F \to T
$$
Finally for $\to$ we reduce to $T$. 

Different assignments for $A,B,C,D$ can yield a different value for our 
formula. For example, if 
$$
B, C, D \mapsto T, \ A \mapsto F
$$
Then 
$$
 \neg A \lor B \to C \land \neg D \mapsto F 
$$

We can think of the possible truth value assignments to our 
collection of propositional variables as different possible universes. 
For example, if $A$ is standing for "the sun is out", then 
$A \mapsto T$ is saying we know the sun it out while $A \mapsto F$ is 
saying the sun is not out. So any real-world or mathematical possibility 
can be found by listing out all the possible T/F assignments and 
the values taken by the formula given that assignment. Below is a 
table for our example

<details markdown="block">
<summary  markdown="span">
The truth table for our example. (Expand to view)
</summary> 

| $A$ | $B$ | $C$ | $D$ |  $\neg A \lor B \to C \land \neg D$ |
| :---: | :---: | :---: | :---: | :---: |
| $T$ | $T$ | $T$ | $T$ | $F$ |
| $T$ | $T$ | $T$ | $F$ | $T$ |
| $T$ | $T$ | $F$ | $T$ | $F$ |
| $T$ | $F$ | $T$ | $T$ | $T$ |
| $F$ | $T$ | $T$ | $T$ | $F$ |
| $T$ | $T$ | $F$ | $F$ | $F$ |
| $T$ | $F$ | $T$ | $F$ | $T$ |
| $F$ | $T$ | $T$ | $F$ | $T$ |
| $T$ | $F$ | $F$ | $T$ | $T$ |
| $F$ | $T$ | $F$ | $T$ | $F$ |
| $F$ | $F$ | $T$ | $T$ | $F$ |
| $T$ | $F$ | $F$ | $F$ | $T$ |
| $F$ | $T$ | $F$ | $F$ | $F$ |
| $F$ | $F$ | $T$ | $F$ | $T$ |
| $F$ | $F$ | $F$ | $T$ | $F$ |
| $F$ | $F$ | $F$ | $F$ | $F$ |

</details>

