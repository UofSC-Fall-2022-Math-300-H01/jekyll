---
layout: page
title: Useful formula
nav_order: 7
has_children: false
has_toc: false
parent: Propositional logic 
grand_parent: Notes
---

## Useful formula  

We delve much deeper into propositional (and other kinds of) logic. While 
we will talk about one more form of logic (first order or predicate 
logic), we want to get to using our new logical skills on mathematical 
questions. 

As such, let's end the module on propositional logic with a list of 
useful and/or well-known provable formulas. Below $A,B,C$ are general formula.

- $$A \land B \leftrightarrow B \land A$$ When we can exchange the placement of 
an operation taking two inputs (binary operation), then we say it is *commutative*. 
This is saying that $\land$ is commutative (up to bi-implication). 
- $\lor$ is commutative : $$A \lor B \leftrightarrow B \lor A$$ 
- $$(A \land B) \land C \leftrightarrow A \land (B \land C)$$ When we 
have three arguments for a binary and consume them in different orders (apply it 
to 1 and 2 then the result to 3 vs apply it to 2 and 3 first then the result to 1 
while keeping the order of the placements) without affecting the final output, 
then we say the operation is *associative*. So here $\land$ is asssociative. 
- You can distribute $\land$ over $\lor$: 
$$ A \land (B \lor C) \leftrightarrow (A \land B) \lor (A \land C)$$
- You can also distribute $\lor$ over $\land$:
$$ A \lor (B \land C) \leftrightarrow (A \lor B) \land (A \lor C)$$
- $$ (A \to (B \to C)) \leftrightarrow (A \land B \to C)$$
- Transitivity of implication: $$(A \to B) \to ((B \to C) \to (A \to C))$$
- $$((A \lor B) \to C) \leftrightarrow (A \to C) \lor (B \to C)$$ 
- $$\neg (A \lor B) \leftrightarrow \neg A \land \neg B$$
- $$\neg (A \land B) \leftrightarrow \neg A \lor \neg B$$ 
<!-- - $$\neg (A \lor \neg A)$$ -->
- $$\neg (A \to B) \leftrightarrow A \land \neg B$$
- $$\neg A \to (A \to B)$$
- $$(\neg A \lor B) \leftrightarrow (A \to B)$$
<!-- - $$A \lor \bot \leftrightarrow A$$ -->
<!-- - $$A \land \bot \leftrightarrow \bot$$ -->
- $$\neg(A \leftrightarrow \neg A)$$
- $$(A \to B) \leftrightarrow (\neg B \to \neg A)$$
- $$(A \to (B \lor C)) \to ((A \to B) \lor (A \to C))$$
<!-- - $$((A \to B) \to A) \to A$$ -->
- If $B \leftrightarrow C$, then for any $A$ we have 
	- $$ A \lor B \leftrightarrow A \lor C$$
	- $$ A \land B \leftrightarrow A \land C$$
	- $$ A \to B \leftrightarrow A \to C$$

Each of the above can provide a useful logical shortcut when in the midst of a 
mathematical argument. 
