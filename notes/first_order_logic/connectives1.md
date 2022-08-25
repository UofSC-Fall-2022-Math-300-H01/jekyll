---
layout: page
title: And, or, implies
nav_order: 2
has_children: false
has_toc: false
parent: First order logic
grand_parent: Notes
---

Last time, we saw the beginnings of a formal system to 
represent logical reasoning. Here we introduce some operations 
on a collection of propositions to build *expressions*. 

You can think of the propositions as the atoms of our system and 
the connectives we introduce as the bonds. 

In addition, for each connective, we give a introductiona and elimination 
rule in deduction. 

## Conjunction 

One basic rhetorical device is a take a bunch of statements and group 
them together with an *and*. 

The murderer was cousin Mr. Plum *and* the weapon was the candlestick *and* 
the murder occured in the foyer. 

The corresponding connective in logic has the fancy name of conjunction is 
denoted by $\land$. So if we have expressions $C$ and $D$, then 
$C \land D$ is another valid expression.

Now let's think about what we can deduce assuming we know $C$ and $D$. It may 
seem silly but if we know $C \land D$ then we know $C$. So we have the following 
elimination rule for deduction 

{% eqn And_left_elimination %}
\begin{prooftree}
\hypo{C\land D} 
\infer1{C} 
\end{prooftree}
\normalsize $\land_{E_L}$
{% endeqn %}

The notation we use for this move is $\land_{E_L}$.

Similarly, we have the right-sided analog. 

{% eqn And_right_elimination %}
\begin{prooftree}
\hypo{C\land D} 
\infer1{D} 
\end{prooftree}
\normalsize $\land_{E_R}$
{% endeqn %}

Then we have a introduction rule that mirrors: if we know that $C$ is true and $D$ 
is true, then we know that $C$ and $D$ is true. 

{% eqn And_introduction %}
\begin{prooftree}
\hypo{C}
\hypo{D}
\infer2{C \land D}
\end{prooftree}
\normalsize $\land_I$
{% endeqn %}

Note that at this level we know very little. For example, $A \land B \land C$ is 
ambigious. It is either 
$$
(A \land B) \land C 
$$
or
$$
A \land (B \land C)
$$
But these are logically equivalent, meaning we can prove one from the other and vice-versa. 
Below we have 
$$
(A \land B) \land C \vdash A \land (B \land C)
$$

{% eqn And_associativity_one_direction %}
\begin{prooftree}
\hypo{ (A \land B) \land C } \infer1{ A \land B } \infer1{A}
\hypo{ (A \land B) \land C } \infer1{ A \land B } \infer1{B}
\hypo{ (A \land B) \land C } \infer1{ C }
\infer2{ B \land C}
\infer2{ A \land (B \land C) }
\end{prooftree}
{% endeqn %}

Can you give a proof for 
$$
A \land (B \land C) \vdash (A \land B) \land C ~?
$$

## Disjunction 

Another common rhetorical pattern is an argument by cases. Often the cases are exhaustive, like 
"it is sunny or it is not sunny". 

Our introduction rules are pretty straightforward. 

{% eqn Or_introduction_left %}
\begin{prooftree}
\hypo{A} 
\infer1[\normalsize $\lor_{I_L}$]{A \lor B}
\end{prooftree} \ \ 
\begin{prooftree}
\hypo{B} 
\infer1[\normalsize $\lor_{I_R}$]{A \lor B}
\end{prooftree}
{% endeqn %}

The elimination rule is a bit more subtle.
If we want to reach our goal $C$ and we know that $A$ or $B$ is true, then we need to 
justify $C$ in two separate cases. One case for when $A$ is true and one case for 
when $B$ is true. This means that elimination needs to take in a proof $A \vdash C$ and 
$B \vdash C$. 

{% eqn Or_elimination %}
\begin{prooftree}
\hypo{A \lor B} 
\infer0[\normalsize 1]{A} \ellipsis{}{ \overline{C} }
\infer0[\normalsize 1]{B} \ellipsis{}{ \overline{C} }
\infer3[\normalsize 1 $~\lor_E$]{C}
\end{prooftree}
{% endeqn %}

Note the lines above $A$ and $B$. This an example of hypothetical reasoning. We have assumed 
that $A$ is true and provided some argument to derive $C$. Similarly, we have assumed that
$B$ is true and argued to $C$. Given both, then know that $A \lor B \vdash C$. 

The superscipts ${}^1$ indicate where we introduce additional assumptions and where we cancel. 
The numbering helps up keep track of any hypotheses introduced. 

## Implication 

Implication is basic step in a (natural language) logical argument. If we know that whenever 
$X$ is true, then so is $Y$. Then once we know that $X$ is true we get that $Y$ is also. 

We have a connective symbol $\to$ for implication. Via our interpretation of proofs, one 
would likely also think of $X \vdash Y$ as type of implication. The introduction and 
elimination rules make this connection clearer. 

First for elimination, we need to know $X \to Y$ and $X$ to conclude $Y$. 

{% eqn Implication_elimination %}
\begin{prooftree}
\hypo{X \to Y}
\hypo{X}
\infer2[\normalsize $\to_E$]{Y}
\end{prooftree}
{% endeqn %}

The introduction rule is 
{% eqn Implication_introduction %}
\begin{prooftree}
\infer0[\normalsize 1]{X} 
\ellipsis{}{ \overline{Y} }
\infer1[\normalsize 1 $~\to_I$]{X \to Y}
\end{prooftree}
{% endeqn %}

## Bi-implication

Another connective is bi-implication, or commonly called iff for if and only if. It is denoted 
$\leftrightarrow$. 

It has two elimination rules depending on whether we know $X$ or $Y$.

{% eqn Bi-implication_left_elimination %}
\begin{prooftree}
\hypo{X \leftrightarrow Y}
\hypo{X}
\infer2[\normalsize $\leftrightarrow_{E_L}$]{Y}
\end{prooftree} \ \ 
\begin{prooftree}
\hypo{X \leftrightarrow Y}
\hypo{Y}
\infer2[\normalsize $\leftrightarrow_{E_R}$]{X}
\end{prooftree}
{% endeqn %}

If we have a proofs $X \vdash Y$ and $Y \vdash X$ then we can conclude $X \leftrightarrow Y$.

{%eqn Bi-implication_right_elimination %}
\begin{prooftree}
\infer0[\normalsize 1]{X}
\ellipsis{}{\overline{Y}}
\infer0[\normalsize 1]{Y}
\ellipsis{}{\overline{X}}
\infer2[\normalsize 1 $\leftrightarrow_I$]{X \leftrightarrow Y}
\end{prooftree}
{% endeqn %}

Let's do an example proof to see how these rules interact. 

**Example**. Let's show that 
$$
(A \to B) \land (B \to C) \vdash A \to C
$$
So if $A$ implies and $B$ implies $C$, then $A$ implies $C$ if we intrepret it using words.

{% proof %}
To prove $A \to C$, we want introduce a $\to$. This introduce says we can conclude $A \to C$ 
if we can establish $A \vdash C$. Thus, we can reduce to proving
$$
(A \to B) \land (B \to C), A \vdash C
$$
With $A$ and $A \to B$, we can eliminate to $B$. Then with $B$ and $B \to C$, we can eliminate 
to $C$. Below is a full proof.

{% eqn Transitivity_of_implication %}
\begin{prooftree}
\infer0[\normalsize 1]{A} 
\hypo{(A \to B) \land (B \to C)}
\infer1[\normalsize $\land E_l$]{A \to B}\
\infer2[\normalsize $\to E$]{B}
\hypo{(A \to B) \land (B \to C)}
\infer1[\normalsize $\land E_r$]{B \to C}
\infer2[\normalsize $\to E$]{C}
\infer1[\normalsize 1 $\to I$]{A \to C}
\end{prooftree}
{% endeqn %}
{% endproof %}

Here is another example. 

**Example**. Let's establish 
$$
((A \lor B) \to C) \to ((A \to C) \land (B \to C))
$$

{% proof %}
Recall that 
$$
((A \lor B) \to C) \to ((A \to C) \land (B \to C))
$$
is shorthand for 
$$
\vdash ((A \lor B) \to C) \to ((A \to C) \land (B \to C))
$$
In other words, we want to proof the formula without assumptions. 

We "backwards" similarly to the last example. To establish a goal of the form $X \to Y$, 
we need $X \vdash Y$. So it suffices to show 
$$
((A \lor B) \to C) \vdash ((A \to C) \land (B \to C))
$$
Now to establish a goal with $\land$ we want to prove both sides of the $\land$. So we 
need two proofs
$$
(A \lor B) \to C \vdash A \to C \\
(A \lor B) \to C \vdash B \to C 
$$
Again we can reverse the introduction rule for $\to$ to reduce to 
$$
(A \lor B) \to C, A \vdash C \\
(A \lor B) \to C, B \vdash C 
$$
We can use the introduction rules for $\lor$ to produce $A \lor B$ from either $A$ or $B$. 

Putting it all together we have 
{% eqn Example_2 %}
\begin{prooftree}
\infer0[\normalsize 0]{A \lor B \to C} 
\infer0[\normalsize 1]{A} 
\infer1[\normalsize $\lor I_l$]{A \lor B} 
\infer2[\normalsize $\to E$]{C}
\infer1[\normalsize 1 $\to I$]{A \to C}
\hypo{A \lor B \to C} 
\infer0[\normalsize 2]{B} 
\infer1[\normalsize $\lor I_r$]{A \lor B} 
\infer2[\normalsize $\to E$]{C}
\infer1[\normalsize 2 $\to I$]{B \to C}
\infer2[\normalsize $\land$ I]{(A \to C) \land (B \to C)}
\infer1[\normalsize 0 $\to$ I]{(A \lor B) \to C \to ((A \to C) \land (B \to C)}
\end{prooftree}
{% endeqn %}
{% endproof %}

## Some conventions 

Writing out lots of $( \ )$ is tedious after awhile. We therefore establish some 
conventions on how to read a formula without paretheses. 

First, all of $\to, \land,$ and $\lor$ associate right to left. This means that 
$$
A \lor B \lor C := A \lor (B \lor C)
$$

Then $\to$ binds more weakly that both $\lor$ and $\land$. For example
$$
A \lor B \to C \land D := (A \lor B) \to (C \land D)
$$

It is important to remember that, in general, the placement of parentheses makes a 
difference!
