---
layout: page
title: Sets in Lean
nav_order: 3
has_children: false
has_toc: false
parent: Sets
grand_parent: Notes
---

## Sets in Lean 

Given a universal set $\mathcal U$, one can go back and forth between 
predicates on elements of $\mathcal U$ and subsets of $\mathcal U$.

For $P(x)$, a predicate on $x \in \mathcal U$, we define the set
$$
X := \lbrace x \mid P(x) \rbrace 
$$
This is the set of all $x \in \mathcal U$ satisfying $P$.

For a subset $X \subset \mathcal U$, we have 
$$
P(x) := x \in X 
$$
the predicate which checks membership of $x$ in $X$. 

We use this idea to embed basic set theory in Lean as follows. For 
our universe of discourse $\mathcal U$, we use a type `U:Type` and 
then we define `Set U` to simply be predicates 

{% highlight lean %}
def Set (U : Type) := U → Prop 
{% endhighlight %}

Here we create a definition, denoted `def`, to indicate we are constructing 
some data. Theorems/examples are just special types of definitions in 
Lean. 

Membership now becomes satisifcation of the underlying predicate. 

{% highlight lean %}
variable (U : Type) 

def Mem (x : U) (X : Set U) : Prop := X x 
{% endhighlight %}

We introduce standard mathematical notation for membership `∈` typed as 
`\in`. To check membership is then equivelent to providing a proof of the 
predicate. 

{% highlight lean %}
variable (U : Type)
variable (X : Set U)

-- going from a proof of X x to x ∈ X 
example (x : U) (h : X x) : x ∈ X := h  

-- going back 
example (x : U) (h : x ∈ X) : X x := h 
{% endhighlight %}

We have containment of sets. 

{% highlight lean %}
variable (U : Type)

def Subset {U : Type} (X Y : Set U) : Prop := ∀ x, x ∈ X → x ∈ Y
-- given the notation ⊆, typed \sub  
{% endhighlight %}

Then, our basic set operations mirror our logical operations. 

{% highlight lean %}
variable (U : Type)

def Union (X Y : Set U) : Set U := fun (x:U) => x ∈ X ∨ x ∈ Y
-- given the notation X ∪ Y, typed as \cup 
def Inter (X Y : Set U) : Set U := fun (x:U) => x ∈ X ∧ x ∈ Y  
-- given the notation X ∩ Y, typed as \cap 
def Diff (X Y : Set U) : Set U := fun (x:U) => x ∈ X ∧ x ∉ Y 
-- given the notation X \ Y 
{% endhighlight %}

We also have the universal set and the empty set

{% highlight lean %}
variable (U : Type)

def Univ : Set U := fun _ => True 
def Empty : Set U := fun _ => False 
--  with notation ∅, typed as \empty 
{% endhighlight %}

With this, we can define the complement of a set: all elements not in it. 

{% highlight lean %}
variable (U : Type)

def Comp (X: Set U) : Set U := Univ \ X 
-- given the notation Xᶜ, typed \^c 
{% endhighlight %}

Then the remainder of set-theoretic constructs 
{% highlight lean %}
variable (I U V: Type) 

def PowerSet (X : Set U) : Set (Set U) := fun (Y : Set U) => Y ⊆ X
-- given notation 𝒫, typed \powerset 

def Prod (X : Set U) (Y : Set V) : Set (U × V) := fun z => z.1 ∈ X ∧ z.2 ∈ Y
-- given notation X ×ˢ Y, typed \times\^s 

def BigUnion (X : I → Set U) : Set U := fun x => ∃ i, x ∈ X i 

def BigInter (X : I → Set U) : Set U := fun x => ∀ i, x ∈ X i 
{% endhighlight %}

Taking both power sets and products naturally land us in sets of a different 
type than we start. 

Notice for products we have a product type `U × V`. Terms of this type are pairs `(u,v)` 
where `u:U` and `v:V`. Writing `z : U × V` we can access the each entry 
using `z.1` and `z.2`. 

Before we prove anything, we need one essential fact: set extensionality. This is an 
axiom of set theory but is a consequence (of other extensionality axioms) in Lean. 

{% highlight lean %}
variable (U : Type)
variable (X Y : Type) 

theorem set_ext : X = Y ↔ (∀ (x:U), x ∈ X ↔ x ∈ Y) := sorry
{% endhighlight %}

Let's see some proves using these notions. 

{% highlight lean %}
varible (U : Type)
variable (X Y : Set U)

theorem sub_left_of_union : X ⊆ X ∪ Y := by 
  intro (x:U) (h: x ∈ X)
  -- we call the corresponding operation on propositions 
  exact Or.inl h 

theorem sub_right_of_union : Y ⊆ X ∪ Y := by 
  intro (x:U) (h: x ∈ Y)
  exact Or.inr h 

theorem comm_union : X ∪ Y = Y ∪ X := by 
  -- we use set extensionality to get equality from a proof 
  -- of (∀ (x:U), x ∈ X ↔ x ∈ Y) 
  apply set_ext.mpr
  intro (x:U) 
  apply Iff.intro
  -- this allows us to split into two proofs for each direction 
  -- of containment. 
  · intro (h: x ∈ X ∪ Y ) 
    apply Or.elim h 
    -- now we supply proofs for each branch of the or 
    · exact fun (g : x ∈ X) => sub_right_of_union x g 
    · exact fun (g : x ∈ Y) => exact sub_left_of_union x g 
  · intro (h : x ∈ Y ∪ X) 
    apply Or.elim h 
    · exact fun (g : x ∈ Y) => sub_right_of_union x g 
    · exact fun (g : x ∈ X) => exact sub_left_of_union x g 
{% endhighlight %}

We introduced some new syntax here. Note the dots. They focus your infoview on a 
single current goal if you have multiple. They are not necessary but might be helpful. 
Note that you _need_ to indent if you use dots. 
