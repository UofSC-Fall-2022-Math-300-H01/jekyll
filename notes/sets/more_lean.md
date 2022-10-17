---
layout: page
title: Proofs in Lean
nav_order: 4
has_children: false
has_toc: false
parent: Sets
grand_parent: Notes
---

## More set theoretic proofs in Lean  

We've seen an example where the goal is to give a proof 
of an equality of sets. Both in Lean and with pen-and-paper, 
to show two sets are equal `X=Y` we use set extensionality 
to reduce to establishing `∀ x, x ∈ X ↔ x ∈ Y`. We then take 
some `x ∈ U`, prove one direction `x ∈ X → x ∈ Y`, and then 
the other `x ∈ Y → x ∈ X`. 

While for pen-and-paper everyone can just do this conversion 
"in their head", in Lean we need to step the computer through 
each time. This can be tedious so we automate it. For that, 
we can use a tactic called `set_extensionality`. 

{% highlight lean %}
variable (U : Type)
variable (X Y : Set U) 

example : X = Y := 
  set_extensionality x 
  -- we now have x:U
  -- and two goals x ∈ X → x ∈ Y and x ∈ X → x ∈ Y
  -- we sorry these goals because we cannot prove two sets are 
  -- equal in general
  . sorry
  . sorry 
{% endhighlight %}

`set_extensionality` helps us when proving a goal of the form 
`X=Y`. What if we have a hypothesis of set equality? 

{% highlight lean %}
variable (x:U)
variable (X Y Z : Set U) 

example (h: X = Y) : X ∪ Z = Y ∪ Z := by 
  rewrite [h] 
  rfl 
{% endhighlight %}

Rewriting the goal with the assumption `X=Y` produces a new 
goal `X ∪ Z = X ∪ Z`. Recall the tactic `rfl` solves goals 
of the form `t = t`. We can also use `rw` in place of `rewrite` 
and `rfl` as `rw` does a rewrite and then calls `rfl`.

Let's see another one. 

{% highlight lean%}
variable (U : Type)
variable (X Y : Set U)

example (h : X ⊆ Y) : Z \ Y ⊆ Z \ X := by 
  intro (x:U) (g : x ∈ Z \ Y)
  have : x ∉ X := sorry 
  exact ⟨g.left,this⟩ 
{% endhighlight %}

The only thing left is to fill in the `sorry`. Knowing that 
if `X ⊆ Y` and `x ∉ Y`, then `x ∉ X` seems like a useful result 
itself. We give it a name and then use it.  (Remember that 
given `h : A ∧ B` we can access a proof of `A` using `h.left` 
and a proof of `B` using `h.right`.)

{% highlight lean%}
variable (U : Type)
variable (X Y : Set U)

theorem sub_comp_super (h : X ⊆ Y) : Yᶜ ⊆ Xᶜ := by 
  intro (x : U) (g : x ∈ Yᶜ) (n : l ∈ X) 
  exact g (h x l) 

example (h : X ⊆ Y) : Z \ Y ⊆ Z \ X := by 
  intro (x:U) (g : x ∈ Z \ Y)
  have : x ∉ X := sub_comp_super h x g.right 
  exact ⟨g.left,this⟩ 
{% endhighlight %}

Next we look at the distributivity of intersection over unions. 

{% highlight lean %}
variable (U : Type) 
variable (X Y Z : Set U)

theorem dist_inter_union : X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := by
  set_extensionality x 
  · intro (h : x ∈ X ∩ (Y ∪ Z))
    cases h.right with 
    | inl (g : x ∈ Y) => exact Or.inl ⟨h.left,g⟩  
    | inr (g : x ∈ Z) => exact Or.inr ⟨h.left,g⟩  
  · intro (h : x ∈ (X ∪ Y) ∩ (X ∩ Z))  
    cases h with 
    | inl (g : X ∩ Y) => exact ⟨g.left,Or.inl g.right⟩ 
    | inr (g : X ∩ Z) => exact ⟨g.left,Or.inr g.right⟩ 
{% endhighlight %}

In place of an `apply Or.elim`, we have used the `cases` tactic. This 
tactic creates different proof goals for each way there is to build 
the term. In our case, `h.right : x ∈ Y ∪ Z` which is definitionally 
equivalent to `x ∈ Y ∨ x ∈ Z`. There are two ways to make a proof of 
an or-statement: either you have a proof of the left and use `.inl` or 
you have a proof the right and use `.inr`. These constructors are 
the labels for the two branches of the cases. Note that `cases` comes 
with additional syntax: `with` and the `|` to label the branches.

Here is an example with the use of `cases` for the existential 
quantifer. 

{% highlight lean %}
variable (I U : Type)
variable (X Y : I → Set U)

example (h : ∃ (i:I), X i ∩ Y i = ∅) : BigInter X ∩ BigInter Y = ∅ := by
  set_extensionality x
  · intro (g : x ∈ BigInter X ∩ BigInter Y)  
    cases h with 
    | intro (i : I) (g₁ : X i ∩ Y i = ∅) => 
      have g₂ : x ∈ X i := g.left i 
      have g₃ : x ∈ Y i := g.right i 
      have g₄ : x ∉ X i ∩ Y i := by 
        rw [g₁] 
        exact fun h => False.elim h
      exact g₄ ⟨g₂,g₃⟩ 
  · exact fun h => False.elim h 

{% endhighlight %}

