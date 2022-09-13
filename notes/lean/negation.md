---
layout: page
title: Negation and RAA 
nav_order: 5
has_children: false
has_toc: false
parent: Lean  
grand_parent: Notes
---

## Negation 

Let's see how Lean understands negation. 

{% highlight lean %}
variable (A : Prop)
#reduce ¬ A -- A → False
{% endhighlight %}

The command `#reduce` tells Lean to try to peel away notation and write 
things in a more basic form. What we see is that 
