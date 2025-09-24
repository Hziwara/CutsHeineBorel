# Heine-Borel Theorem for Cuts

This repository contains an intuitionistic proof in Lean 4 of the following proposition:

> A pair $(L, U)$ of subsets of rational numbers $\mathbb{Q}$ is called a *cut* if the following conditions are satisfied:
> - $\forall a,b : \mathbb{Q},\, a < b \land b \in L \to a \in L$.
> - $\forall a,b : \mathbb{Q},\, a < b \land a \in U \to b \in U$.
> - $\forall a : \mathbb{Q},\, a \in L \to \exists b : \mathbb{Q},\, a < b \land b \in L$.
> - $\forall b : \mathbb{Q},\, b \in U \to \exists a : \mathbb{Q},\, a < b \land a \in U$.
> - $\forall a,b : \mathbb{Q},\, a \in L \land b \in U \to a < b$.
> 
> For a cut $(L, U)$, we write
>  - $\overline{L} := \{b : \mathbb{Q} \mid \forall a : \mathbb{Q},\, a < b \to a \in L\}$,
>  - $\overline{U} := \{a : \mathbb{Q} \mid \forall b : \mathbb{Q},\, a < b \to b \in U\}$.
> 
> Let $a, b \in \mathbb{Q}$ be a pair of rational numbers and let $(q_i, r_i)_{i\in \iota}$ be an indexed set of pairs of rational numbers.
> We assume the following condition:
>> For all cuts $(L,U)$, if $ q_i \in L \to r_i \in \overline{L}$ and $ r_i \in U \to q_i \in \overline{U}$ for all $i\in\iota$, then $a \in \overline{L}\to b \in L$ and $b \in \overline{U} \to a \in U$.
> 
> Then, there exists a finite subset of indices $i_0,\ldots i_{n-1} \in \iota$ such that
>> For all cuts $(L,U)$, if $ q_i \in L \to r_i \in \overline{L}$ and $ r_i \in U \to q_i \in \overline{U}$ for all $i= i_0,\ldots, i_{n-1}$, then $a \in \overline{L}\to b \in L$ and $b \in \overline{U} \to a \in U$.

Note that the above assumption is classically equivalent to the condition that open intervals $(q_i, r_i)$ cover the closed interval $[a,b]$.
Thus, this proposition is classically equivalent to the Heine-Borel theorem for closed intervals.

## Caution
Since our code uses mathlib4, the result may depend on the axiom of choice unless the version of the library is exactly the same.