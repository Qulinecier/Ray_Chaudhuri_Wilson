Theorem 1.1 (Ray-Chaudhuri-Wilson). If $\mathcal{F}$ is a $k$-uniform, L-intersecting family of subsets of a set of $n$ elements, where $|L|=s$, then $|\mathcal{F}| \leq\binom{ n}{s}$.

*Proof.*

Define $V=R^{\mathcal{F}}$ for some ring $R$.

```Lean
instance: Module ℝ (F → ℝ) := by infer_instance
```


For each subset $S$, define a vector:

$$
\bar{S}=\sum_{\substack{A \in \mathcal{F} \\ S \subseteq A}} A\tag{1}
$$

```Lean
def S_bar (S : Finset α): F → ℝ  :=
    fun A => if S ⊆ A then 1 else 0
```
Then we define the whole set $\left\{\bar{S}: S \in \mathscr{P}_s(X)\right\}$, where $\mathscr{P}_s(X)$ is the set of subsets $S$ such that $\#S = s$.


```Lean
variable (S: X.powerset)

noncomputable def S_bar_set :=
  Finset.image (fun (S : Finset α) => (S_bar F S: F → ℝ)) (powersetCard s X)
```


Now we say $L = \left\{\mu_1, \mu_2, \cdots, \mu_s\right\}$

Define an indicator for intersection with $S$ such that $|B \cap S| = \mu$:
$$
H_\mu=\sum\left(B: B \in \mathcal{A},\left|B \cap S\right|=\mu\right)\tag{2}
$$

```Lean
def intersection_indicator (S: Finset α) (μ : ℕ): F → ℝ :=
    fun B => if #(B ∩ S) = μ then 1 else 0
```

Then we define an indicator that combine the indicator for vector of subset $S$ and the indicator for intersection with $S$:
$$G_r=\sum\left(\bar{S}: S \in \mathscr{P}_s(X),\left|S \cap A\right|=r\right)\tag{3}$$

```Lean
def subset_intersection_indicator (A: Finset α) (μ : ℕ): F → ℝ :=
    fun B => ∑ S ∈ powersetCard s X, if #(A ∩ S)  = μ then (subset_indicator F S B) else 0
```

We add an condition $|B \cap A| = \mu$ and add up all $\mu \in L$:
$$G_r =\sum\limits_{\mu\in L} \sum\limits_{S\in \mathscr{P}_s(X)} \sum\limits _{B\in \mathcal{F}} \{B: |S\cap A| = r, S\subseteq B, |B\cap A| = \mu\} \tag{4}$$
Then we can choose $r$ elements in $A\cap B$ and $s-r$ elements in $B\setminus A$ to form $S$, so we can define a bijection
$$\{S\in \mathscr{P}_s(X)| |A\cap S| = r\text{ and }S\subseteq B\} \rightarrow \mathscr{P}_r(A\cap B) \times \mathscr{P}_{s-r}(B\setminus A)\tag{5}$$
by
$$S \mapsto ((A\cap B)\cap S, (B\setminus A)\cap S)\tag{6}$$
so that we have
$$\#\{S\in \mathscr{P}_s(X)| |A\cap S| = r\text{ and }S\subseteq B\} = \#\mathscr{P}_r(A\cap B) \times \#\mathscr{P}_{s-r}(B\setminus A)\tag{7}$$

```Lean
lemma card_powerset_card_product (hrs : r ≤ s) : #{S ∈ powersetCard s X | #(A.val.val ∩ S) = r
    ∧ (S: Finset α) ⊆ (B: Finset α)} = #((powersetCard r ((A: Finset α) ∩ (B: Finset α))) ×ˢ
    (powersetCard (s-r) ((B: Finset α) \ (A: Finset α))))
```

together with the $(4)$ and $(7)$, we have
$$G_r=\sum_{\mu\in L}\binom{\mu}{r}\binom{k-\mu}{s-r} H_\mu\tag{8}$$

```Lean
lemma vector_sum_eq_intersection_sum (hintersect : intersecting F L) (huniform: uniform F k) (hrs : r ≤ s):
    subset_intersection_indicator F s A r =
    ∑ (l∈ L), (Nat.choose l r) * (Nat.choose (k - l) (s - r))
    * (intersection_indicator F A l)
```


We want to show $\left\{\bar{S}: S \in \mathscr{P}_s(X)\right\}$ span $\mathbb{R}^\mathcal{F}$ as our final goal. Here are the steps to show it:
1. ${\rm span} \{H_i\} = \mathcal{F}$

Showing ${\rm span} \{H_i\} \leq \mathcal{F}$ is straightforward. The main statement here is to show ${\rm span} \{H_i\} \geq \mathcal{F}$ :
```Lean
lemma span_H (huniform: uniform F k): (⊤: Submodule ℝ (F → ℝ)) ≤ Submodule.span ℝ (subset_H F k)
```