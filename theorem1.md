Theorem 1.1 (Ray-Chaudhuri-Wilson). If $\mathcal{F}$ is a $k$-uniform, L-intersecting family of subsets of a set of $n$ elements, where $|L|=s$, then $|\mathcal{F}| \leq\binom{ n}{s}$.

*Proof.*

Define $V=R^{\mathcal{F}}$ for some ring $R$.

(I chose real numbers here, but maybe $\mathbb{F}_2$ seems better?)


```Lean
instance: Module ℝ (F → ℝ) := by infer_instance
```



For each subset $S$, define a vector:

$$
\bar{S}=\sum_{\substack{A \in \mathcal{F} \\ S \subseteq A}} A
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