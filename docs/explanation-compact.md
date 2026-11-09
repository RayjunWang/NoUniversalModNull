$$
\begin{gathered}
\exists\text{ a compact metrizable abelian Haar probability group }K
\text{ and subgroups }(H_T)_{T\in\mathrm{WF}},\\
H_T\in\Delta^0_3(K),\qquad
E_{H_T}^K\in\Delta^0_3(K^2),\qquad
E_{H_T}^K\text{ is a difference of two }F_\sigma\text{ sets},\\
\forall F\text{ a standard Borel equivalence relation}\;
\exists T\in\mathrm{WF},\qquad E_{H_T}^K\not\leq_B F.
\end{gathered}
$$

The group and the entire subgroup family are fixed before the arbitrary Borel target. The proof realizes the actual unbounded tree-tensor family inside one countable product of circles. Its complexity comes from a compact finite-rank envelope and a universal reconstruction test whose failures are countable unions of compact sets.

Let the source spaces and scalar-tagged subspace be

$$
S=\mathbb N^{<\mathbb N},\quad o=\varnothing,\quad
A=\ell^1(S),\quad Z=\ell^1(S\times S),\quad V=\mathbb R\times Z,
$$

$$
V_D=\left\{\bigl(K(o,o),(D\otimes\mathrm{id})K\bigr):
K\in Z\text{ is symmetric and has finite tensor rank}\right\}.
$$

The tree construction supplies a bounded injective operator for each well-founded tree. The source equivalence relation is equality modulo the corresponding subspace. All the operators and tensor subspaces in the construction are explicit.

We first prove the complexity statement for every bounded injective operator. Regard a scalar-matrix pair as a real coordinate vector with index set

$$
I=\{*\}\sqcup(S\times S),\qquad X=\mathbb R^I.
$$

The topology here is the product topology. For a nonnegative integer and a finite-rank bound, define

$$
B_M=\left\{u\in X:
\sum_{i\in F}|u_i|\leq M\text{ for every finite }F\subseteq I\right\},
$$

$$
C_{M,r}=B_M\cap
\left\{u:\text{every }(r+1)\times(r+1)\text{ matrix minor of }u\text{ vanishes}\right\}.
$$

The first set is closed and lies in the product of the compact intervals from minus the bound to the bound. It is therefore compact. The minor condition is closed, so each bounded finite-rank set is compact as well. Every element of a coordinate ball determines an actual summable scalar-matrix pair: the uniform bounds on finite absolute sums imply summability. Conversely, every summable scalar-matrix pair belongs to some integer coordinate ball. Thus these compact sets are genuine source-coordinate pieces.

Vanishing minors give the required algebraic rank bound. If there were one more independent row than the bound allows, finitely many coordinate evaluations would exhibit a nonzero minor, a contradiction. Selecting an independent family spanning the row space proves that it is finite dimensional and has dimension at most the bound. The converse follows by applying the same determinant argument to a family exceeding its dimension. A finite-dimensional row space also gives a finite tensor expansion, obtained from a nonsingular coordinate pivot and its adjugate. These facts are proved for the actual summable matrix space.

Here is the universal membership test. For any finite row and column selectors, form the selected rows, the operator pivot, its determinant, and its reconstruction numerator:

$$
a_t=\operatorname{row}_{\rho_t}R,\qquad
P_{st}=D(a_t)(q_s),\qquad d=\det P,
$$

$$
L=\sum_{t,s}(\operatorname{adj}P)_{ts}\,
a_t\otimes\operatorname{row}_{q_s}R.
$$

Whenever the matrix rank is at most the number of selected rows and the determinant is nonzero, require the three identities

$$
dR=(D\otimes\mathrm{id})L,\qquad
L^{\mathsf T}=L,\qquad d\lambda=L(o,o).
$$

A nonzero pivot makes the selected rows independent; the rank bound then makes them a basis of the row space. If the pair belongs to the scalar-tagged symmetric image, symmetry of its preimage and injectivity of the operator put every preimage column in that row span. Adjugate reconstruction gives the scalar multiple of the preimage as precisely the numerator, proving all three identities in every applicable chart.

Conversely, suppose the matrix has finite rank and every applicable chart satisfies the identities. Choose a basis from its actual rows. Applying the injective operator preserves independence, so finitely many coordinate evaluations give a nonzero pivot. The corresponding chart supplies a symmetric finite tensor preimage:

$$
K=d^{-1}L.
$$

Its scalar coordinate and its operator image are the required pair. The test includes rank zero. In that chart the determinant of the empty matrix is one and the numerator is zero, so the identities force both the matrix and its scalar tag to vanish. No separate positive-rank convention leaves an exceptional scalar axis.

The tests have the required descriptive complexity on each coordinate ball. For a fixed row and evaluation coordinate, enumerate the matrix-coordinate index set. The operator evaluation is the pointwise limit of continuous finite-coordinate expressions:

$$
D(\operatorname{row}_aR)(q)
=\lim_{n\to\infty}
\sum_{k<n}D\bigl(R(a,s_k)e_{s_k}\bigr)(q).
$$

This convergence follows from the summable expansion of a row into its coordinate vectors and continuity of the bounded operator. Hence each evaluation is Baire one. Determinants, adjugates, and the coordinates of the reconstruction numerator and its operator image are finite polynomial combinations of these evaluations and ordinary coordinate functions. They are Baire one as well. Equality sets of two real Baire-one functions are G-delta sets. Each conditional chart test is the union of the open rank-failure set, the G-delta zero-determinant set, and the G-delta set of reconstruction identities. There are only countably many charts, so satisfying every chart is G-delta on the ball.

Let the envelope and the failed-test obstruction be

$$
B=\bigcup_{M,r\in\mathbb N}C_{M,r},\qquad
N=\bigcup_{M\in\mathbb N}
\left\{u\in B_M:\text{some applicable universal chart test fails}\right\}.
$$

The envelope is a countable union of compact sets. On each compact ball, the failed-test set is F-sigma relative to that ball, hence a countable union of compact sets in the ambient coordinate space. The obstruction has the same compact-union property. The membership characterization proves the exact identity

$$
\operatorname{coordinates}(V_D)=B\setminus N.
$$

We now compactify the coordinate space by

$$
K=(\mathbb R/\mathbb Z)^{I\times\mathbb N},\qquad
j(u)_{i,n}=\frac{u_i}{n+1}\pmod{\mathbb Z}.
$$

This is a continuous injective homomorphism. A coordinate whose quotient by every positive integer is integral must vanish, since a sufficiently large denominator gives an integer of absolute value less than one. This choice of denominators is a separating variant of the factorial-denominator compactification in the manuscript. The countable product is compact, metrizable, and abelian, and it carries its normalized Haar probability measure.

Define the compact subgroup for each tree to be the image of its source tensor subspace under the coordinate map followed by this homomorphism. A continuous map takes compact sets to compact sets, and compact sets in the target are closed. Injectivity preserves set difference, so the identity above makes every subgroup a difference of two F-sigma sets. The graph of its coset relation is the preimage under the continuous group-difference map and has the same complexity. In metrizable spaces a difference of two F-sigma sets is Delta-three; this proves the subgroup and graph clauses simultaneously.

It remains to prove unboundedness for these particular witnesses. In the nilpotent source construction, the correction map `theta` gives a continuous reduction of each generated-subgroup coset relation to equality on two residual coordinates times the corresponding tensor coset relation. If all well-founded tensor relations reduced to one target, the category-transfer theorem would imply that the designated-element membership set was Borel. The tree-kernel argument identifies that set with the non-Borel set of ill-founded trees. Therefore the source tensor family has no Borel upper bound.

Finally, the continuous injective group homomorphism preserves and reflects membership in the image of each tensor subspace. It consequently reduces each source tensor relation to its compact coset relation. A common upper bound for the compact family would compose with these maps to give a common upper bound for the source family, contradicting the preceding result. This yields the stated ordinary unboundedness of the fixed compact family.
