$$
\begin{gathered}
\exists\text{ a compact metrizable abelian group }K,
\text{ its normalized Haar measure }\lambda,
\text{ and subgroups }(H_T)_{T\in\mathrm{WF}},\\
H_T\in\Delta^0_3(K),\qquad
E_{H_T}^K\in\Delta^0_3(K^2),\qquad
E_{H_T}^K\text{ is a difference of two }F_\sigma\text{ sets},\\
\forall F\text{ a standard Borel equivalence relation}\;
\exists T\in\mathrm{WF}\;
\forall C\subseteq K\text{ Borel with }\lambda(C)=1,\qquad
E_{H_T}^K\mathbin{\upharpoonright}C\not\leq_B F.
\end{gathered}
$$

Here the coset relation means that the group difference belongs to the subgroup. The group, its measure, and the entire subgroup family are chosen before the arbitrary target relation. The selected tree must work for every Borel conull domain, without any invariance assumption on that domain.

The proof combines ordinary unboundedness of one fixed compact coset family with a uniform Haar-amplification lemma. The latter replaces any proposed target by one fixed Borel relation that absorbs reductions defined on conull domains. Choosing a member of the family that does not reduce to this amplified target excludes all conull reductions at once.

We first describe the fixed family and its complexity. Let the coordinate index set be the finite lists of natural numbers, with distinguished index the empty list, and put

$$
S=\mathbb N^{<\mathbb N},\qquad
A=\ell^1(S),\qquad
Z=\ell^1(S\times S),\qquad
V=\mathbb R\times Z.
$$

For every well-founded tree the tree construction gives a bounded injective operator on the first space. For an arbitrary such operator, define the scalar-tagged symmetric tensor subspace

$$
V_D=
\left\{\bigl(K(o,o),(D\otimes\mathrm{id})K\bigr):
K\in Z\text{ is symmetric and has finite tensor rank}\right\}.
$$

This is the actual linear subspace `imageSubmodule D o`, rather than an assumed family satisfying an unboundedness property. The tree-indexed source relation is equivalence modulo this subspace.

The coordinate map records the scalar and every matrix entry. Write its index set as the disjoint union of a singleton and the matrix indices. The compact group and the homomorphism into it are

$$
I=\{*\}\sqcup(S\times S),\qquad
K=(\mathbb R/\mathbb Z)^{I\times\mathbb N},\qquad
j(u)_{i,n}=\frac{u_i}{n+1}\pmod{\mathbb Z}.
$$

The homomorphism is continuous and injective. Indeed, if every divided coordinate is integral, dividing by a sufficiently large positive integer makes its absolute value less than one, so that integral must vanish. We equip this countable product of circles with normalized Haar measure and define the compact subgroup for a tree to be the image of its source tensor subspace under this homomorphism and the coordinate map. Using all positive integers in the denominator is a separating compactification variant of the factorial-denominator construction in the manuscript.

The complexity proof establishes that each source subspace, in the product topology on its coordinates, is a difference of two countable unions of compact sets. A compact envelope is obtained by bounding the total coordinate absolute sum and the finite matrix rank. Finite-rank bounds are closed because they are expressed by vanishing minors. Membership inside the envelope is characterized by all full-rank reconstruction charts, including the chart of rank zero. Operator evaluations along rows are pointwise limits of continuous finite-coordinate sums; the chart equations are therefore equalities between Baire-one real functions and define a countable intersection of open sets. The failed universal tests form an F-sigma set on each compact coordinate ball, hence a countable union of compact sets there. Removing all these failed tests gives exactly the coordinate image of the tensor subspace.

The continuous injective compactification carries each of the two countable unions of compact sets to an F-sigma set and respects their difference. Each compact subgroup is consequently a difference of two F-sigma sets. Pulling this representation back under the continuous group-difference map gives the same representation for its coset graph. In a metrizable space every such difference is simultaneously a countable union of G-delta sets and a countable intersection of F-sigma sets. This proves all clauses of `LowComplexityFamily`.

Ordinary unboundedness is proved for this same family. The source argument uses the nilpotent central-extension construction and the continuous correction map `theta`. For a fixed operator, two elements are in the same nilpotent coset exactly when their two residual coordinates agree and their corrected central coordinates differ by the source tensor subspace. If every source tensor relation reduced to one Borel target, this identity would reduce every well-founded nilpotent coset relation to equality on the residual coordinates times that target. The category-transfer theorem would then make the designated-element membership set Borel. The tree-kernel construction identifies that membership set with the non-Borel set of ill-founded trees, a contradiction. Composition with the injective compactification transfers this unboundedness to the fixed compact family:

$$
\forall Q\text{ a standard Borel equivalence relation}\;
\exists T\in\mathrm{WF},\qquad E_{H_T}^K\not\leq_B Q.
$$

Now fix a nonempty standard Borel target. The Haar-amplification theorem produces one standard Borel relation, depending only on the compact group and this target, with the following property:

$$
E_H^K\mathbin{\upharpoonright}C\leq_B F
\quad\Longrightarrow\quad
E_H^K\leq_B Q_{K,F}
$$

for every Borel subgroup and every Borel conull domain. This target is an almost-everywhere pointwise power represented on Baire-space codes. A fixed dense sequence of real integrable functions supplies measurable codes for every jointly Borel bounded real family; a bounded Borel embedding and a total Borel inverse extend this to arbitrary nonempty standard Borel targets. Summable approximation errors show that decoding recovers each section almost everywhere. The resulting almost-everywhere relation on codes has a Borel graph, since the measure of each Borel disagreement section is a measurable function of the two codes. This establishes the needed standard Borel target directly; the formalization does not construct a topological space of equivalence classes of measurable functions.

To verify amplification, extend a reduction on the conull domain to a Borel map on the whole group and code its family of left translates:

$$
a(x,t)=g(tx).
$$

For each fixed pair of group elements, right translations preserve Haar null sets, so both translated points lie in the original domain for almost every translation parameter. Left multiplication preserves their coset relation. The code relation therefore agrees with the original coset relation for that pair, giving a Borel reduction of the whole-group coset relation to the single amplified target. This works for arbitrary compact groups and does not require the domain to be invariant.

Apply ordinary unboundedness to this amplified target and select the corresponding tree. A reduction from any conull restriction of its coset relation to the original target would amplify to a forbidden whole-group reduction. Since the tree was selected before the conull domain, it excludes every such domain simultaneously. If the target space is empty, any set of Haar measure one is nonempty, so a reduction to that target cannot exist. These two cases prove the stated quantifiers, using the fixed witnesses `compactGroup` and `compactFamily`.
