$$
\exists(K,\lambda,(H_T)_{T\in\mathrm{WF}})\;
\forall F\;\exists T\;\forall C\text{ Borel},\qquad
\lambda(C)=1\Longrightarrow
E_{H_T}^K\mathbin{\upharpoonright}C\not\leq_B F.
$$

The witnesses are one compact metrizable abelian group with normalized Haar probability and one family of subgroups. Each subgroup is Delta-three; each coset graph is a difference of two F-sigma sets, hence Delta-three. The quantifier over the domain follows the selected tree. A reduction on a domain must preserve and reflect the relation on every pair in that domain.

The proof has three components: the actual tree-tensor family is unbounded under ordinary Borel reducibility; the same family has a low-complexity realization in a fixed compact group; and Haar translation turns a reduction on a conull domain into a whole-group reduction to a fixed amplified target.

The source spaces and operators are

$$
S=\mathbb N^{<\mathbb N},\quad o=\varnothing,\quad
A=\ell^1(S),\quad Z=\ell^1(S\times S),\quad V=\mathbb R\times Z,
\qquad D_T:A\longrightarrow A.
$$

For a well-founded tree, the tree-kernel argument proves that the bounded operator is injective. Its scalar-tagged symmetric tensor subspace is

$$
V_T=\left\{\bigl(K(o,o),(D_T\otimes\mathrm{id})K\bigr):
K\in Z\text{ is symmetric and has finite tensor rank}\right\}.
$$

Equivalence on the source space means that the difference belongs to this subspace. `TensorFamily.lean` defines these specific witnesses as `treeOperator`, `tensorSubspace`, and `sourceRelation`.

Ordinary source unboundedness uses the nilpotent central extension from the vendored `NoBorelUpperBound` proof. The continuous map `theta` records two residual coordinates and a corrected central coordinate. The coset calculation identifies a nilpotent coset relation with equality of the residuals together with the tensor coset relation on the corrected central coordinates. Consequently, a common Borel upper bound for all well-founded tensor relations would give a common Borel upper bound for the corresponding nilpotent relations after adding the equality coordinates. Category transfer would make designated-element membership Borel. Tree-kernel computations identify this membership set with the non-Borel set of ill-founded trees. This contradiction proves `source_family_unbounded` for the concrete tensor family.

The compactification uses product coordinates and a countable product of circles:

$$
I=\{*\}\sqcup(S\times S),\quad X=\mathbb R^I,
\quad K=(\mathbb R/\mathbb Z)^{I\times\mathbb N},\qquad
j(u)_{i,n}=\frac{u_i}{n+1}\pmod{\mathbb Z}.
$$

The coordinate map from the source space is continuous and injective. The displayed homomorphism is also continuous and injective, because dividing a nonzero real coordinate by sufficiently large positive integers cannot always give integers. All positive integers in the denominator give a separating compactification variant of the factorial denominators in the manuscript. The group is fixed independently of the tree, compact, metrizable, and abelian. Its measure is an actual normalized Haar measure. Lean uses `Multiplicative` to express this additive product as a group for the existing subgroup and coset definitions.

For any bounded injective operator, the coordinate image of its scalar-tagged tensor subspace has an exact representation

$$
\operatorname{coordinates}(V_D)=B\setminus N,
\qquad B,N\text{ countable unions of compact subsets of }X.
$$

The envelope is the union of all pieces with an integer bound on the sum of absolute coordinates and an integer finite-rank bound. The absolute-sum condition gives a closed subset of a product of compact intervals and recovers an actual summable matrix. The rank condition is closed because it consists of vanishing finite minors. The rank lemmas prove that this coordinate rank is the finite-dimensional row-space rank and, equivalently, finite tensor rank.

The obstruction removes precisely the points failing a universal chart consistency test. For every possible finite row selector and operator-coordinate pivot, if the matrix rank is at most the pivot size and its determinant is nonzero, require

$$
dR=(D\otimes\mathrm{id})L,\qquad
L^{\mathsf T}=L,\qquad d\lambda=L(o,o),
$$

where the numerator is the finite tensor expression formed from the pivot adjugate and selected rows. A nonzero pivot and the rank bound force those rows to span. Genuine images satisfy every applicable test by reconstruction; conversely, an actual row basis and injectivity of the operator yield an applicable nonzero pivot, and the three equations supply the symmetric finite tensor preimage. Rank zero is included: its empty determinant is one and its numerator vanishes, forcing the scalar tag to vanish along with the matrix.

On each compact coordinate ball, operator row evaluations are Baire-one functions. This is proved from the summable expansion into coordinate vectors: applying a bounded operator to finite partial sums gives continuous finite-coordinate approximants converging pointwise to the evaluation. All chart coordinates are finite polynomial combinations of these evaluations. The equality sets are therefore G-delta. A conditional chart is the union of rank failure, zero determinant, and satisfaction of the equations, so the universal test is G-delta. Its complement on a compact ball is F-sigma and hence a countable union of compact sets. Taking the union over the balls gives the obstruction above.

The homomorphism carries the two compact-union sets to F-sigma sets in the compact target. Its injectivity preserves their difference. Define the fixed compact subgroup family by

$$
H_T=j\bigl(\operatorname{coordinates}(V_T)\bigr).
$$

Each subgroup is a difference of two F-sigma sets. The same holds for its coset graph by preimage under the continuous group-difference map. In metrizable spaces these sets are Delta-three. The source-to-compact homomorphism reduces every source relation to its compact relation, so ordinary source unboundedness gives ordinary compact-family unboundedness. The formal witnesses used in the final theorem are exactly `compactGroup` and `compactFamily`.

For Haar amplification, the fixed target is an almost-everywhere power represented on Baire-space codes. A fixed dense sequence in real integrable-function space gives measurable codes for jointly Borel integrable families. At each stage, choose the least approximation index with integral error less than the corresponding geometric bound. Measurability of the integral errors proves measurability of the choices. Summability proves almost-everywhere recovery of each section. A bounded Borel embedding of the original target into the real line, together with a total Borel inverse, reduces arbitrary nonempty standard Borel targets to this integrable real construction.

Every code has a total jointly Borel interpretation, defined using an extended-real limit superior. Two codes are related when their decoded sections are equivalent in the original relation almost everywhere. This is an equivalence relation, and its graph is Borel because the measure of the disagreement section is measurable in the codes. The formal target is this Baire-space relation. The formalization does not construct a topology on a quotient space of measurable functions.

Extend a reduction on a Borel conull domain to a Borel map on the whole compact group. Code the jointly Borel family

$$
a(x,t)=g(tx).
$$

For each fixed pair, right Haar translations carry the conull domain back to conull sets, and simultaneous left multiplication preserves coset membership. After intersecting these conull sets with the two decoding sets, equivalence of decoded sections agrees with the original coset relation. Thus coding gives a whole-group reduction to one fixed amplified target. This target is chosen before the subgroup and the domain.

Finally choose a tree whose compact coset relation does not reduce to the amplified target. Any reduction on any conull domain to the original target would amplify to a contradictory whole-group reduction. If the target space is empty, conull sets are nonempty, so no reduction exists. This proves Theorem 1.1 with all domains excluded by the same selected tree.

The principal file responsibilities are as follows.

| Files | Mathematical role |
| --- | --- |
| `ModNullProof/TensorFamily.lean` | The actual tree operators and scalar-tagged tensor subspaces. |
| `ModNullProof/LinearCosets.lean`, `OrdinaryUnbounded.lean` | The nilpotent correction map and category-transfer contradiction for the source family. |
| `ModNullProof/Coordinates.lean`, `CoordinateBounds.lean` | Product coordinates, compact absolute-sum balls, and recovery of summable source points. |
| `ModNullProof/WeakTensorRank.lean`, `WeakTensorCharts.lean` | Closed-minor rank bounds and the universal chart membership characterization. |
| `ModNullProof/BaireOneComplexity.lean`, `WeakTensorCoordinates.lean` | Real Baire-one complexity and the actual operator-coordinate approximations. |
| `ModNullProof/KSigmaComplexity.lean`, `TensorCompact.lean` | The compact envelope, failed-test obstruction, and exact difference-of-compact-unions representation. |
| `ModNullProof/CompactEmbedding.lean`, `CompactCosets.lean` | The countable torus, normalized Haar measure, subgroup images, and graph complexity. |
| `ModNullProof/CompactUnbounded.lean`, `CompactFamily.lean` | Transfer of ordinary unboundedness and the fixed low-complexity compact family. |
| `ModNullProof/AEPowerRealCodes.lean`, `AEPowerBorel.lean` | Measurable dense-function coding and the fixed Borel almost-everywhere power. |
| `ModNullProof/HaarAmplification.lean`, `ConullAssembly.lean` | Haar translation and the final order of quantifiers. |
| `Solutions/HaarAmplification.lean`, `CompactCosetUnboundedness.lean`, `Main.lean` | The three public target statements. |

The development targets Lean 4.30.0 and Mathlib revision `c5ea00351c28e24afc9f0f84379aa41082b1188f`. The complete local build and the final exact-statement and axiom audits are recorded by the repository verification files. The mathematical explanations for the three targets are in `explanation-haar.md`, `explanation-compact.md`, and `explanation-main.md`.
