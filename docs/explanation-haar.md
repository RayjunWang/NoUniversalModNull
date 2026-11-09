$$
\begin{gathered}
\forall\text{ compact metrizable Haar probability groups }K
\text{ and Borel equivalence relations }F\text{ on nonempty standard Borel spaces},\\
\exists Q\text{ a standard Borel equivalence relation}\;
\forall H\leq K\text{ Borel}\;
\forall C\subseteq K\text{ Borel with }\lambda(C)=1,\\
E_H^K\mathbin{\upharpoonright}C\leq_B F
\quad\Longrightarrow\quad E_H^K\leq_B Q.
\end{gathered}
$$

The target is chosen before the subgroup and the conull domain. The idea is to encode the entire family of translates of a reduction on the domain. Almost every translate returns any fixed pair to that domain, and simultaneous left multiplication preserves the coset relation.

We construct the target on Baire space. Start with a fixed dense sequence in the real integrable-function space of Haar measure. Every sequence of indices is given a total Borel interpretation by taking the pointwise extended-real limit superior of the corresponding representatives and converting it to a real value. The interpretation is jointly Borel in the code and the group element, including codes that do not describe convergent approximations.

For a jointly Borel family of integrable real functions, choose at each parameter and each stage the least index from the dense sequence whose integral absolute error satisfies

$$
\int |b_{c(x)(n)}(t)-a(x,t)|\,d\lambda(t)<2^{-n}.
$$

The integral error is measurable in the parameter, so this least-index choice is measurable. The errors are summable. Integrating their sum shows that the pointwise error sum is finite almost everywhere, which forces the approximants to converge to the required section almost everywhere. Therefore the Borel interpretation of the chosen code recovers every section almost everywhere.

Embed the nonempty standard Borel target space into the real line by a bounded Borel embedding, and choose a total Borel inverse that agrees with the inverse on the embedded range. Boundedness gives integrability, so the real coding result supplies codes for every jointly Borel family taking values in the target space. Decoding through the Borel inverse recovers each section almost everywhere. No topology on a space of equivalence classes of measurable functions is needed for this construction.

Define the equivalence relation on codes by almost-everywhere pointwise equivalence of their decoded sections:

$$
s\;Q\;r
\quad\Longleftrightarrow\quad
F(\operatorname{decode}(s,t),\operatorname{decode}(r,t))
\text{ for almost every }t.
$$

Reflexivity, symmetry, and transitivity follow from the corresponding properties of the original relation and finite intersections of conull sets. Its graph is Borel: the decoded disagreement set is Borel in the two codes and the group variable, and the measure of its sections is a measurable function of the codes. The graph is the zero set of that section-measure function. Baire space is standard Borel, so this gives the required fixed standard Borel target.

Now let a reduction on a Borel conull domain be given. Extend it to a Borel map on the entire group, using nonemptiness of the target, and apply the parameter coding theorem to

$$
a(x,t)=g(tx).
$$

This produces a Borel map assigning to each group element a code for its translated section. Fix two group elements. Right translations preserve Haar null sets on a compact group; hence both translated points lie in the original domain for almost every translation parameter. On that conull set, the extension agrees with the original reduction. Moreover,

$$
(tx)^{-1}(ty)=x^{-1}y.
$$

After also intersecting the two conull decoding sets, the original reduction therefore gives

$$
F(\operatorname{decode}(c(x),t),\operatorname{decode}(c(y),t))
\quad\Longleftrightarrow\quad x^{-1}y\in H
$$

for almost every translation parameter. The right-hand side is independent of that parameter. Since Haar measure is a probability measure, it follows that equivalence of the two codes holds exactly when the two original points are in the same coset. Thus the code map is a Borel reduction of the whole-group coset relation to the fixed target. The argument requires neither commutativity of the group nor invariance of the conull domain.
