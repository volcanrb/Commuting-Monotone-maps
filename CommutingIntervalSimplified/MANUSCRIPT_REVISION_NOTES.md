# Applied revision record for `common_fixed_points_simplified.tex`

These are mathematical or expository changes discovered while designing the
formal proof.  The coordinated journal revision has now been applied.  This
file preserves the mathematical rationale and the formerly insertion-ready
text as an audit history; implementation commentary remains outside the paper
itself.

The final audited manuscript snapshot has 989 lines and SHA-256
`574FCF260AF68466A26F534BC4566F2803ED9D13931D99F3225E153BFEF38B03`.
Both confirmed corrections and all eleven tracked clarifications are present.

## Applied confirmed corrections

### 1. The common-positive-iterate citation was corrected

In the earlier `lem:common-iterate`, the inverse limit `X_T` was
arc-like/chainable, not a tree, so the stated appeal to Bogatyi--Frolkina
Theorem 3 did not justify a
point fixed by both auxiliary homeomorphisms.  This is especially important
because arbitrary chainable continua can carry commuting homeomorphisms with
no common fixed point.

The final manuscript uses the following mathematical route:

> The periodic homeomorphism `V` acts on the arc-like, hence tree-like,
> continuum `X_T`.  By Fugate--McLean, Theorem 1.5, `Fix(V)` is a nonempty
> continuum.  Since `U` commutes with `V`, it preserves this set.  For each
> `epsilon>0`, choose a sufficiently late coordinate projection.  Its image
> of `Fix(V)` is an interval.  Comparing the projected displacement of `U` at
> preimages of the two endpoints gives, by the intermediate value theorem, a
> point whose projected displacement is zero; if the projected interval is a
> singleton, every point works.  The inverse-limit metric then makes the full
> displacement smaller than `epsilon`.  Compactness and `epsilon -> 0` give a
> point fixed by both `U` and `V`.  The displayed Bezout factorizations show
> that it is fixed by both lifted maps, and its zeroth coordinate is a common
> fixed point downstairs.

Use the precise citation: J. B. Fugate and T. B. McLean, *Compact groups of
homeomorphisms on tree-like continua*, Trans. Amer. Math. Soc. 267 (1981),
609--620, Theorem 1.5,
doi:10.1090/S0002-9947-1981-0626493-5.  Hamilton is not needed because the
fixed point of `U` is proved directly.  The standalone Lean development proves
its specialized fixed-set input internally rather than assuming this
publication.

### 2. The square-fixed-point endpoint gap was corrected

In the earlier `lem:irreducible`, after choosing `a < z < b` with `f(a)=v`
and `f(b)=u`, the prose used strict endpoint inequalities which need not hold
when `a=u` or `b=v`.  The final manuscript uses the endpoint-complete argument
recorded below.

> If `a=u` and `b=v`, then `f^2(u)=u`, so `u` and `z` are two fixed points.
> If `a>u`, then `f^2(a)=u<a`, while `f^2(u)>=u`; the intermediate value
> theorem gives a fixed point of `f^2` in `[u,a]`, distinct from `z`.  If
> `a=u` but `b<v`, then `f^2(b)=v>b`, while `f^2(v)<=v`; the intermediate
> value theorem gives a fixed point in `[b,v]`, again distinct from `z`.

The corresponding Lean fact is proved as
`intervalSurjection_square_has_two_fixedPoints` and is used by the completed
extremal argument.

## Applied LaTeX replacements

The blocks in this section record the mathematics used in the coordinated
revision.  The final TeX incorporates them, with small journal-style copyedits.
Declaration names and proof-assistant bookkeeping remain outside the paper.

### Applied replacement A: the complete common-positive-iterate argument

Applied in the final TeX's common-positive-iterate section.  The corrected
citation is **Theorem 1.5**, not Bogatyi--Frolkina Theorem 3; the following
block records the replacement proof.

```latex
We shall use the theorem of Fugate--McLean that the fixed-point set of a
periodic homeomorphism of a tree-like continuum is a nonempty continuum
\cite[Theorem~1.5, p.~613]{FugateMcLean}.

\begin{lemma}[Common positive iterates]\label{lem:common-iterate}
If commuting continuous interval maps $F,G$ satisfy $F^m=G^n$ for some
$m,n\geq1$, then $F,G$ have a common fixed point.
\end{lemma}

\begin{proof}
Put $T=F^m=G^n$ and
\[
J_\infty=\bigcap_{r\geq0}T^r(\I).
\]
The sets $T^r(\I)$ are nested nonempty compact intervals.  Moreover,
$T(J_\infty)=J_\infty$.  One inclusion is immediate.  For the other, if
$y\in J_\infty$, then the sets
\[
T^{-1}(y)\cap T^r(\I),\qquad r\geq0,
\]
are nested nonempty compact sets: nonemptiness follows from
$y\in T^{r+1}(\I)$.  A point of their intersection is a preimage of $y$ in
$J_\infty$.  Commutation gives
$F(J_\infty),G(J_\infty)\subseteq J_\infty$.  If $J_\infty$ is a singleton,
its point is fixed by both maps, so assume that it is nondegenerate.

Form the natural extension
\[
X_T=\{(x_0,x_1,\ldots)\in J_\infty^{\mathbb N_0}:
          T(x_{i+1})=x_i\text{ for all }i\geq0\}.
\]
It is a nonempty compact connected metric space.  For example, the sets in
$J_\infty^{\mathbb N_0}$ obtained by imposing only the first $N$ bonding
equations are nested nonempty compact connected sets: projection to the
coordinates $x_N,x_{N+1},\ldots$ identifies each of them with a product of
copies of $J_\infty$.  Their intersection is $X_T$.  Give $X_T$ the metric
\[
d_X(x,y)=\sum_{i=0}^{\infty}2^{-i-1}|x_i-y_i|.
\]
Every coordinate projection $\pi_N:X_T\to J_\infty$ is onto, because
$T|_{J_\infty}$ is onto.  If $\pi_N(x)=\pi_N(y)$, the bonding equations give
$x_i=y_i$ for $0\leq i\leq N$, and hence
\[
d_X(x,y)\leq\sum_{i>N}2^{-i-1}=2^{-N-1}.
\]
Thus $X_T$ admits arbitrarily fine maps onto an interval; it is arc-like and
hence tree-like.

The shift
\[
\Sigma(x_0,x_1,\ldots)=(T(x_0),x_0,x_1,\ldots)
\]
is a homeomorphism.  Coordinatewise application defines commuting maps
$\widehat F,\widehat G:X_T\to X_T$, and
\[
\widehat F^m=\Sigma=\widehat G^n.
\]
A continuous selfmap whose positive power is a homeomorphism is itself a
homeomorphism, so negative powers of $\widehat F$ and $\widehat G$ are
available.

Write $m=dm_0$, $n=dn_0$, where $\gcd(m_0,n_0)=1$, and choose
$r,s\in\mathbb Z$ with $rn_0+sm_0=1$.  Set
\[
U=\widehat F^r\widehat G^s,\qquad
V=\widehat F^{m_0}\widehat G^{-n_0}.
\]
Then
\[
V^d=\id,\qquad
\widehat F=U^{n_0}V^s,\qquad
\widehat G=U^{m_0}V^{-r}.
\]
By the quoted Fugate--McLean theorem,
$\mathcal D=\Fix(V)$ is a nonempty compact connected subset of $X_T$.
Since $U$ commutes with $V$, it preserves $\mathcal D$.

We prove directly that $U|_{\mathcal D}$ has a fixed point.  Given
$\varepsilon>0$, choose $N$ with $2^{-N-1}<\varepsilon$.  Connectedness gives
$\pi_N(\mathcal D)=[\alpha,\beta]$.  If $\alpha=\beta$, then every
$z\in\mathcal D$ has $\pi_N(Uz)=\pi_N(z)$ and hence
$d_X(Uz,z)<\varepsilon$.  If $\alpha<\beta$, choose
$z_\alpha,z_\beta\in\mathcal D$ over the two endpoints.  The continuous
function
\[
z\longmapsto \pi_N(Uz)-\pi_N(z)
\]
is nonnegative at $z_\alpha$ and nonpositive at $z_\beta$; its image of the
connected set $\mathcal D$ therefore contains zero.  Again there is
$z_\varepsilon\in\mathcal D$ with
$d_X(Uz_\varepsilon,z_\varepsilon)<\varepsilon$.  Take
$\varepsilon_j\downarrow0$ and pass to a convergent subsequence of the
$z_{\varepsilon_j}$ in the compact set $\mathcal D$.  Continuity of $U$ shows
that its limit $z$ satisfies $U(z)=z$.
Since also $V(z)=z$, the Bezout factorizations show that
$\widehat F(z)=z=\widehat G(z)$.  The zeroth coordinate of $z$ is a common
fixed point of $F$ and $G$.
\end{proof}
```

Add the following bibliography entry:

```latex
\bibitem{FugateMcLean}
J.~B. Fugate and T.~B. McLean,
\emph{Compact groups of homeomorphisms on tree-like continua},
Trans. Amer. Math. Soc. \textbf{267} (1981), 609--620,
doi: \href{https://doi.org/10.1090/S0002-9947-1981-0626493-5}
{10.1090/S0002-9947-1981-0626493-5}.
```

### Applied replacement B: the endpoint-complete square-fixed-point paragraph

Applied in the final TeX's irreducibility proof.  The replacement paragraph is:

```latex
To prove the assertion, write the interval as $[u,v]$.  If $f$ already has
two fixed points, there is nothing to prove.  Otherwise let $z$ be its unique
fixed point.  It lies in $(u,v)$.  Indeed, if $z=u$, then
$f(x)<x$ for every $x>u$, whereas a preimage of $v$ supplied by surjectivity
would satisfy the opposite inequality; the case $z=v$ is symmetric.
Uniqueness and the endpoint inequalities now give
\[
f(x)>x\quad(u\leq x<z),\qquad
f(x)<x\quad(z<x\leq v).
\]
Choose $a<z<b$ with $f(a)=v$ and $f(b)=u$; the displayed inequalities force
the indicated locations of these preimages.  Since
$f(a)=v\geq b$ and $f(z)=z<b$, the intermediate value theorem gives
$c\in[a,z)$ with $f(c)=b$.  Hence $f^2(c)=u\leq c$, while
$f^2(u)\geq u$.  If equality already holds at an endpoint, that endpoint is
fixed by $f^2$; otherwise the intermediate value theorem gives a zero of
$f^2(x)-x$ in $(u,c)$.  In either case this fixed point lies strictly to the
left of $z$, while $z$ itself is fixed by $f^2$.  Thus $f^2$ has at least two
fixed points.
```

### Applied replacement C: state the minimal-core normalization in the correct direction

The earlier statement of `lem:linearize` called the initial restriction a
factor of the original system.  The final statement uses the following
direction; the rest of the branch-length proof applies to the normalized pair.

```latex
\begin{lemma}[Common constant-slope factor]\label{lem:linearize}
Every counterexample to Theorem~\ref{thm:main} has a nondegenerate compact
common invariant interval $J$ which is minimal among such intervals.  After
affinely conjugating the restrictions $P|_J,Q|_J$ to maps of $\I$, the
resulting commuting onto minimal-core counterexample has a common monotone
factor which is a pair of commuting onto finite-piece PL maps of constant
absolute slopes $C,D>1$, has no common fixed point, and has no proper nonempty
compact common invariant interval.
\end{lemma}
```

The final TeX also uses the following fully explicit opening of the
normalization proof:

```latex
Let $\mathscr J$ be the set of pairs $(a,b)$ with $0\leq a\leq b\leq1$ for
which both $P([a,b])$ and $Q([a,b])$ are contained in $[a,b]$.
It is nonempty because $(0,1)\in\mathscr J$.  It is closed: if
$(a_k,b_k)\to(a,b)$ with $(a_k,b_k)\in\mathscr J$ and $x\in[a,b]$, choose
$x_k\in[a_k,b_k]$ with $x_k\to x$; continuity gives
$P(x)=\lim P(x_k)\in[a,b]$, and likewise for $Q$.  Choose $(a,b)\in\mathscr J$
of least length and put $J=[a,b]$.  The interval $J$ is nondegenerate, since
an invariant singleton would be a common fixed point.  Least length makes it
inclusion-minimal.

The image $P(J)$ is a nonempty compact interval contained in $J$, and
\[
P(P(J))\subseteq P(J),\qquad Q(P(J))=P(Q(J))\subseteq P(J).
\]
Thus $P(J)$ is another compact common invariant interval, so minimality gives
$P(J)=J$; similarly $Q(J)=J$.  Let $\eta:\I\to J$ be the increasing affine
homeomorphism and replace $P|_J,Q|_J$ by
$\eta^{-1}P\eta,\eta^{-1}Q\eta$.  These normalized maps are commuting and
onto, have no common fixed point, and have no proper nonempty compact common
invariant interval.  We retain the symbols $P,Q$ for them.  Notice that
$\eta$ embeds this normalized restriction into the original system; the
monotone factor used below is a factor of the normalized pair.
```

### Applied replacement D: construct and verify the component-collapse quotient

Applied in `lem:irreducible` in place of the earlier compressed collapse
sentence and regularity assertion.  This was the main compression found in the
irreducibility proof.

```latex
Write the component-unions, in their order on the interval, as
\[
K_r=[\alpha_r,\beta_r]\qquad(1\leq r\leq N),
\quad
\beta_r<\alpha_{r+1}.
\]
There are at least two graph components.  Translation of the phase labels is
a graph automorphism and satisfies
$P(D_{i,j})=D_{i+1,j}$ and $Q(D_{i,j})=D_{i,j+1}$.  Consequently $P$ and $Q$
permute the intervals $K_r$.

Put $E=\bigcup_rK_r$ and
\[
\kappa=1-\sum_{r=1}^N(\beta_r-\alpha_r)>0.
\]
Write $|K_r\cap[0,x]|$ for the length of that intersection, with value zero
when it is empty, and define
\[
\pi(x)=\frac{1}{\kappa}
 \left(x-\sum_{r=1}^N\bigl|K_r\cap[0,x]\bigr|\right).
\]
Then $\pi:\I\to\I$ is a continuous nondecreasing PL surjection, constant on
each $K_r$ and strictly increasing on every complementary gap.  Its only
non-singleton fibres are the intervals $K_r$.  Since each generator sends
every $K_r$ into one of the $K_s$, both generators respect the fibres of
$\pi$.  There are therefore unique continuous maps $\bar P,\bar Q:\I\to\I$
such that
\[
\pi P=\bar P\pi,\qquad \pi Q=\bar Q\pi.
\]
Surjectivity of $P,Q$ and $\pi$ makes $\bar P,\bar Q$ onto, and surjectivity
of $\pi$ transfers the commutation relation to the descended maps.

It remains to record their finite-piece PL regularity.  On each complementary
gap, $\pi$ has an affine inverse.  A flat-free finite-piece PL map has finite
fibres.  Refine that gap at the finitely many affine breakpoints of $P$ and
$Q$ and at the preimages of all endpoints $\alpha_r,\beta_r$.  On a resulting
cell, the image under a generator lies
either in one $K_r$, in which case its descended map is constant, or in a
single complementary gap, in which case
\[
\bar P=\pi\circ P\circ(\pi|_J)^{-1}
\quad\text{or}\quad
\bar Q=\pi\circ Q\circ(\pi|_J)^{-1}
\]
is affine.  There are only finitely many such cells, so both descendants are
finite-piece PL.  The factor and fixed-point arguments from
Lemma~\ref{lem:linearize}, including
$\Fix(\bar T)=\pi(\Fix(T))$ for every word $T$, show that the descended pair
is again a minimal counterexample.
```

After the strict fixed-count decrease, the final TeX uses the following
expanded relinearization step:

```latex
The quotient pair need not have constant slopes.  Apply
Lemma~\ref{lem:linearize} to it.  Because the quotient pair is already
minimal on its common invariant core, the preliminary minimal-core
restriction in that lemma is the whole interval.  The resulting
constant-slope system is therefore a monotone factor of the quotient pair.
Composing this coordinate with the collapse coordinate and with the original
factor coordinate shows that the resulting pair still belongs to the class
of constant-slope minimal-counterexample factors of $(P_0,Q_0)$.  Both slopes
are greater than one, and the exact fixed-point identity for the composite
factor coordinate shows that the number of fixed points of $P^{2L}$ cannot
increase.  This contradicts the defining minimality of $\mu$.
```

### Applied replacement E: intrinsic turns and quantified regularity terminology

The final TeX places the first paragraph before `lem:finite-postcritical` and
the second before `lem:two-scale`.  These are mathematical definitions; the
particular finite partitions used to encode them in Lean do not belong in the
paper.

```latex
For a flat-free finite-piece PL map $T$, an interior point $x$ is a
\emph{turn} if, on sufficiently small left- and right-hand intervals at $x$,
$T$ is affine with nonzero slopes of opposite signs.  This definition is
intrinsic: inserting a redundant vertex into an affine branch does not create
a turn.  We write
\[
E(T)=\{0,1\}\cup\Turn(T),\qquad \mathcal V(T)=T(E(T)).
\]
Two numbers $a,b>1$ are \emph{multiplicatively independent} when
$a^m\neq b^n$ for every pair of positive integers $m,n$.
```

```latex
A map $\Phi:[0,\infty)\to\I$ is \emph{locally finite-piece affine of unit
speed} if every compact parameter interval admits a finite subdivision on
whose cells $\Phi$ is affine with slope $+1$ or $-1$.  It is
\emph{eventually periodic} if there are $T_0\geq0$ and a period $\tau>0$ such
that $\Phi(t+\tau)=\Phi(t)$ for every $t\geq T_0$.
```

### Applied replacement F: simultaneous reflection and the finite side action

The final TeX replaces the earlier orientation sentence and expands the
subsequent directed-side paragraph as recorded below.

```latex
Choose consecutive $p<c$ in $X=\Fix(H)$.  Since $H(x)-x$ has no zero in
$(p,c)$, it has a constant strict sign there.  If that sign is negative, let
$\iota(x)=1-x$ and replace both generators simultaneously by
\[
\widetilde P=\iota P\iota,\qquad \widetilde Q=\iota Q\iota.
\]
For every word $W$ in the two generators one has
$\widetilde W=\iota W\iota$.  Thus the conjugacy preserves continuity,
onto-ness, finite-piece PL structure, constant slope magnitudes, commutation,
the absence of a common fixed point, all fixed-set cardinalities, and
minimality of the common invariant core.  It also carries nondegenerate
common invariant intervals for the returned powers bijectively to such
intervals, so \eqref{eq:irreducible} is preserved.  Finally,
\[
(\iota H\iota)(x)-x=-\bigl(H(1-x)-(1-x)\bigr),
\]
and the reflected gap is $(1-c,1-p)$.  After this simultaneous conjugacy and
a relabelling, we may therefore assume $H(x)>x$ on $(p,c)$.

Represent a directed side by $(x,\sigma)$, where $x\in X$,
$\sigma\in\{-1,+1\}$, and $x+\sigma t\in\I$ for all sufficiently small
$t>0$.  If a flat-free PL map $T$ carries this side, then for some
$\delta>0$ its restriction to $x+\sigma(0,\delta)$ is affine with nonzero
slope.  Its image consequently contains a punctured one-sided interval at
$T(x)$.  Such an image cannot be contained in both the left and the right
side at $T(x)$, so the carried target side is unique.  Shrinking source
intervals shows that side transport respects composition.

If $(x,\sigma)$ is repelling for $H$, the identity $PH=HP$ transports its
positive $CD$-dilation germ to a repelling side based at $P(x)$; the same is
true for $Q$.  Hence $P$ and $Q$ induce well-defined maps $P_*,Q_*$ on the
finite set of repelling sides.  Composition compatibility and
$PQ=QP=H$ give
\[
Q_*P_*=H_*=\id=P_*Q_*.
\]
Thus the two side actions are inverse permutations.  There are at most
$N\leq2\#X\leq2\nu_0$ states.  Every cycle length is at most $N$, so the
order of either permutation divides $N!$, which in turn divides
$(2\nu_0)!=L$.  The returned maps $A=P^L$ and $B=Q^L$ therefore fix the
chosen right side.  Their constant absolute slopes and preservation of its
orientation give the positive germs
\[
A(p+t)=p+at,\qquad B(p+t)=p+bt
\]
for all sufficiently small $t\geq0$.
```

### Applied replacement G: returned hulls, scale comparison, and ray regularity

The final TeX uses the following expanded returned-hull, scale-comparison, and
ray-regularity argument.

```latex
Let $U=\bigcup_{n\geq0}I_n$ and $K_0=\cl U$.  Each $I_n$ is a compact
interval, the intervals are nested, and $I_0$ has positive length.  Hence
$K_0$ is a nondegenerate compact interval.  The inclusions already proved
give $A(U),B(U)\subseteq U$.  Continuity therefore gives
$A(K_0),B(K_0)\subseteq K_0$.  Moreover,
\[
R(U)=\bigcup_{n\geq0}I_{n+1}=U,
\]
where the last equality uses $I_0\subseteq I_1$.  Continuity gives
$R(K_0)\subseteq\cl R(U)=K_0$.  Conversely, $R(K_0)$ is compact and hence
closed, and it contains $R(U)=U$; therefore it contains $K_0=\cl U$.  Thus
$R(K_0)=K_0$.  Since $R=AB=BA$,
\[
K_0=AB(K_0)\subseteq A(K_0)\subseteq K_0,
\qquad
K_0=BA(K_0)\subseteq B(K_0)\subseteq K_0.
\]
Both returned maps are onto $K_0$, so \eqref{eq:irreducible} gives
$K_0=\I$.  Hence $U$ is dense.
```

The final TeX replaces the earlier "choose a smaller initial interval"
shorthand by the following radius-controlled argument:

```latex
Suppose that $a^m=b^n=q$ for positive integers $m,n$.  Choose a germ radius
$\varepsilon_0>0$ on which the three formulas for $A,B,R$ used above are
valid.  By induction on the iterate, after choosing
\[
0<\delta\leq
\min\{\varepsilon_0/s,\varepsilon_0/a^m,
                     \varepsilon_0/b^n\},
\]
and decreasing it further if necessary, all intermediate points remain in
the corresponding germ intervals and
\[
A^m(p+t)=p+qt=B^n(p+t)\qquad(0\leq t\leq\delta).
\]
The original $A$-, $B$-, and $R$-germ estimates also remain valid on
$J_0=[p,p+\delta]$.  Repeating the returned-hull construction with $J_0$ in
place of $I_0$ shows that $\bigcup_{k\geq0}R^k(J_0)$ is dense.  The maps
$A^m$ and $B^n$ commute with $R$ and agree on $J_0$, hence agree on every
$R^k(J_0)$ and, by continuity, on all of $\I$.  Thus
$P^{Lm}=Q^{Ln}$, contrary to Lemma~\ref{lem:common-iterate}.
```

After defining $\Psi$, the final TeX gives its local PL regularity through the
following compact-uniform argument:

```latex
The representatives are compatible because
$R(p+x)=p+sx$ on the chosen germ.  Let $[u,v]\subset[0,\infty)$ be compact
and choose one $n$ with $v<s^n\varepsilon$.  The same representative
\[
t\longmapsto R^n\left(p+\frac{t}{s^n}\right)
\]
then defines $\Psi$ throughout $[u,v]$.  Pull a finite affine partition for
$R^n$ back by $t=s^n(x-p)$.  Every affine branch of $R^n$ has slope of
absolute value $s^n$, so every pulled-back branch of $\Psi$ has slope of
absolute value one.  This proves, uniformly on each compact parameter
interval, continuity and locally finite-piece affine unit speed.
```

### Applied replacement H: regularity in the periodic-fold extension

The final TeX expands both short regularity steps in `lem:periodic-fold`.  The
following records the text used after defining the two-sided extension $\psi$:

```latex
If $m$ and $m'$ are two admissible choices, assume $m'\geq m$; repeated use
of the eventual $P_*$-periodicity shows that
$\Psi(t+m'P_*)=\Psi(t+mP_*)$, so the definition is independent of the
choice.  Given $t_0\in\mathbb R$, choose one $m$ and a neighbourhood $W$ of
$t_0$ such that $W+mP_*\subset[T_0,\infty)$.  On $W$ the map $\psi$ is the
translate $t\mapsto\Psi(t+mP_*)$.  It is therefore continuous and admits a
finite affine unit-speed partition on every compact subinterval of $W$.
Thus $\psi$ is a nonconstant periodic locally finite-piece affine path of
unit speed.
```

The final TeX verifies local unit speed of $v_P$ and $v_Q$ as follows:

```latex
The paths $v_P(t)=P\psi(t/C)$ and $v_Q(t)=Q\psi(t/D)$ are onto and periodic.
To check local unit speed for $v_P$, start with a compact parameter interval,
take a finite unit-speed affine partition for $\psi$ on the corresponding
scaled interval, and pull it back by $t\mapsto t/C$.  Refine the pulled-back
partition at the preimages of the finitely many affine breakpoints of $P$.
On every resulting cell the inner path has slope $\pm1/C$ and the relevant
branch of $P$ has slope of absolute value $C$; their composite therefore has
slope $\pm1$.  This refinement is finite.  The argument for $v_Q$ is
identical, with $D$ in place of $C$.
```

## Incorporated clarification checklist

1. [x] The normalization step now distinguishes the derived normalized
   restriction from a factor of the original global system.  “Factor” is
   reserved for the subsequent monotone quotient.
2. [x] `Turn(T)` is defined intrinsically as an interior reversal of
   orientation, so the vertex-value composition identity is not phrased in
   terms of arbitrary redundant PL partition vertices.
3. [x] Multiplicative independence is stated with positive integer exponents:
   `a^m != b^n` for every `m,n >= 1`.
4. [x] The common constant-slope factor proof explains that a common fixed
   point downstairs has a common invariant interval as its fibre, and that a
   nonconstant quotient makes this fibre proper, contradicting minimality.
5. [x] “Locally finite-piece affine of unit speed” and “eventually periodic”
   are defined with their compact-local-finiteness, positive-period, and
   nonnegative-ray quantifiers before use.
6. [x] The component-collapse proof records positivity of
   `L = (2 nu_0)!` and derives the component permutations from the bijective
   phase-label shifts preserving interval intersections.
7. [x] The orientation change in `lem:two-scale` is a simultaneous reflection
   conjugacy of both generators.  The proof lists every transported property,
   and the final theorem explicitly conjugates the resulting common fixed
   point back when the reflected alternative occurs.
8. [x] The directed-side relation is defined by an exact affine one-sided germ;
   uniqueness of the target side and compatibility with composition are proved
   before `P_*` and `Q_*` are treated as inverse finite permutations.
9. [x] The returned-hull proof gives both inclusions in `R(K_0)=K_0`: continuity
   gives the forward inclusion, while compactness and closedness of `R(K_0)`
   give the reverse inclusion.  Nested-interval and positive-seed arguments
   supply nondegeneracy.
10. [x] The scale-equality argument chooses an explicit positive radius on
    which the original `A`, `B`, and `R` germs and the two iterated germs all
    remain valid, then repeats the density/globalization construction on that
    restricted seed.
11. [x] The stabilized ray is defined by an admissible representative
    independent of depth.  On each compact parameter interval one common depth
    is chosen, and a finite affine partition for `R^n` is pulled back to prove
    continuity and locally finite-piece unit speed; the `n=0` representative
    also proves the initial identity `Psi(t)=p+t`.

## Checks which passed

- The current manuscript already uses the linear ordered increment
  `S(max{u,v})-S(min{u,v})`; an earlier audit warning that it used absolute
  value was a version-synchronization mistake and is withdrawn.
- With that ordered increment, the revised finite-dimensionality argument using
  `V_N = {H^N(c_i)}` is valid: completed branch increments vanish, and the
  remaining increment is bounded by the sup norm.
- The current manuscript now derives that `Fix(PQ)` has at least two points
  before choosing consecutive fixed points.
- Durand Theorem 9 is the appropriate general growing/nonerasing theorem; no
  primitivity assumption is needed after restricting to the occurring
  alphabet.  The final TeX explicitly states the incidence-matrix transpose
  convention before identifying the dominant eigenvalues.
- No o-minimality, Denjoy, Kopell, orbit-circle, or related machinery is part
  of the simplified mathematical route.
