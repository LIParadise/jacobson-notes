#set text(size: 13pt, font: ((name: "Libertinus Serif", covers: "latin-in-cjk"), "Noto Serif CJK JP"))

#show math.sum: math.limits
#show math.product: math.limits
#show math.integral: math.limits
#show link: set text(fill: blue)

#import "@preview/commute:0.3.0": arr, commutative-diagram, node

#let hl(content) = box(
  content,
  inset: 0.1em,
  radius: 0.2em,
  fill: gradient.linear(
    rgb("#F5AAAA"), // Soft coral red
    rgb("#FFD0A6"), // Peach orange
    rgb("#FFF0B3"), // Warm pastel yellow
    angle: 33deg,
  ),
)
#let quo(expr) = {
  set math.frac(style: "skewed")
  expr
}

#let aut = $op("Aut")$
#let endo = $op("End")$
#let ann = $op("Ann")$
#let subgroup = $subset.eq^"group"$
#let subideal = $subset.eq^"ideal"$
#let submodule = $subset.eq^"module"$
#let subring = $subset.eq^"ring"$
#let inj = $arrow.r.hook$
#let surj = $arrow.r.twohead$
#let iso = $arrow.r.tilde$

== Chapter 0 Introduction

- (0.2, p.7) set $S$, map $phi: S -> S$, then $phi$ is a _transformation_ on $S$
- (0.3, p.12) $scr(E)$ equivalence relation, $iota: S -> quo(S / scr(E))$ defined by $a mapsto overline(a)$ is called the *natural map* of $S$ to the quotient set $quo(S / scr(E))$
  - (0.3, p.12) $alpha: S -> S^prime$ then _inverse image_ is $alpha^(-1) (sigma^prime) := {sigma in S | alpha(sigma) = sigma^prime}$ and $alpha^(-1) (T^prime) := {sigma in S | alpha(sigma) in T^prime subset.eq S^prime }$, which may be empty if $sigma^prime in.not im alpha$
    - _fiber over element $sigma^prime in im alpha$_ is $lr((alpha^(-1) (sigma^prime in im alpha))) != nothing$, so the set of the fibers is exactly $quo(S / scr(E)_alpha)$
  - (0.3, p.13) $overline(alpha): quo(S / scr(E)_alpha) -> S^prime$ given by $overline(alpha) (overline(sigma)) = alpha(sigma)$, the map of $quo(S / scr(E)_alpha)$ *induced by* $alpha$, is a well-defined _injective_ map
    - $overline(alpha)$ bijective iff $alpha$ surjective
  - If $alpha$ injection, we say $quo(S / scr(E)_alpha)$ can be identified with $S$ and $overline(alpha)$ can be regarded as the same as $alpha$
  - #commutative-diagram(
      node((0, 0), $S$, "domain"),
      node((0, 1), $S^prime$, "codomain"),
      node((1, 0), $quo(S / scr(E)_alpha)$, "quotient"),

      arr("domain", "quotient", $iota$, "surj"),
      arr("domain", "codomain", $alpha$),
      arr("quotient", "codomain", $exists ! overline(alpha)$, "dashed"),
    ) $alpha = overline(alpha) compose iota$, the *factorization* of the given map $alpha$ as a product of the *natural surjective map* $iota: S -> S^prime$ and the *induced* map $overline(alpha): quo(S / scr(E)_alpha) -> S^prime$: $iota$ _surjective_ and $overline(alpha)$ _injective_, i.e. the diagram commutes
  - Universal property: $overline(alpha)$ is the unique map that makes the diagram commute, for if $beta: quo(S / scr(E)_alpha) -> S^prime$ satisfies $beta compose iota = alpha$, then $beta(overline(sigma)) = beta(iota(sigma)) = alpha(sigma)$ which is exactly how we define $overline(alpha)$
- Universal property: <universal-property> $alpha: S -> S^prime$ is *compatible with* equivalence relation $scr(E)$ on $S$ if $sigma scr(E) tau ==> alpha(sigma) = alpha(tau)$, $iota: S -> quo(S / scr(E))$ given by $sigma mapsto overline(sigma)$ the _natural surjection_, then there *exists unique* _induced_ map $overline(alpha): quo(S / scr(E)) -> S^prime$ s.t. $overline(alpha) compose iota = alpha$
  - the unique induced map $overline(alpha)$ is injective iff $scr(E) = scr(E)_alpha$.

== Chapter 1

- (1.1, p.29) $M(S) := { phi: S -> S }$ i.e. the set of _all monoid of transformations on $S$_
  - (1.1, p.29) a _monoid of transformations on $S$_ is a submonoid of $M(S)$
    - i.e. contains the identity map $id_S$ and is closed under composition
- (1.2, p.31) $M$ monoid, $U(M)$ the _group of units of $M$_ or _invertible elements of $M$_, is subgroup of monoid $M$
  - $op("Sym") S := U(M(S))$ the _symmetric group of the set $S$_
    - $S_n := op("Sym") { 1, 2, ..., n }$
      - in which the elements are _permutations of $S = { 1, 2, ..., n }$_
      - note when $abs(S) = n$, $abs(op("Sym") S) = n! << abs(M(S)) = n^n$
  - $H subset.eq op("Sym") S$, subgroup of the symmetric group of the set $S$, is called _group of transformations on $S$_ or simply _transformation group_
    - If $abs(S) < oo$, $H$ is also dubbed as _permutation group_
- (1.2, p.32) $NN := {0, 1, 2, ...}$
- (1.2, p.33) $D_n$ the _symmetries_ of regular $n$-gon, dihedral group
- (1.2, p.34) $U_n := { z | z^n = 1 } subset.neq CC^times$
- (1.2, p.35) _$n$-fold direct power of $N$_, $N^((n))$, is defined to be $N times N times ... times N$ i.e. the direct product with itself for $n$ times
- (1.3, p.38) Isomorphism for monoids: $eta: M -> M^prime$ bijective and $eta(a b) = eta(a) eta(b)$
  - This is sufficient, since $eta(x) = eta(1) eta(x) = eta(x) eta(1)$, $eta$ surjection so this holds for all $x in M$, meaning $eta(1)$ unit in monoid $M^prime$, which is unique.
  - Isomorphism form equivalence relation: that it requires bijection means inverse is isomorphism, and transitivity is easily obtained too.
- (1.3, p.38) $M$ monoid, $a_L (alpha) = a dot alpha$ is a _left translation_ or _left multiplication_ living in the monoid of transformations of the set $M$ into itself, and $M_L = { a_L | a in M }$.
  - Cayley: a monoid is isomorphic to some monoid of transformations, in particular $M tilde.eq M_L$. The injective part is done by "functional equality": if $a_L = b_L$, then $a = a dot 1_M = a_L (1_M) = b_L (1_M) = b$.
- (1.4, p.40) (proving $a_1 dot a_2 ... a_n$ is well-defined via induction)
- (1.4, p.41) Centralizer $C_M (x) = C(x) = { a x = x a | a in M }$ is a submonoid of $M$, subgroup of $M$ if $M$ turns out to be group
  - $1 x = x 1 = x$
  - $a in C(x) and b in C(x) => a b x = a x b = x a b$ i.e. $a b in C(x)$
  - $a x = x a => a^(-1) x = a^(-1) x a a^(-1) = a^(-1) a x a^(-1) = x a^(-1)$ i.e. $a^(-1) in C(x)$
- (1.4, p.41) monoids and groups are closed under intersection
- (1.4, p.41) Given $A subset.eq M$ we define $C_M (A) = C(A) = limits(inter.big)_(a in A) C_G (a)$, which is submonoid if $M$ monoid and subgroup if $M$ group.
  - $C_M (M)$ is called _center_ of monoid/group.
- (1.4, p.40) (proving ${ a_i } subset.eq C_M ({ a_i })$ then we have things like $(a b)^n = a^n b^n$ for $n in NN$, $ZZ$ if both are invertible)
- (1.8, p.54) definition 1.4 a congruence (or a congruence relation) $equiv$ in $M$ is a equivalence relation that "could be multiplied" i.e. $a equiv alpha and b equiv beta => a b equiv alpha beta$
  - _Quotient monoid of $M$ relative to the congruence $equiv$_: $overline(M) times overline(M) -> overline(M)$ for the relation "could be multiplied"
- (1.8, p.55) theorem 1.6 $G$ group, then congruence relation iff there's some backing normal subgroup
- (1.9, p.59) Homomorphism for monoids $phi: M -> M^prime$ provided $phi(1_M) = 1_(M^prime)$ and $phi(x y) = phi(x) phi(y)$
  - If $M$ were a group, the former is superfluous.
- (1.9, p.59, p.60)
  - _epimorphism_: sujective homomorphism
  - _monomorphism_: injective homomorphism
  - _endomorphism_: homomorphism of $M$ into itself (no injection/surjection assumed)
  - _automorphism_: isomorphism from $M$ to $M$ itself
- (1.9, p.60) theorem 1.7 if two homomorphism agrees on some generators, then they are the same homomorphism
  - In linear algebra, we say that a linear transformation is completely specified when we know where it maps the basis
  - Observe that the points on which $phi$ and $psi$ agree is a submonoid, subgroup if the whole monoid is group
    - $phi(a) = psi(a) and phi(b) = psi(b) ==> phi(a b) = phi(a) phi(b) = psi(a) psi(b) = psi(a b)$ thus monoid
    - $ phi(a) = psi(a) and a^(-1) in M & ==> 1_(G^prime) = phi(a) phi(a^(-1)) = psi(a) phi(a^(-1)) \
                                      & ==> phi(a^(-1)) = psi(a)^(-1) = psi(a^(-1)) $ i.e. if element in the submonoid happened to have inverse, that inverse is agreed upon by the two morphisms too.
- (1.9, p.60) $op("Aut") M$ automorphisms of a monoid $M$ is a group of transformations of the monoid, aka _group of automorphisms of $M$_
  - $op("End") M$ the endomorphisms of a monoid $M$ is a monoid of transformations of the monoid, the _endormorphism monoid of $M$_
- (1.9, p.61) *_Fundamental Theorem of Homomorphisms of Monoids and Groups_*
  - homomorphism gives congruence relations by considering fibers
  - Consider group. $L lt.closed.eq K = ker phi$ (so $phi$ is #link(<universal-property>)[compatible] with congruence defined by $L$), we have _induced homomorphism_ $overline(phi): a L mapsto phi(a)$, given by the _universal property_ satisfying $overline(phi) compose (a mapsto a L) = phi$. $ker overline(phi) = quo((ker phi) / L) = quo(K / L)$ in particular $overline(phi)$ injective iff $K = L$.
  - $ker phi = {e} <==> phi "injective"$ is for group: the monoid of strings has homomorphism to $NN$ by length, which has trivial kernel (the empty string) but certainly not injective
  - $phi$ is equal to first epimorphism to quotient and then (exist unique) momomorphism (*induced map*) to codomain
  - #commutative-diagram(
      node((0, 0), $M$, "domain"),
      node((0, 1), $M^prime$, "codomain"),
      node((1, 0), $quo(M / ker(f))$, "quotient"),

      arr("domain", "quotient", $pi$, "surj"),
      arr("domain", "codomain", $phi$),
      arr("quotient", "codomain", $exists ! overline(phi)$, "dashed"),
    ) #link(<universal-property>)[commutes]
  - Corollary: $phi: G -> G^prime$ group epimorphism, then induced map $overline(phi): quo(G / (ker phi)) -> G^prime$ is both epimorphism and monomorphism, meaning isomorphism, i.e. $im phi tilde.eq quo(G / (ker phi))$
- (1.10, p.65) (Theorem 1.8) $eta: G -> G^prime$ epimorphism, then there's _bijection_ between the family of subgroups in $G$ in which $ker eta$ is contained, ${H subset.eq G | ker eta subset.eq H}$, and the family of _all_ subgroups in $G^prime$, given by $H mapsto eta(H)$.
  - $H lt.closed.eq G <==> eta(H) lt.closed.eq G^prime$
    - Composed homomorphism $((G^prime -> quo(G^prime / eta(H))) compose eta)$ has kernel $ker((y^prime mapsto y^prime eta(H)) compose (x mapsto^eta x^prime)) = H$, meaning (universal property, factors through, induced map, injective since $ker (G -> quo(G / H)) = H$ too, surjective by epimorphism premise) we have isomorphism $quo(G / H) arrow.r.tilde quo(G^prime / eta(H))$ given by $g H mapsto eta(g) eta(H)$.

=== Generic Remarks

- $sigma in S_n$, $(a_1, a_2, dots, a_m)$ single cycle of which members distinct, then $sigma compose ({a_i}) compose sigma^(-1) = (sigma(a_1), sigma(a_2), sigma(a_3), dots, sigma(a_m))$
  - It suffices to show $sigma compose ({a_i}) compose sigma^(-1) compose (sigma(a_1), sigma(a_2), sigma(a_3), dots, sigma(a_m))^(-1) = id in S_n$
  - $sigma(a_1) mapsto^({sigma(a_i)})^(-1) sigma(a_m) mapsto^(sigma^(-1)) a_m mapsto^(({a_i})) a_1 mapsto^sigma sigma(a_1)$
  - $sigma in S_n$, meaning $x in {sigma(a_i)} <==> sigma^(-1)(x) in {a_i}$, thus $x in.not {sigma(a_i)} <==> sigma^(-1)(x) in.not {a_i}$
  - $x mapsto^({sigma(a_i)})^(-1) x mapsto^(sigma^(-1)) sigma^(-1)(x) mapsto^(({a_i})) sigma^(-1)(x) mapsto^sigma x$
- Conjugacy classes are equivalence relation and is exactly the types within symmetric group.
  - $eta in op("Inn")(S_n)$ then $eta(tau) = sigma compose tau compose sigma^(-1)$ never cross any conjugacy class
  - The type of some $sigma in S_n$ is defined to be the lengths of the cycles in its disjoint cycle decomposition when ordered non-decreasing/non-increasing.
  - Suppose $tau^prime = sigma compose tau compose sigma^(-1)$, then by the preceding remark, we can "distribute" $sigma$ entry-wise to all the cycles in $tau$ and get disjoint cycle decomposition of $tau^prime$, meaning $tau$ and $tau^prime$ are of the same type.
  - Suppose $tau^prime$ and $tau$ are of the same type, then entry-wise comparison we get a map mapping $tau$'s entry to $tau^prime$'s entry. Such map is injective since $tau^prime$ is in disjoint cycle decomposition; injective endofunction on finite set so bijection. Name it $sigma$ and we see $tau^prime = sigma compose tau compose sigma^(-1)$.
- $phi in op("Aut")(S_n)$ then $phi$ sends conjugacy classes to conjugacy classes
  - $phi(sigma tau sigma^(-1)) = phi(sigma) phi(tau) (phi(sigma))^(-1)$
  - Not necessarily the same class...?: Maybe type ${(i j)}$ mapped to ${(a b)(c d)}$
    - The type, i.e. disjoint cycle decomposition, contains only transpositions and singletons, for else the order would not be preserved
    - Note ${(1 r) | 1 <= r <= n}$ is generating set for $S_n$
    - $(x y) tilde (i j)$ then $phi((x y)) tilde phi((i j))$, meaning there's some _fixed_ constant $k >= 1$ s.t. $phi((i j)) = product_(l = 1)^k tau_l$ in disjoint transposition decomposition
    - LHS has $binom(n, n-1)$ while RHS has $(product_(l=0)^(k-1) binom(n-2l, 2)) (1/k!) = n! / (2^k k! (n-2k)!)$
    - $2^(k-1) = (n-2)! / (k! (n-2k)!)$, $k=1$ ok, $n > 2k >= 6$ then RHS some multiple of $binom(n-2, k)$ so the prime factorization mismatch
- In general we cannot find $quo(G / H) inj G$
  - $quo(Q_8 / {plus.minus 1}) tilde.eq V_4$ the Klein-$4$ group, but there's no monomorphism $V_4 -> Q_8$ for $V_4$ has $3$ order-$2$ elements while $Q_8$ has only $1$.
  - $ZZ surj quo(ZZ / (2 ZZ))$ but $ZZ$ has no element of order $2$

=== Exercises

- (1.2, ex.7, p.36) Suppose $mu in M$ monoid and $alpha mu = mu beta = 1_M$, show that $alpha = beta$ meaning $mu$ is indeed a unit i.e. invertible.
  - $alpha = alpha (mu beta) = (alpha mu) beta = beta$ by associativity
- (1.2, ex.7, p.36) Given monoid $M$, show that $alpha$ and $beta$ are inverse of each other iff $alpha beta alpha = alpha and alpha beta^2 alpha = 1_M$
  - Direct part being trivial, consider converse
  - $1 = (alpha) beta^2 alpha = (alpha beta alpha) beta^2 alpha = (alpha beta) (alpha beta^2 alpha) = alpha beta$
  - $beta alpha = (1) beta alpha = (alpha beta) beta alpha = 1$
- (1.2, ex.9, p.36) $G subset.eq M$ submonoid of monoid $M$ being non-vacuous, show that $G$ subgroup of monoid $M$ iff for all ${ g, gamma } subset.eq G$, we have $g^(-1) gamma in G$
  - Direct part being trivial, consider converse
  - Identity: being non-empty, pick any $gamma = g in G$
  - Inverse: pick any $g$ and $1_M$ then $g^(-1) 1_M in G$ by premise
  - Closed: for any $g^prime$ and $gamma$, pick $g = g'^(-1)$ and $gamma$
- (1.3, ex.3, p.39) $G$ group, show that $g |-> g_L^(-1)$ (note it's an mapping into some group of transformations) is isomorphism
  - note $g_L^(-1)$ is simply $(g^(-1))_L$: $(x |-> x g g^(-1)) = (x |-> x g^(-1) g) = id$
  - $a b |-> (x |-> x (a b)^(-1)) = (x |-> x b^(-1) a^(-1)) = (x |-> x a^(-1)) compose (x |-> x b^(-1))$
- (1.3, ex.4, p.39) Is $(QQ, +)$ isomorphic (as a group) to $(ZZ, +)$?
  - Nope: $ZZ$ is cyclic group with $chevron.l -1 chevron.r$ or $chevron.l 1 chevron.r$, but $QQ$ generated by one element are of certain denominators only, meaning we need more generators.
  - In fact $QQ$ is not finitely generated, since given a set we may figure out some common denominator s.t. all numerators are integers and their greatest common divisor is $1$.
- (1.3, ex.5, p.39) Is $(QQ, +)$ isomorphic (as a group) to $(QQ, times)$?
  - Nope: consider $phi: (QQ, +) -> (QQ, times)$, suppose $phi(1) = q != 0$, by isomorphism we know $phi(a) = b <=> q^a = b$, but for all $q != 0$ there's some $m in ZZ_(>0)$ s.t. $q^(-m) in RR without QQ$.
- (1.4, ex.3, p.42) Show that if $g^2 = 1_G$ for all $g in G$, then $G$ abelian. Consider also $g^3 = 1_G$ for all $g in G$.
  - $g^2 = 1$, $(a b)(a b) = 1$, $a b a = a b a b b = 1 b = b$, $a b = a b a a = b a$.
  - $ mat(
      1, x, y;
      0, 1, z;
      0, 0, 1;
      delim: "[",
    ) in quo(ZZ / 3 ZZ)_(3 times 3) $, the Heisenberg group
    - Note it's minimal example: by Cauchy and the fact we have no other prime orders other than $3$, the group is of size $3^n$, and $3$ is cyclic while $3^2$ is abelian.
      - That $p^2$ is abelian: consider acting on itself by conjugation: fixed points are $C_G(G) = Z_G$ and apply orbit-stabilizer theorem
- (1.9, ex.4, p.63) Consider automorphism group of cyclic groups
  - Recall that homomorphisms are described by the generators, and cyclic groups have only $1$
  - $op("Aut") ZZ tilde.eq C_2$
  - $op("Aut") C_m tilde.eq (ZZ / m ZZ)^times$ of which cardinality is Euler totient $phi(m)$
- (1.9, ex.9, p.64) fixed-point-free automorphisms...?

== Chapter 2

- (2.1, p.87) the additive group of $R$ means the $(R, +, 0)$ part of ring $R$, while the multiplicative monoid denotes the $(R, times, 1)$ part.
- (2.1, p.87) subring $S$ if $(S, +, 0)$ is subgroup of the additive group of $R$ and $(S, times, 1)$ is submonoid of the multiplicative monoid of $R$
- (2.1, p.87) rings are closed under intersection, thus _subring generated by_ set is the intersection of all subrings to which the set belongs
- (2.2, p.90) domain: $(R^* := R without {0}, times, 1)$ is submonoid of the multiplicative monoid of $R$
  - closed!
  - In particular $R != 0$ i.e. $1_R != 0_R$ and $a != 0 and b != 0 => a b != 0$
  - Iff no nonzero zero divisors
  - Iff both $R != 0$ _and_ *restrict cancellation* works on both side
    - $a != 0$ then $(b a = c a => b = c) and (a b = a c => a = c)$
- (2.2, p.91) _skew field_, _sfield_, _division ring_ if $(R^*, times, 1)$ is subgroup of the multiplicative monoid
  - Iff $1 != 0 and (forall a != 0 exists b quad a b = b a = 1)$
  - _field_ if the multiplicative monoid being commutative
  - _division subring_ if the subring is a division ring
- (2.3, p.92) determinants require commutative rings
- (2.3, p.94) _matrix units_ ${e_(i j)}$ e.g. $e_(2 3) = mat(0, 0, 0; 0, 0, 1; 0, 0, 0)$
  - Do not commute: $e_(i j) e_(k l) = delta_(j k) e_(i l)$: Kronecker delta
  - ${e_(i i)}$ are idempotent
  - They are _not_ units in $M_n (R)$: consider $I = mat(1, 0, 0; 0, 1, 0; 0, 0, 1)$
  - They span $M_n (R)$: $A = mat(a_(1 1), a_(1 2), dots, a_(1 n); a_(2 1), a_(2 2), dots, a_(2 n); dots; a_(n 1), , dots, a_(n 1)) = sum_(i j) a_(i j) e_(i j)$
- (2.3, p.95) Identify $a in R$ in $M_n (R)$ by $op("diag") { a, a, dots, a }$
  - $a I = I a = op("diag"){a, a, dots, a} subset.eq C_(M_n (R))({e_(i j)})$ as subring (exercise 6)
  - $R -> {op("diag"){a, a, dots, a} | a in R} subset.eq M_n (R)$ isomorphism of rings: _embedding_ of $R$ in $M_n (R)$
- (2.3, p.95) For *commutative ring* we have _determinant_: \ $det A = sum_sigma (op("sgn") sigma) a_(1 sigma(1)) a_(2 sigma(2)) a_(2 sigma(2)) dots a_(n sigma(n)) \ = sum_(k=1)^n a_(r k) A_(r k) \ = sum_(k=1)^n a_(k c) A_(k c)$: _cofactor expansion_
  - $A_(r c)$ is _cofactor at row $r$ column $c$_ given by $(-1)^(r + c) det (A "sans column" c "and row" r)$
  - Cofactor expansion using different rows/columns vanishes: $sum_k a_(x k) A_(x^prime k) = sum_k a_(k x) A_(k x^prime) = 0$ if $x eq.not x^prime$
  - Writing $(op("adj") A) times A = A times (op("adj") A) = det A$ (recognize $R$ in $M_n (R)$ so $op("diag"){a, a, dots, a}$), define _adjoint_ $op("adj") A := (alpha_(i j))^T$ s.t. $(op("adj") A)_(r c) = alpha_(c r) = (-1)^(c+r) det (A "sans column" r "and row" c)$: here we use $alpha_(i j)$ for cofactor at row $i$ col $j$
    - Note the transpose required for cofactor expansion is along rows/columns
  - $det (A B) = det A dot det B$ and $det I = 1$ implies $det: M_n (R) -> R$ homomorphism, whereby the codomain is the multiplicative monoid of ring $R$
    - $det (op("GL")_n (R)) = U(R)$
  - $det A in U(R) <==> A^(-1) in M_n (R)$
    - $<==$: $det A^(-1) dot det A = det A dot det A^(-1) = det I = 1$
    - $==>$: $(det A)^(-1) op("adj") A$ suffices as inverse and is well-defined
- (2.3, p.95) isomorphism of rings is defined to be map that's both isomorphism for the abelian group $+$ and the monoid $times$
- (2.3, p.96) adjoint: $op("adj") A$ is s.t. its $r$ row $c$ col is the cofactor $A_(c,r) = (-1)^(c+r) det(A "sans row" c "sans col" r)$
  - note the swap of indices
- (2.4, p.98) _quarternions_: $i^2 = j^2 = k^2 = -1 = i j k$
  - $i j = -j i = k and j k = -k j = i and k i = -i k = j$
  - Embedded in $M_2 (CC)$, ${mat(a, b; -overline(b), overline(a)) | {a, b} subset CC}$
    - Division ring but not field, not commutative!
    - Specifically $i = mat(sqrt(-1), 0; 0, -sqrt(-1)) and j = mat(0, 1; -1, 0) and k = mat(0, sqrt(-1); sqrt(-1), 0)$
- (2.5, p.101) congruence for rings are s.t. it's congruence for both the abelian $+$ and the monoid $times$ i.e. $a equiv alpha and b equiv beta => a + b equiv alpha + beta and a b equiv alpha beta$
  - (congruence for both the additive abelian group and multiplicative monoid) iff (subgroup in additive abelian group and multiplication is absorbing), motivating the definition of _ideal_: subgroup to the additive group that is absorbing in both sides when multiplied
  - ideals are closed under intersection, thus define ideal _generated by_ some set $S$, denoted as $(S)$. We have $ (S) = sum_(sigma in S) (sum_({ alpha, beta } subset.eq R) alpha sigma beta) $ (all summations are assumed to be of finite length)
    - _principal_ ideal if $I = (sigma in S)$ i.e. generated by one
    - If $R$ is commutative, $ (S) = (sigma_1, sigma_2, ..., sigma_n) = sum_(1 <= i <= n and r_i in R) r_i sigma_i = sum_(1 <= i <= n and r_i in R) sigma_i r_i $
      - In particular _principal_ $(a)$ becomes simply ${a gamma = gamma a | gamma in R}$
- (2.5, p.101) quotient rings i.e. difference rings with respect to the ideal $I$
- (2.5, p.102) $R$ commutative ring, then field iff ideals are trivial, ${0}$ and $R$
  - $==>$: division ring, any nonzero element has inverse, $1 in I$, $1 x = x 1 = x$ absorbing so $I = R$
  - $<==$: $R = (0 eq.not a in I) subset.eq I$, meaning $a alpha = 1$ by principal ideal in commutative ring, so $alpha$ is inverse of $a$
- (2.5, p.102) $K=I+J$ the ideal _generated by_ ${i+j | i in I, j in J}$ i.e. $({i+j | i in I, j in J})$
  - simply ${i+j | i in I, j in J}$ for being closed in the additive abelian group and closed (due to distro) in the multiplicative monoid
- (2.5, p.102) $K=I J$ the ideal _generated by_ ${i j | i in I, j in J}$ i.e. $({i j | i in I, j in J})$
  - $I J subset.eq I inter J$ but the converse does not hold in general
  - $(7)^2 = (49) subset.neq (7)$
- (2.6, p.102) Theorem 2.2: <ch-2.6-thm-2.2> $R$ commutative, then $R$ is field iff its only ideals are $(0)$ and $R$
- (2.6, p.103) Ring $R$, left ideal: $L subgroup (R, +, 0)$ that are absorbing multiplicatively i.e. $forall r in R #h(1em) r L subset.eq L$. Similarly right ideal.
- (2.7, p.106) *homomorphism for rings* is $phi: R -> R^prime$ s.t. it's both a homomorphism for the additive group and the multiplicative monoid
  - kernel for ring homomorphism: $ker phi := phi^(-1) (0_(R^prime))$ is defined to be the kernel of $phi$ as homomorphism on the additive group. Preimage, congruence for both the additive abelian group and the multiplicative monoid, ideal.
  - $eta: R -> R^prime$, $I subset.eq ker eta$ ideal, $pi: R -> quo(R / I)$ natural epimorphism, then $eta$ factors through $quo(R / I)$ uniquely (#link(<universal-property>)[universal property]) with $overline(eta): overline(a) = a + I mapsto eta(a)$ s.t. $eta = overline(eta) compose pi$
  - $overline(eta)$ injective (thus monomorphism) iff $I = ker eta$
  - #commutative-diagram(
      node((0, 0), $R$, "domain"),
      node((0, 1), $R^prime$, "codomain"),
      node((1, 0), $quo(R / I)$, "quotient"),

      arr("domain", "quotient", $pi$, "surj"),
      arr("domain", "codomain", $eta$),
      arr("quotient", "codomain", $exists ! overline(eta)$, "dashed"),
    ) #link(<universal-property>)[commutes]
  - (Theorem 2.6) *TODO* (rings/ideals in $quo(R / ker(phi))$ has bijection and associated isomorphism to some subrings/ideals of $R$ containing $ker(phi)$)
- (2.7, p.109) _prime ring of $R$_ (modern notation *prime subring of $R$*): the smallest subring containing $1_R$ i.e. the subring generated by $1_R$
  - $phi: ZZ -> R$ given by $n mapsto n 1_R := sum_(i=1)^n 1_R$; image being subring, contained in any other subring that contains $1_R$, thus the smallest: prime subring in $R$
  - $im phi tilde.eq ZZ 1_R$ meaning $ker phi$ ideal in $ZZ$, meaning $ker phi = {0} or (k)$, the latter dubbed as _ring of residues modulo $k$_
  - Ring $R$ has prime subring being isomorphic to either $ZZ tilde.eq quo(ZZ / (0))$ or $quo(ZZ / (k))$. Define *characteristic*, $op("char") R$, to be $0$ for the former and $k$ for the latter.
    - $op("char") R = k > 0$ then $k a := sum_(i=1)^k a =^"distro" (sum_(i=1)^k 1_R) a = 0_R a = 0$ \ i.e. $forall gamma in R, thick k gamma = 0$
    - $R$ domain, then its prime subring is either $ZZ$ or $quo(ZZ / (p))$ whereby $p$ prime
- (2.8, p.112) $phi: R -> R^prime$ is _anti-isomorphism_ if it's isomorphism on the additive abelian group satisfying $phi(a b) = phi(b) phi(a) and phi(1_R) = 1_(R^prime)$, in which case $R$ and $R^prime$ are _anti-isomorphic_
  - For any $R$ ring we can construct $R^circle.small$, dubbed _$R$ opposite_, s.t. they are anti-isomorphic
  - _anti-automorphism_ if $phi: R -> R$, _involution_ if $phi compose phi = id$
    - transpose on the matrix ring of commutative ring $R$, $(a_(i j) mapsto a_(j i))$, is involution
    - adjoint on the matrix ring of commutative ring $R$ is involution
    - both $(psi in op("Aut") R) compose phi$ and $phi compose (psi in op("Aut") R)$ are anti-automoprhism if $phi$ is anti-automorphism
- (2.10, p.120) Towards the end of chapter 2, except 2.17 and explicitly mentioned otherwise, by default rings are commutative
- (2.10, p.120) Given (commutative) $R$ subring to $R^prime$ ($R^prime$ _overring_ to $R$ (p.123)), *adjoining* $U subset.eq R^prime$ some subset of $R^prime$ to $R$ is denoting the subring *generated* by subring $R$ and subset $U$, denoted as $R[U]$.
  - $R[U][V] = R[U union V]$
  - WLOG consider $R[{u}]$ abbreviated/abused as $R[u]$, which contained in (thus equal) ${sum_(i=0)^n r_i u^i | n < infinity and r_i in R}$: note the finiteness.
    - See also #link(<ch2.7-ex.8>)[2.7 exercise 8 (p.110)].
  - It might well be that ${a_i | 0 <= i <= k} != {b_i | 0 <= j <= l}$ with $sum_(i=0)^k a_i u^i = sum_(j=0)^l b_j u^j$: alternative names for the same element
    - $R = RR subset.eq R^prime = CC$ and $u = sqrt(-1)$: $1 = u^2$
    - $u in R$ then $(a_0 = u) = (a_0 = 0 and a_1 = 1)$
- (2.10, p.121) We'd like a ring whereby comparing "coefficients" asserts equality. Consider the set of maps $NN -> R$ with *finite* support i.e. those maps to $0_R$ for all but finitely many elements.
  - ${(r_0, r_1, r_2, dots) | "all but finitely many" r_i != 0}$
    - Addition: pointwise
    - Multiplication: ${a_i} times {b_j} = {c_k}$ where $c_k = sum_(i+j=k) a_i b_j$
      - nowdays aka convolution
    - $(1, 0, 0, dots)$ is the multiplicative identity
    - $(0, 0, 0, dots)$ is the additive identity
    - Monomorphism $R$ into our new ring: identify $R$ with ${(r, 0, 0, dots) | r in R}$
    - $x := (0, 1, 0, dots)$
    - By adjoining $x$ to our (embedded) $R$, we see $R[x]$ generates the whole ring: _ring of polynomials over $R$ in the indeterminate $x$_
    - $sum a_i x^i = sum b_i x^i <==> forall i #h(1em) a_i = b_i$
- (2.10, p.121) Fundamental homomorphism property of polynomial rings: let $S$ and $R$ be commutative rings, $sigma in S$, $eta: R -> S$ ring homomorphism, then there exists unique ring homomorphism $tilde(eta): R[x] -> S$ serving as extension of $eta$ ($tilde(eta) compose nu = eta$ where $nu: R -> R[x]$ the natural monomorphism)
  - Existence: so-called _substituting $u$ for $x$ in $f(x) in R[x]$_
  - Uniqueness: see #link(<ch2.7-ex.8>)[exercise 8, chapter 2.7, p.110]
  - #commutative-diagram(
      node((0, 0), $R$, "domain"),
      node((0, 1), $S$, "codomain"),
      node((1, 0), $R[x]$, "polynomial ring"),

      arr("domain", "polynomial ring", $nu$, "inj"),
      arr("domain", "codomain", $eta$),
      arr("polynomial ring", "codomain", $exists ! tilde(eta)$, "dashed"),
    )
- (2.10, p.121) theorem 2.10: <ch-2.10-thm-2.10> $R subset.eq S$ commutative rings, $sigma in S$, identity homomorphism $nu: R -> S$, then exists unique homomorphism $tilde(nu): R[x] -> S$ that's both extention of $nu$ and s.t. $x$ got mapped to $u$. Meaning $ quo(R[x] / ker(tilde(nu))) tilde.eq im(tilde(nu)) = R[u] and ker(tilde(nu)) inter R = {0} $
- (2.10, p.122) Conversely if $I subset.eq^"ideal" R[x] and R inter I = {0}$, via the natural homomorphism $eta: R[x] -> quo(R[x] / I)$, $eta$ restricted on $R$ is monomorphism so we may identify $R$ with $eta(R) subset.eq^"subring" quo(R[x] / I)$. Letting $u = x + I in quo(R[x] / I)$, since $R[x]$ is generated by $R$ and ${x}$, $eta(R[x]) = quo(R[x] / I)$ is generated by $eta(R)$ and $eta(u)$. I.e. $quo(R[x] / I) iso R[u]$
  - where again RHS is via the identification of $R$ in $quo(R[x] / I)$ via $eta(R)$.
- (2.10, p.124) theorem 2.11: <ch-2.10-thm-2.11> _*the* ring of polynomials over $R$ in $r$ indeterminates $x_1, dots, x_r$_, i.e. $R[x_1, dots, x_r]$, satisfies the following #link(<universal-property>)[_universal property_]: #hl("Note") we have a (natural) monomorphism $R -> R[x_1, dots, x_r]$. For _any_ $S$ ring, _any_ $eta: R -> S$ homomorphism, and _any_ $nu: {1,dots, r} -> {u_1, dots, u_r} subset.eq S$, there _exists unique_ extension of $eta$ to $tilde(eta): R[x_1, dots, x_r] -> S$ with $ forall 1 <= i <= r #h(1em) tilde(eta)(x_i) = nu(i) = u_i $
  - #hl("so we need to fix some monomorphism first?") I.e. it's the tuples $(A, iota_alpha: R -> A)$ and $(R[x_1, dots, x_r], iota_gamma: R -> R[x_1, dots, x_r])$ that we talk about if they satiesfy the universal property
  - Proof: Jacobson defines $R[x_1, dots, x_r]$ inductively, thus it suffices to inductively apply #link(<ch-2.10-thm-2.10>)[theorem 2.10].
  - _If_ we have ring $R subset.neq^"subring" A$ with the same exact #link(<ch-2.10-thm-2.11>)[universal property], #hl("WLOG") assume that $A$ is generated (as a ring) by $ R union.sq ({a_1, dots, a_r} subset.eq (A without R)) $ i.e. $ A = R[{a_1, dots, a_r} subset.eq A without R] $ then $A tilde.eq R[x_1, dots, x_r]$.
    - Proof: we _need_ the *uniqueness* of the universal property
    - Two natural monomorphism, $iota_alpha: R -> A$ and $iota_gamma: R -> R[x_1, dots, x_r]$
    - By universal property of $A$, there _exists_ *unique* $phi: A -> R[x_1, dots, x_r]$ that both s.t. $a_i mapsto x_i$ _and_ serves as extension of $iota_gamma$: #commutative-diagram(
        node((0, 0), $R$, "domain"),
        node((0, 1), $R[x_1, dots, x_r]$, "codomain"),
        node((1, 0), $A$, "generated"),

        arr("domain", "generated", $iota_alpha$, "inj"),
        arr("domain", "codomain", $iota_gamma$),
        arr("generated", "codomain", $exists ! phi$, "dashed"),
      )
    - By universal property of $R[x_1, dots, x_r]$, there _exists_ *unique* $psi: R[x_1, dots, x_r] -> A$ that both s.t. $x_i mapsto a_i$ _and_ serves as extension of $iota_alpha$: #commutative-diagram(
        node((0, 0), $R$, "domain"),
        node((0, 1), $A$, "codomain"),
        node((1, 0), $R[x_1, dots, x_r]$, "generated"),

        arr("domain", "generated", $iota_gamma$, "inj"),
        arr("domain", "codomain", $iota_alpha$),
        arr("generated", "codomain", $exists ! psi$, "dashed"),
      )
    - Identity map on $R[x_1, dots, x_r]$ is *the* unique homomorphism that maps $R[x_1, dots, x_r]$ back to itself since $R[x_1, dots, x_r]$ satiesfy the universal property.
    - Meaning $phi compose psi = id$. The unique $phi$ is isomorphism: $A arrow.tilde^phi R[x_1, dots, x_r]$.
  - In my own words...
    - Suppose we have...
      - $iota: R inj A$ monomorphism
      - ${a_1, dots, a_r} subset.eq A$ some _distinguished distinct_ elements $a_i in.not im(iota)$.
      - $A = im(iota)[a_1, dots, a_r]$ i.e. generated by the image and the distinguished elements
    - _If_ additionally $A$ satiesfies the universal property, that for any $eta: R -> S$ homomorphism, for any $nu: {1, dots, r} -> {sigma_1, dots, sigma_r} subset.eq S$, there _exists unique_ $tilde(eta): A -> S$ that's both...
      - an extension of $eta$, i.e. $tilde(eta) compose iota = eta$
      - $tilde(eta)(a_i) = nu(i) = sigma_i$
    - Then $A tilde.eq R[x_1, dots, x_r]$: the unique homomorphism s.t. $x_i mapsto^phi a_i$ and $a_i mapsto^psi x_i$, when composed, has to be _the_ identity mapping on resp. rings, that is, $psi compose phi = id_(R[x_j])$ and $phi compose psi = id_A$: note we can also think of resp. identity isomorphism as some unique extension by universal property, too.
      - $iota: R inj A$ must thus be injective
- (2.10, p.123, p.124) Corollary: $R[u] tilde.eq quo(R[x] / I)$
- (2.10, p.123, p.124) Refer to the homomorphism via #link(<ch-2.10-thm-2.10>)[universal property] $R[x] -> R[u]$ _substituting $u$ for $x$_. Then $u in S$ is...
  - _transcendental_ if $R[x] -> R[u]$ injective
  - _algebraic_ if otherwise
  - Classical case: $QQ[u] subring RR subring CC$.
- (2.10, p.124) $R subset.eq S$ and ${u_1, dots, u_r} subset.eq S$, then ${u_i}$ is _algebraically independent over $R$_ if the only finite sum of products $sum_(i in I and abs(I) < infinity) (a_i product_(j=1)^r u_j^(e_(i j)) ) = 0_S$ is for all the coefficients to be $0_S$.
  - Another characterization for $R[x_1, dots, x_r]$ as an extension of $R$!
    - (me) check: it satisfies the #link(<ch-2.10-thm-2.11>)[polynomial ring universal property] since the independence ensure the straightforward extension being well-defined
- (2.11, p.128, p.129) theorem 2.13: if $D$ is commutative integral domain, then $D[x_1, x_2, dots, x_k]$ is commutative integral domain too, of which units are those in $D$
  - $deg(f(x) g(x)) = deg(f(x)) + deg(g(x))$ works even for $deg(0) = -infinity$ for there's no nonzero zero-divisor
  - $
          & f(x) g(x) = 0 \
      ==> & deg(f(x) g(x)) = deg(0) = -infinity \
      ==> & deg(f(x)) = -infinity or deg(g(x)) = -infinity \
      ==> & f(x) = 0 or g(x) = 0
    $
  - $
          & f(x) g(x) = 1 \
      ==> & deg(f(x) g(x)) = deg(1) = 0 \
      ==> & deg(f(x)) = 0 and deg(g(x)) = 0 \
      ==> & f(x) in D and g(x) in D \
      ==> & f(x) in D^times and g(x) in D^times
    $
  - $
      f & = q_1 g + r_1 = q_2 g + r_2 \
        & and deg(r_1) < deg(g) \
        & and deg(r_2) < deg(g) \
        & ==> q_1 = q_2 and r_1 = r_2
    $
    - $g(q_1 - q_2) = r_2 - r_1$
    - RHS has $deg$ strictly less than $deg(g)$ since $deg(f+g) <= max(deg(f), deg(g))$
    - Suppose $q_1 != q_2$, then LHS has degree no less than $deg(g)$ by $D$ domain, $bot$
    - So $q_1 = q_2$, and $r_1 = r_2$ follows from the abelian additive group of the ring $D$
- (2.12) polynomial functions
  - $F^S := {scr(f) mid(|) scr(f): S -> F}$ is a ring
    - Both multiplication and addition pointwise
    - Embedding $F -> F^S$ via $f mapsto (alpha mapsto f)$ is ring homomorphism
    - $F^F = F -> F$ is _polynomial functions in one variable over $F$_
  - Consider $phi: F[x] -> F^F$ by #link(<ch-2.10-thm-2.10>)[universal property]
    - $x mapsto id$ and $f in F mapsto (alpha mapsto f)$
    - $x^2 mapsto (alpha mapsto alpha) times (alpha mapsto alpha) = (alpha mapsto alpha^2)$: pointwise!
    - $phi(A(x) = sum_(i=0)^k a_i x^i) = (xi mapsto sum_(i=0)^k a_i xi^i)$
    - Suppose $abs(F) = infinity$ and $phi(A) = (alpha mapsto 0)$. But any $A(x) in F[x]$ has at most $deg A$ roots (or has at most this many homomorphism s.t. $A(x) mapsto (0 in F[u])$). So $A(x) = 0_(F[x])$. I.e. $phi$ is injective.
    - Suppose $abs(F) = q < infinity$. Consider $A(x) = product_(f in F^times) (x - f)$. $F$ field so integral domain so $F[x]$ domain so $A(x) eq.not 0_(F[x])$. But clearly $phi(A)$ is the zero function $(xi mapsto 0_F)$ in $F -> F$.
  - Consider $psi: F[x_1, dots, x_r] -> F^(F^r)$ i.e. $psi: F[x_1, dots, x_r] -> F^r -> F$ given by the #link(<ch-2.10-thm-2.11>)[universal property] defined by $ x_i mapsto mat(xi_1; dots.v; xi_r) mapsto xi_i $
    - For instance $ (x^2 + 2 y^2 + x y + 3) mapsto (alpha, beta) mapsto (alpha^2 + 2 beta^2 + alpha beta + 3) $
    - Theorem 2.19: <ch-2.12-thm-2.19> $abs(F) = infinity$ and $0 eq.not A(x_1, dots, x_r) in F[x_1, dots, x_r]$ then $ psi(A) eq.not (mat(xi_1; dots.v; xi_r) mapsto 0) $
      - Proof: induction
      - Base case had been solved
      - Consider $A in F[x_1, dots, x_(r-1)][x_r]$ and write $A = sum_(i=0)^r B_i x_r^i$ where $B_i in F[x_1, dots, x_(r-1)]$
      - By induction hypothesis there's some specific constant $mat(kappa_1; dots.v; kappa_(r-1)) in R^(r-1)$ enabling us to "substitute" to have $tilde(A) in F[x_r]$ where $deg tilde(A) = r$
      - Observe that the single indeterminate base gives us $phi(tilde(A))$, which is exactly the function $zeta mapsto psi(A)(mat(kappa_1; dots.v; kappa_(r-1); zeta))$, in particular it's not the zero function, thereby establishing the claim.
    - $abs(F) = q$ then _the ring of polynomial functions in $r$ variables_ is isomorphic to $ quo(F[x_1, dots, x_r] / ((x_1^q - x_1, dots, x_r^q - x_r))) $
      - Lemma: $deg(A in F[x]) < q$ then $phi(A) eq.not 0_(F -> F)$: at most $deg(A)$ roots
      - Inductively, if none of the indeterminates in $A in F[x_1, dots, x_r]$ has power greater than or equal to $q$, then $psi(A) eq.not 0_(F^r -> F)$
      - Observe that by Lagrange, $ psi(x_i^q - x_i) = mat(xi_1; dots.v; xi_r) mapsto xi_i^q - xi_q = bold(xi) mapsto 0_F $
      - $ x_i^q - x_i in ker(psi) subideal F[x_1, dots, x_r] $
      - For any $k >= q$, via long division, $x_i^k = (x_i^q - x_i) q_k (x_i) + r_k (x_i)$, we can rewrite any $A in F[x_1, dots, x_r]$ as $ A = (sum_(i=1)^r (x_i^q-x_i)B_i (x_1, dots, x_r)) + B_0(x_1, dots, x_r) $ where $B_0$ has no $x_i$ with power greater than or equal to $q$
      - We have $psi(A) = 0_(F^r -> F) <==> psi(B_0) = 0_(F^r -> F)$
      - $ker(psi)$ is therefore identified to be the ideal $(x_1^q - x_1, dots, x_r^q - x_r)$.
- (2.14, p.141) Assuming cancellative commutative monoid $M$
  - _associates_: $a divides b and b divides a$, equivalently $a = mu b$ where $mu in M^times$ i.e. $mu$ unit
    - $M^times subgroup M$ so being associates is equivalence relation
  - $f divides a and a divides.not f$ then $f$ is _proper factor_ of $a$
  - _irreducible_: <irreducible> $u$ s.t. there's no proper factor, i.e. factor iff associate
    - In general there's no _unique up to associates and permutation_ factorization
      - $ZZ[sqrt(-5)] in.rev 6 = 2 times 3 = (1+sqrt(-5)) times (1-sqrt(-5))$
      - $ZZ[sqrt(-5)] in.rev 9 = 3 times 3 = (2+sqrt(-5)) times (2-sqrt(-5))$
      - Generic Euclidean norm is multiplicative: the only units are ${plus.minus 1}$ and these are some irreducibles that are not associates
  - _Unique factorization monoid_, _Gaussian_, or _factorial_: cancellative commutative monoid where exists unique up to associates factorization
    - (repetition allowed) $a = product_(i=1)^alpha p_i$, $b = product_(i=1)^beta p^prime_i$, $c = product_(i=1)^gamma p^prime.double_i$, and $a = b c$, then by uniqueness there's injection $p^prime_j mapsto p_(i_j)$ i.e. any factor of $a$ is of the form $product_(j=1)^(k <= alpha) p_(i_j)$
- (2.14, p.142) <ch-2.14-ufd-then-irreducibility-implies-primeness> $R$ UFD then irreducible implies primeness
  - $r$ irreducible and $r | a b$. WLOG assume neither $a$ nor $b$ is unit.
  - Consider unique factorization into irreducibles, $a = product_(i = 1)^(k < infinity) gamma_i and b = product_(j = 1)^(l < infinity) gamma^prime_j$ (repetition allowed)
  - By uniqueness, factors of $a b$ must be some subset (multiset) within ${gamma_i} union {gamma^prime_j}$.
  - $r$ is irreducible, so $r | a or r | b$
- (2.14, p.142) _divisor chain condition_: there's no infinite sequence ${a_i}$ s.t. $a_(i+1)$ is proper factor of $a_i$
- (2.14, p.142) _primeness condition_: irreducibility implies primeness
- (2.14, p.143) UFD iff commutative cancellative monoid with divisor chain condition and primeness condition
  - Irreducibility is #link(<irreducible>)[by definition] suitable base case for mathematical induction
  - By induction (twice) we know irreducible decomposition exists
  - Base case for uniqueness: <primeness-imply-uniqueness-of-irreducible-factorization> suppose $a$ can be written as two products of irreducibles...
    - $a = p = product_(i=1)^k p_i$. By irreducibility of $p$, $k = 1$.
  - Inductive case: irreducible implies prime, $ p a divides c d ==> c d = p a b ==> p divides c d $ WLOG for $ a = product_(i=1)^s p_i = product_(i=1)^t p^prime_i $ we have $p_1 tilde p_1^prime$ associates and apply inductive hypothesis
- (2.14, p.143) UFD iff commutative cancellative monoid with divisor chain condition and GCD condition
  - $
      gcd(a, b) := {u mid(|) u divides a and u divides b and forall mu #h(1em) mu divides a and mu divides b ==> mu divides u }
    $
    - _relatively prime_: if $gcd$ is some unit
      - In UFD, iff either is unit, or there's no shared irreducible factor
      - For irreducible $r$, either $(a, r) ~ 1$ or $(a, r) ~ r$.
  - $
      lcm(a, b) := {m mid(|) a divides m and b divides m and forall mu #h(1em) a divides mu and b divides mu ==> m divides mu }
    $
  - GCD condition: any finite subset of elements has $gcd$ defined
  - UFD implies both $gcd$ and $lcm$: observe that by gathering associated terms we can rely on the exponents
  - Commutative cancellative monoid and GCD condition implies that irreducibility leads to primeness
    - $c(a, b) ~ (c a, c b)$
      - Let $(a, b) = delta$ and $(c a, c b) = delta^prime$
      - Let $a = delta alpha$ and $c a = delta^prime alpha^prime$
      - $c delta divides c a and c delta divides c b ==> c delta divides delta^prime$
      - $delta^prime = c delta mu$
      - $c a = delta^prime alpha^prime = c delta mu alpha^prime$
      - $a = delta mu alpha^prime$ by cancellative domain
      - $delta mu divides a$, in the same vein $delta mu divides b$, gcd so $delta mu divides delta$
      - $delta mu x = delta$, cancellation so $mu$ unit
    - $(a, b) ~ 1 and (a, c) ~ 1 ==> (a, b c) ~ 1$
      - $1 ~ (a, c) ~ (a, (a c, b c)) ~ ((a, a c), b c) ~ (a, b c)$
    - Contrapositive: suppose irreducible $p$, $p divides.not a and p divides.not b$, #link(<irreducibility-in-poset>)[then] $(p, a) ~ 1 and (p, b) ~ 1$ and so $(p, a b) ~ 1$ meaning $p divides.not a b$
- (2.16, p.152) $D$ UFD, $A(x) in D[x]$ is _primitive_ if there's no $D in.rev d divides A(x)$
  - $A(x) = sum_(i=1)^k a_i x^i$ then consider $sum_(i=1)^k a_i / gcd(a_1, dots, a_k) x^i$
  - $F$ field of fractions of domain $D$ and $A^prime (x) in F[x]$, _exists unique_ <equivalence-via-primitivity-shared-across-field-of-fractions> primitive $A in D[x]$ (up to _units in $D$_) with $A^prime = gamma A$ where $gamma in F$
    - (IMHO) sharing primitives via _scalar scaling_ in $D$ and $F$ (_up to units in $D$_) is an equivalence relation not only on $D[x]$ but also extends over $F[x]$ and we can always find 'em via some scaling and $gcd$
- (2.16, p.152) (Gauss lemma) <Gauss-lemma> $D$ UFD, $A(x)$ and $B(x)$ both primitive in $D[x]$, then $A(x) B(x)$ is also primitive
  - Contrapositive: suppose some $d in D$ that are not unit s.t. $d divides A(x) B(x)$
  - WLOG suppose $d$ irreducible, UFD thus prime, meaning $quo(D/((d)))$ domain thus $quo(D/((d)))[x]$ domain
  - Observe that $tilde(A) tilde(B) = 0_(quo(D/((d)))[x])$ violating domain
- (2.16, p.153) $D$ UFD, then irreducibility in $D[x]$ implies irreducibility in $F[x]$ <field-of-fractions-preserve-irreducibility> where $F$ field of fractions of $D$
  - Contrapositive: suppose $A in D[x]$ is irreducible but reducible in $F[x]$ via $A = B C$, note $deg B > 0 and deg C > 0$
  - There exists some ${mu, nu} subset.eq F$ with $B = mu B^prime$, $C = nu C^prime$, and #link(<equivalence-via-primitivity-shared-across-field-of-fractions>)[both $B^prime$ and $C^prime$ in $D[x]$ primitive] s.t. $A = mu nu B^prime C^prime$
  - $B^prime C^prime$ primitive by #link(<Gauss-lemma>)[Gauss], and $A$ itself is already primitive thx to irreducibility
  - Thus we get two different ways to show primitivity. They are the #link(<equivalence-via-primitivity-shared-across-field-of-fractions>)[same up to units], meaning there's some $u in D$ unit s.t. $A = u A^prime B^prime$, thereby violating irreducibility
  - Conversely if irreducible in $F[x]$, its #link(<equivalence-via-primitivity-shared-across-field-of-fractions>)[primitive counterpart in $D[x]$] is also irreducible, since these two are associates in $F[x]$
- (2.16, p.153) theorem 2.25 $D$ UFD then $D[x]$ UFD
  - Need to check existence of factorization and uniqueness up to permutation and units
  - Existence: degree argument
  - Uniqueness: $D[x] in.rev A(x) = product_(i=1)^k d_i product_(i=1)^l q_i (x) = product_(i=1)^(k^prime) d^prime_i product_(i=1)^(l^prime) q^prime_i (x)$ two irreducible factorizations
    - First assume $A$ is primitive so we're left to deal with $product_(i=1)^l q_i (x) = product_(i=1)^(l^prime) q^prime_i (x)$
    - They are ackchyually irreducible in $F[x]$, #link(<field-of-fractions-preserve-irreducibility>)[too]
    - We know $F$ field then $F[x]$ PID thus UFD, establishing the case
    - For the general case WLOG (by multiplying units) we assume $product_(i=1)^k d_i = product_(i=1)^(k^prime) d^prime_i = scr(c)(A(x))$ the _content_ of $A$
    - Thus the scalar part is clearly unique up to associates since $D$ UFD premise. Then we're back to $A$ primitive case.
    - In short, factor into irreducibles, take the _content_ $scr(c)(A(x))$ out, then since irreducibility is maintained in $F[x]$ the polynomial ring by field of fractions the $deg > 0$ part is resolved by the fact PID implies UFD
- (2.16, p.154) $D$ UFD, $A(x) in D[x]$ monic, then any monic factor of $A(x)$ in $F[x]$ is contained in $D[x]$
  - Proof: consider monic irreducible factorization of $A(x)$
  - $D[x]$ UFD and irreducibility is #link(<field-of-fractions-preserve-irreducibility>)[inherited], these factors are also _the_ factors $F[x]$
  - Off by units is fine but the monic constraint brings us back to the ones we obtained earlier in $D[x]$

=== Generic Remarks

- A (left) $R$-module $(R, M)$ is a _ring homomorphism_ $R -> endo_ZZ (M)$, just like $G arrow.cw S$ group action is some group homomorphism $G -> aut(S)$
  - $M$ is assumed to be abelian in modules. The set of all (group) endomorphisms on $M$ are called $endo_ZZ (M)$
    - Addition by pointwise and multiplication by composition
    - $(f compose (g+h))(x) + (f compose (g+h))(y) = f(g(x) + h(x)) + f(g(y) + h(y))$
    - $(f compose (g+h))(x + y) = f(g(x) + g(y) + h(x) + h(y)) = f(g(x) + h(x)) + f(g(y) + h(y))$
  - $M$ is $R$-module, so we got $phi: R -> endo_ZZ (M)$. $ker phi = ann(M)$: some $r in R$ s.t. $forall mu in M #h(1em) r mu = 0$: ideal.
    - $quo(R / ann(M)) tilde.eq im(phi) subset.eq^"subring" endo_ZZ (M)$
    - Meaning we have another module: $M$ as $quo(R / ann(M))$-module
    - $I subideal R$ then $I M submodule M$ is also a $R$-module
      - In particular $I$ annihilates the quotient group $quo(M / (I M))$: it's a $quo(R / I)$-module.
- $D$ (integral) domain, then $deg(f(x) g(x)) = deg(f(x)) + deg(g(x))$ always work, thereby $D[x]$ domain
  - Polynomial ring $g(x) = sum_(i=0)^m b_i x^i ==> b_m^k f(x) = g(x)q(x) + r(x)$
  - (ch2.11, theorem 2.14, corollary 1) _remainder theorem_ there exists unique $q(x)$ s.t. $f(x) = (x-a)q(x) + f(a)$
  - (ch2.11, theorem 2.14, corollary 2) _factor theorem_ $(x-a) | f(x) <==> f(a) = 0$
  - Thereby $x_i in D[x_1, dots]$ is _irreducible_
    - This is _false_ for $R[x_1, dots]$ whereby $R$ not integral domain: #link("https://math.stackexchange.com/questions/2302555")[$ (2x+3)(3x+2) = x in (quo(ZZ / (6 ZZ))) [x] $]
    - In fact, $x_i$ is irreducible in $R[x]$ _iff_ $R$ has no nontrivial #link("https://math.stackexchange.com/a/2305344/595630")[idempotent] elements i.e. where $r^2 = r in R$
- Commutative ring, $r$ irreducible, then the set ${ gamma "irreducible" mid(|) r | gamma }$ is exactly the _associates_ of $r$
  - $gamma = r u$, then since $gamma$ irreducible, $u$ must be unit
- Primeness vs irreducibility...
  - $I$ maximal then $quo(I / R)$ is division ring, so if in addition $R$ commutative $quo(I/R)$ is field
    - Correspondence theorem of ring homomorphisms
  - $I$ prime then $quo(R / I)$ is integral domain
    - Prime ideal: $a b in I ==> a in I or b in I$, consider $overline(a)$ and $overline(b)$
  - Commutative integral domain then primeness implies irreducibility
  - UFD (which is commutative by convention) then irreducibility #link(<ch-2.14-ufd-then-irreducibility-implies-primeness>)[implies] primeness
  - Which is "stronger", primeness or irreducibility?
    - #quote(
        block: true,
        attribution: "naive thought",
      )[prime implies irreducible, but principal ideal of irreducible is field and field implies domain...?]
  - Principal ideal of irreducible is only maximal _amongst_ principal ideals.
    - $(1+sqrt(-5)) subideal (1+sqrt(-5), 1-sqrt(-5)) subset.neq^"ideal" ZZ[sqrt(-5)]$
    - Ideal generated by union of ideals is straightforward for all rings: $ (I union J) = {i + j mid(|) i in I and j in J} = I + J $
    - Commutative, suffices to consider $ 3 in.not (1+sqrt(-5))ZZ + (1-sqrt(-5))ZZ $
- Assuming commutative ring $R$
  - If $gcd(a, b)$ exists, $(a) union (b) = (a) + (b) subset.eq (gcd(a, b))$
    - $subset.eq$: by divisibility clearly $R a + R b$ is contained in $R gcd(a, b)$
    - $supset.eq$: this is _false_ in UFD: considering $(x) union (y) subset.neq K[x, y]$ ($K$ field)
      - Assuming PID then LHS is some $(c)$, in particular $a = c alpha$, $b = c beta$, and $c = a x + b y$
      - By GCD definition $c divides gcd(a, b)$ so $(c) supset.eq gcd(a, b)$
      - _Bezout_: there exists some $x$ and $y$ s.t. $c = a x + b y and (c) = (gcd(a, b))$
- Consider poset $a | b <==> a prec.eq b$, lattice where nodes are elements modulo equivalences by associates.
  - Unit is _the_ minimum
  - $0$ is _the_ maximum
  - Irreducibles <irreducibility-in-poset> are exactly nodes of which the only "downward" edges are just the units.
    - So those just above the unit
    - Consider $ZZ[sqrt(-5)]$. Irreducible is not enough to #link(<primeness-imply-uniqueness-of-irreducible-factorization>)[inductively show uniqueness of irreducible factorization]. In particular we may have $alpha beta = gamma zeta$ where all four are distinct irreducibles.
      - Can we have product of different number of irreducibles that are _not_ associates? $alpha beta = xi gamma zeta$ where neither of the are associates?
- $quo((F_2[x]) / ((x^2)))$ has the following multiplication table
  - $mat(
      without, 0, 1, x, x+1;
      0, 0, 0, 0, 0;
      1, 0, 1, x, x+1;
      x, 0, x, 0, x;
      x+1, 0, x+1, x, 1;
    )$
  - $1 ~ x+1$ are the units
  - $x$ is irreducible with $x^2 = 0$

=== Exercises

- (2.1, ex.3, p.89) we don't really need abelian group for addition in rings
- (2.2, ex.2, p.91) show that in a domain the only _idempotent_ elements ($x^2=x$) are $0$ and $1$ and that in a domain the only _nilpotent_ element is $0$
  - $x^2=x ==>^op("distro") x(x-1)=0 ==>^op("domain") x =0 or x=1$
  - domain, meaning the submonoid $(R without {0}, times, 1_R)$ is closed, meaning no power vanishes
  - finite ring in which the only nilpotent being $0$ is domain and thus division ring
    - powers must repeat, i.e. $x^m = x^n ==>^op("distro") x^n (x^(m-n) - 1) = 0 ==>^("domain") x^(m-n) = 1$
    - $g(x) = cases(0 "if" x < 0, x "if" x >= 0)$ and $f(x) = cases(x "if" x < 0, 0 "if" x >= 0)$: $cal(C)(RR)$, continuous endofunctions on $RR$, is a ring s.t. the only nilpotent is $(gamma mapsto 0)$ the zero function, but it's not a domain
- (2.2, ex.7, p.91) Kaplansky: ${x, r, gamma} subset.eq R and r != gamma and x r = x gamma = 1_R$ then there's infinitely many elements s.t. $x y = 1_R$. Also show this is not the case for monoids.
- (2.3, ex.6, p.97) Show that for any ring $R$ and _subset_ $S subset.eq R$, $C_R (S)$ the set of elements that commute with any $sigma in S$ is a subring in $R$. Note $C_R (R)$ is called the _center_ of the ring $R$. Find $C_(M_n (R))({e_(i j) | 1 <= i <= n and 1 <= j <= n})$ and $C_(M_n (R))(M_n (R))$.
  - additive: (subgroup criterion) ${a, b} subset.eq C_R (S) ==> (a-b) sigma =^"distro" a sigma - b sigma =^"premise" sigma a - sigma b =^"distro" sigma(a-b)$ i.e. distributive law is both-sided
  - multiplicative: trivial
  - $C_(M_n (R))({e_(i j) | 1 <= i <= n and 1 <= j <= n})$
    - Let $A = mat(bold(r)_1; bold(r)_2; bold(r)_3; dots; bold(r)_n) = mat(bold(c)_1 bold(c)_2 dots bold(c)_n)$
    - $e_(i j) times A$ is all zeros except $i$-th row is $bold(r)_j$, while $A times e_(i j)$ is all zeros except $j$-th column is $c_i$.
    - So the result is some $(a in R) dot e_(i j)$ whereby $a = r_(j j) = c_(i i)$, meaning $a_(i i) = a_(j j)$; the indices being arbitrary, $A$'s main diagonal is of same exact value
    - the other values are wiped out, so $A = (a in R) dot I$
    - For $M_n (R)$, we need stronger condition: ${a I | a in C_R (R) = Z(R)}$, e.g. we need $(a I) times (b I) = (a b) I = (b a) I = (b I) times (a I)$. Turns out this is sufficient, since $M_n (R)$ is linear combination of ${e_(i j)}$.
- (2.6, ex.5, p.103) Show that $R$ is division ring iff the only left (right) ideals are $(0)$ and $R$, as an extension to #link(<ch-2.6-thm-2.2>)[theorem 2.2]:
  - Note that left principal ideal is but some $R a$
    - Closed subgroup in the additive abelian group: distributive
    - Multiplication on the left is absorbing: associativity
  - Consider any $0 eq.not a in R$ and $R a$. It's $R$ by premise. So there's some $0 eq.not b in R$ with $b a = 1$.
  - Similarly consider $a R$ the right principal ideal generated by $a$. It's again $R$ by premise. So $a c = 1$.
  - $b = b (a c) = (b a) c = c$ so $a$ is invertible with inverse $b = c$.
- (2.7, ex.7, p.110) Suppose $S$ some subring/subfield of some ring/field $S^prime$ and that $S^prime$ is _generated by_ $S$ (namely, $S$ is a set of _generators_ for ring/field $S^prime$). Show that if $eta_1$ and $eta_2$ are ring/field homomorphisms $S^prime -> R$ agreeing on $S$, then $eta_1 = eta_2$.
  - Think of a finitely sized #link("https://en.wikipedia.org/wiki/M-ary_tree")[$2$-ary] (syntax) tree, where leaves are in $S union {1, -1}$ and internal nodes are operators ${times, plus}$ for ring homomorphism and ${times, plus, ""^(-1)}$ for field homomorphism. Value of the tree is resp. evaluation from the root.
    - In Jacobson we require subring to be submonoid (1.1, p.29) of the multiplicative monoid, which in turn meaning the _same_ exact multiplicative identity: singleton ${0}$ is ruled out.
    - Additive inverse is obtained by $(-s) = (-1) times s$.
    - The internal node operators differ: it takes more elements to form a field than that for a ring, e.g. consider any prime $p in ZZ subset.neq QQ$
  - The set of finitely sized $2$-ary trees is ring/field. $S^prime$ is generated by $S$ so $S^prime$ is contained in the set of finite $2$-ary trees.
  - Meaning every element $sigma^prime in S^prime$ admits such finite $2$-ary tree notation.
  - Meaning $eta_1$ agrees with $eta_2$ on every $sigma^prime in S^prime$. We conclude $eta_1 = eta_2$.
- (2.7, ex.8, p.110) <ch2.7-ex.8> $R$ division ring and $h: R -> R^prime eq.not 0$ homomorphism. Show that $h$ is monomorphism.
  - $0_(R^prime) 0_(R^prime) = 0_(R^prime)$ so if $0_R eq.not u in R$ got mapped to $h(u) = 0_(R^prime)$, there's no element in $R^prime$ that can bring $h(u)$ back to $1_(R^prime)$. But to be a ring homomorphism, it shall be a homomorphism on the multiplicative monoid of $R$, s.t. $1_R mapsto 1_(R^prime) eq.not 0_(R^prime)$. Thus the homomorphism on the additive group of $R$ has trivial kernel, meaning the mapping injective, thus ring monomorphism.
- (2.10, ex.1, p.126)
  - (TA) turns out for $w in CC$ and $overline(w)$ its complex conjugate, their _mimimal polynomial_ in $RR[x]$, irreducible monomial s.t. when substituted equals $0_RR$, are the same: they divide each other.
- $K$ field, show that $K[t^2, t^3] iso quo((K[x, y]) / ((x^2 - y^3))) subring K[t]$
  - Find a ring homomorphism that's invertible...?
    - Consider $phi: K[x, y] -> K[t]$ by $x mapsto t^3$ and $y mapsto t^2$ then apply first isomorphism theorem
    - In this ring we have $t^2 t^2 t^2 = t^3 t^3$ i.e. some element that can be written as product of different number of irreducible elements

=== Questions

- Maximal ideal of $QQ$? Like $({2^k/p | p != 2 and k >= 1})$?
  - Ideal containing identity is whole ring so $({1/p | p != 2})$ generates the whole ring $QQ$
  - What does $quo(QQ / ({2^k/p | p != 2 and k >= 1}))$ look like?
  - $QQ$ is not (field generated by finite elements) by virtue of lowest common multiple of the denominators
  - nvm it cannot be ideal for $1/2 times 2/3 = 1/3$ and with $1/3$ the generated ideal contains $1$
  - nah nvm $QQ$ is field so ideal contain only units so they are trivial
- #quote(
    block: true,
    attribution: [Around Jacobson Theorem 2.11, p.124],
    "There is essentially only one ring having the property stated in Theorem 2.11",
  )
  - #link(<ch-2.10-thm-2.11>)[Theorem 2.11]
- #quote(
    block: true,
    attribution: [Around Jacobson Theorem 2.12, p.126],
    "It is clear that this property of the $x$s gives another characterization of the ring $R[x_1, x_2, dots, x_r]$ as an extension of $R$",
  )
  - WTF?
- #link(<ch-2.10-thm-2.11>)[universal property for polynomial rings]: it's intriguing that we can pick whatever element to send our indeterminates to, and there _exists unique_ ring homomorphism that accompany such choice(s). Kinda remind me of the layman's terms in (homogeneous) differential equation $y^(prime prime) + 2y^prime + y = 0$ that you "wiggle" your way out via multiplying with your solution at hand by $x$.
