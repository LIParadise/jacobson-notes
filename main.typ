#set text(size: 14pt)
#import "@preview/commute:0.3.0": arr, commutative-diagram, node

== Chapter 0 Introduction

- (0.2, p.7) set $S$, map $phi: S -> S$, then $phi$ is a _transformation_ on $S$
- (0.3, p.12) $E$ equivalence relation, $iota: S -> S slash E$ defined by $a mapsto overline(a)$ is called the *natural map* of $S$ to the quotient set $S slash E$
  - (0.3, p.12) $alpha: S -> S^prime$ then _inverse image_ is $alpha^(-1) (sigma^prime) = {sigma in S | alpha(sigma) = sigma^prime}$ and $alpha^(-1) (T^prime) = {sigma in S | alpha(sigma) in T^prime subset.eq S^prime }$, which may be empty if $sigma^prime in.not im alpha$
    - _fiber over element $sigma^prime in im alpha$_ is $lr((alpha^(-1) (sigma^prime in im alpha))) != nothing$, so the set of the fibers is exactly $S slash E_alpha$
  - (0.3, p.13) $overline(alpha): S slash E_alpha -> S^prime$ given by $overline(alpha) (overline(sigma)) = alpha(sigma)$, the map of $S slash E_alpha$ *induced by* $alpha$, is a well-defined _injective_ map
    - $overline(alpha)$ bijective iff $alpha$ surjective
  - If $alpha$ injection, we say $S slash E_alpha$ can be identified with $S$ and $overline(alpha)$ can be regarded as the same as $alpha$
  - #commutative-diagram(
      node((0, 0), $S$, "domain"),
      node((0, 1), $S^prime$, "codomain"),
      node((1, 0), $S slash E_alpha$, "quotient"),

      arr("domain", "quotient", $iota$, "surj"),
      arr("domain", "codomain", $alpha$),
      arr("quotient", "codomain", $exists ! overline(alpha)$, "dashed"),
    ) $alpha = overline(alpha) compose iota$, the *factorization* of the given map $alpha$ as a product of the *natural surjective map* $iota: S -> S^prime$ and the *induced* map $overline(alpha): S slash E_alpha -> S^prime$: $iota$ _surjective_ and $overline(alpha)$ _injective_, i.e. the diagram commutes
  - Universal property: $overline(alpha)$ is the unique map that makes the diagram commute, for if $beta: S slash E_alpha -> S^prime$ satisfies $beta compose iota = alpha$, then $beta(overline(sigma)) = beta(iota(sigma)) = alpha(sigma)$ which is exactly how we define $overline(alpha)$
- Universal property: <universal-property> $alpha: S -> S^prime$ is *compatible with* equivalence relation $E$ on $S$ if $sigma E tau ==> alpha(sigma) = alpha(tau)$, $iota: S -> S slash E$ given by $sigma mapsto overline(sigma)$ the *natural surjection*, then there exists unique *induced* map $overline(alpha): S slash E -> S^prime$ s.t. $overline(alpha) compose iota = alpha$
  - the unique induced map $overline(alpha)$ is injective iff $E = E_alpha$.

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
  - Consider group. $L lt.closed.eq K = ker phi$ (so $phi$ is #link(<universal-property>)[compatible] with congruence defined by $L$), we have _induced homomorphism_ $overline(phi): a L mapsto phi(a)$, given by the _universal property_ satisfying $overline(phi) compose (a mapsto a L) = phi$. $ker overline(phi) = (ker phi) slash L = K slash L$ in particular $overline(phi)$ injective iff $K = L$.
  - $ker phi = {e} <==> phi "injective"$ is for group: the monoid of strings has homomorphism to $NN$ by length, which has trivial kernel (the empty string) but certainly not injective
  - $phi$ is equal to first epimorphism to quotient and then (exist unique) momomorphism (*induced map*) to codomain
  - #commutative-diagram(
      node((0, 0), $M$, "domain"),
      node((0, 1), $M^prime$, "codomain"),
      node((1, 0), $M slash "ker"(f)$, "quotient"),

      arr("domain", "quotient", $pi$, "surj"),
      arr("domain", "codomain", $phi$),
      arr("quotient", "codomain", $exists ! overline(phi)$, "dashed"),
    ) #link(<universal-property>)[commutes]
  - Corollary: $phi: G -> G^prime$ group epimorphism, then induced map $overline(phi): G slash ker phi -> G^prime$ is both epimorphism and monomorphism, meaning isomorphism, i.e. $im phi tilde.eq G slash ker phi$

== Chapter 2

- (2.1, p.87) the additive group of $R$ means the $(R, +, 0)$ part of ring $R$, while the multiplicative monoid denotes the $(R, times, 1)$ part.
- (2.1, p.87) subring $S$ if $(S, +, 0)$ is subgroup of the additive group of $R$ and $(S, times, 1)$ is submonoid of the multiplicative monoid of $R$
- (2.1, p.87) rings are closed under intersection, thus _subring generated by_ set is the intersection of all subrings to which the set belongs
- (2.2, p.90) domain: $(R^* := R without {0}, times, 1)$ is submonoid of the multiplicative monoid of $R$
  - closed!
  - In particular $R != 0$ i.e. $1_R != 0_R$ and $a != 0 and b != 0 => a b != 0$
  - Iff no nonzero zero divisors
  - Iff $R != 0$ and _restrict cancellation_ works on both side
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
  - They span $M_n (R)$: $A = mat(a_(1 1), a_(1 2), dots, a_(1 n); a_(2 1), a_(2 2), dots, a_(2 n); dots; a_(n 1), , dots, a_(n 1)) = limits(sum)_(i j) a_(i j) e_(i j)$
- (2.3, p.95) Identify $a in R$ in $M_n (R)$ by $op("diag") { a, a, dots, a }$
  - $a I = I a = op("diag"){a, a, dots, a} subset.eq C_(M_n (R))({e_(i j)})$ as subring (exercise 6)
  - $R -> {op("diag"){a, a, dots, a} | a in R} subset.eq M_n (R)$ isomorphism of rings: _embedding_ of $R$ in $M_n (R)$
- (2.3, p.95) For *commutative ring* we have _determinant_: \ $det A = limits(sum)_sigma (op("sgn") sigma) a_(1 sigma(1)) a_(2 sigma(2)) a_(2 sigma(2)) dots a_(n sigma(n)) \ = limits(sum)_(k=1)^n a_(r k) A_(r k) \ = limits(sum)_(k=1)^n a_(k c) A_(k c)$: _cofactor expansion_
  - $A_(r c)$ is _cofactor at row $r$ column $c$_ given by $(-1)^(r + c) det (A "sans column" c "and row" r)$
  - Cofactor expansion using different rows/columns vanishes: $limits(sum)_k a_(x k) A_(x^prime k) = limits(sum)_k a_(k x) A_(k x^prime) = 0$ if $x eq.not x^prime$
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
  - ideals are closed under intersection, thus define ideal _generated by_ some set $S$, denoted as $(S)$. We have $(S) = limits(sum)_(sigma in S) (limits(sum)_({ alpha, beta } subset.eq R) alpha sigma beta)$ (all summations are assumed to be of finite length)
    - _principal_ ideal if $I = (sigma in S)$ i.e. generated by one
  - If $R$ is commutative, \ $(S) = (sigma_1, sigma_2, ..., sigma_n) = limits(sum)_(1 <= i <= n and r_i in R) r_i sigma_i = limits(sum)_(1 <= i <= n and r_i in R) sigma_i r_i$
    - Commutative ring so _principal_ $(a)$ becomes simply ${a gamma = gamma a | gamma in R}$
- (2.5, p.101) quotient rings i.e. difference rings with respect to the ideal $I$
- (2.5, p.102) $R$ commutative ring, then field iff ideals are trivial, ${0}$ and $R$
  - $==>$: division ring, any nonzero element has inverse, $1 in I$, $1 x = x 1 = x$ absorbing so $I = R$
  - $<==$: $R = (0 eq.not a in I) subset.eq I$, meaning $a alpha = 1$ by principal ideal in commutative ring, so $alpha$ is inverse of $a$
- (2.5, p.102) $K=I+J$ the ideal _generated by_ ${i+j | i in I, j in J}$ i.e. $({i+j | i in I, j in J})$
  - simply ${i+j | i in I, j in J}$ for being closed in the additive abelian group and closed (due to distro) in the multiplicative monoid
- (2.5, p.102) $K=I J$ the ideal _generated by_ ${i j | i in I, j in J}$ i.e. $({i j | i in I, j in J})$
  - $I J subset.eq I inter J$ but the converse does not hold in general
  - $(7)^2 = (49) subset.neq (7)$
- (2.7, p.106) *homomorphism for rings* is $phi: R -> R^prime$ s.t. it's both a homomorphism for the additive group and the multiplicative monoid
  - kernel for ring homomorphism: $ker phi := phi^(-1) (0_(R^prime))$ is defined to be the kernel of $phi$ as homomorphism on the additive group. Congruence for both the additive abelian group and the multiplicative monoid, ideal.
  - $eta: R -> R^prime$, $I subset.eq ker eta$ ideal, $pi: R -> R slash I$ natural epimorphism, then $eta$ factors through $R slash I$ uniquely (universal property) with $overline(eta): overline(a) = a + I mapsto eta(a)$ s.t. $eta = overline(eta) compose pi$
  - $overline(eta)$ injective (thus monomorphism) iff $I = ker eta$
  - #commutative-diagram(
      node((0, 0), $R$, "domain"),
      node((0, 1), $R^prime$, "codomain"),
      node((1, 0), $R slash I$, "quotient"),
      
      arr("domain", "quotient", $pi$, "surj"),
      arr("domain", "codomain", $eta$),
      arr("quotient", "codomain", $exists ! overline(eta)$, "dashed"),
    ) #link(<universal-property>)[commutes]
- (2.7, p.109) _prime ring of $R$_ (modern notation *prime subring of $R$*): the smallest subring containing $1_R$ i.e. the subring generated by $1_R$
  - $phi: ZZ -> R$ given by $n mapsto n 1_R := limits(sum)_(i=1)^n 1_R$; image being subring, contained in any other subring that contains $1_R$, thus the smallest: prime subring in $R$
  - $im phi tilde.eq ZZ 1_R$ meaning $ker phi$ ideal in $ZZ$, meaning $ker phi = {0} or (k)$, the latter dubbed as _ring of residues modulo $k$_
  - Ring $R$ has prime subring being isomorphic to either $ZZ tilde.eq ZZ slash (0)$ or $ZZ slash (k)$. Define *characteristic*, $op("char") R$, to be $0$ for the former and $k$ for the latter.
    - $op("char") R = k > 0$ then $k a := limits(sum)_(i=1)^k a =^"distro" (limits(sum)_(i=1)^k 1_R) a = 0_R a = 0$ \ i.e. $forall gamma in R, thick k gamma = 0$
    - $R$ domain, then its prime subring is either $ZZ$ or $ZZ slash (p)$ whereby $p$ prime
- (2.8, p.112) $phi: R -> R^prime$ is _anti-isomorphism_ if it's isomorphism on the additive abelian group satisfying $phi(a b) = phi(b) phi(a) and phi(1_R) = 1_(R^prime)$, in which case $R$ and $R^prime$ are _anti-isomorphic_
  - For any $R$ ring we can construct $R^circle.small$, dubbed _$R$ opposite_, s.t. they are anti-isomorphic
  - _anti-automorphism_ if $phi: R -> R$, _involution_ if $phi compose phi = id$
    - transpose on the matrix ring of commutative ring $R$, $(a_(i j) mapsto a_(j i))$, is involution
    - adjoint on the matrix ring of commutative ring $R$ is involution
    - both $(psi in op("Aut") R) compose phi$ and $phi compose (psi in op("Aut") R)$ are anti-automoprhism if $phi$ is anti-automorphism

= Exercises

== Chapter 1

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
    ) in ZZ slash 3 ZZ_(3 times 3) $, the Heisenberg group
    - Note it's minimal example: by Cauchy and the fact we have no other prime orders other than $3$, the group is of size $3^n$, and $3$ is cyclic while $3^2$ is abelian.
      - That $p^2$ is abelian: consider acting on itself by conjugation: fixed points are $C_G(G) = Z_G$ and apply orbit-stabilizer theorem
- (1.9, ex.4, p.63) Consider automorphism group of cyclic groups
  - Recall that homomorphisms are described by the generators, and cyclic groups have only $1$
  - $op("Aut") ZZ tilde.eq C_2$
  - $op("Aut") C_m tilde.eq (ZZ / m ZZ)^times$ of which cardinality is Euler totient $phi(m)$
- (1.9, ex.9, p.64) fixed-point-free automorphisms...?

== Chapter 2

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
