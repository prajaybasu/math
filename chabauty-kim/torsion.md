# Fixed depth on the torsion component

For the thrice-punctured line over the rationals with $S=\{2,3\}$, the target is equality of the full refined depth-four locus with the 21 integral points for a set of auxiliary primes of Dirichlet density one. Lüdtke's Lemma 3.1 gives a sufficient reduction to the two components $(1,1)$ and $(1,0)$. On $(1,1)$ the equations include $\log(z)=\operatorname{Li}_2(z)=\operatorname{Li}_4(z)=0$. Every such point is a Teichmüller root of unity reducing to $a\in\mathbb F_p\setminus\{0,1\}$. The integral point $-1$ belongs to this component. These facts hold for $S=\{2,q\}$ with any odd prime $q\ne p$. [Lüdtke, Lemma 3.1, Theorem 3.2 and Remark 3.3](https://arxiv.org/html/2402.03573v2#S3)

The fixed depth matters. At weight $p-3$, Betts–Kumpitsch–Lüdtke already isolate $-1$ for every $p\ge5$. They also cite Stix for the $S$-Selmer Section Conjecture on this rational curve for every $S$. A density-one determination at depth four would give another route to that consequence. [Betts–Kumpitsch–Lüdtke, introduction and Proposition 5.15](https://arxiv.org/html/2305.09462) · [Stix, Corollary 6](https://arxiv.org/abs/1203.3236)

## A sufficient cross-prime criterion

Write $\ell_m(X)=\sum_{j=1}^{p-1}j^{-m}X^j$. For $p\ge7$, Besser's reduction implies that any common Coleman zero above has $\ell_2(a)=\ell_4(a)=0$. Here the factor $a-1$ in the normalization is a unit. The implication from an exact zero to a finite-field zero goes in this direction. [Besser, Proposition 2.1](https://arxiv.org/pdf/math/0006051)

Let $B_0=1$ and $B_{n+1}=X((1-X)B_n'+(n+1)B_n)$. For $n>0$, $B_n$ is $X$ times the ordinary Eulerian polynomial. For $n+m=p-1$, $n>0$, one has the polynomial identity
$$
(1-X)^{n+1}\ell_m(X)=(1-X^p)B_n(X)\quad\text{in }\mathbb F_p[X].
$$
Indeed the Euler derivative $X\,d/dX$ multiplies the coefficient of $X^j$ by $j$. Its $n$th iterate on $1+X+\cdots+X^{p-1}$ yields $\ell_m$ by Fermat's theorem. Differentiating the cleared geometric identity gives the stated recurrence because $(X^p)'=0$. For $a\in\mathbb F_p$ with $a\ne1$, both prefactors in the identity are units on evaluation. [Lean proof](../lean/BBPGrouping/TorsionDisc.lean)

Put
$$
M_p=\frac{X^{p-1}-1}{X^2-1},\qquad
G_p=\gcd(M_p,B_{p-3},B_{p-5})
$$
with monic gcd over $\mathbb F_p$. The first polynomial is the product of the distinct linear factors for all $a\notin\{0,1,-1\}$. Thus $\deg G_p$ counts exactly the extra common zeros of the **two reductions**. If $G_p=1$, the only possible residue for the $(1,1)$ component is $-1$, with unique Teichmüller lift $-1$. Lean proves this last implication given the two finite-polylogarithm vanishings. If $G_p$ has positive degree, its roots are the residues requiring higher precision.

A sufficient target for this component is that the primes with $\deg G_p>0$ have Dirichlet density zero. For example, the stronger first-moment estimate
$$
\sum_{7\le p\le x}\deg G_p=o(\pi(x))
$$
would suffice, since each exceptional prime contributes at least one. The existing per-prime power saving bounds the size of a possible exception, and supplies no estimate of this average tending to zero. The distribution of these split common factors across primes and the separate $(1,0)$ component remain open in this argument.

## The factor for primitive fourth roots

Fix $p\equiv1\pmod4$, $p\ge 7$, and $i\in\mathbb F_p$ with $i^2=-1$. Use signed Euler numbers $E_n$ given by $1/\cosh t=\sum_n E_n t^n/n!$. For $m=2,4$ put $n=p-1-m$. Then
$$
\ell_m(i)=(1-i)\frac{i}{2} E_n\pmod p.
$$
To obtain the coefficient, work first over $\mathbb Q(\mathrm i)$ with $\mathrm i^2=-1$. The $n$th derivative at zero of $1/(1-\mathrm i e^t)$ is $B_n(\mathrm i)/(1-\mathrm i)^{n+1}$ by the Euler recurrence above. Rewriting the same series as
$$
\frac{1-\tanh t}{2}+\frac{\mathrm i}{2\cosh t}
$$
shows that its positive even derivatives are $\mathrm i E_n/2$. This equality of elements of $\mathbb Z[\mathrm i,1/2]$ reduces at either choice of $i$. The cleared finite-polylogarithm identity supplies the remaining factor $1-i^p=1-i$.

Consequently $X^2+1$ divides $G_p$ exactly when $p$ divides both $E_{p-3}$ and $E_{p-5}$. This also explains why failure of the weight-two test at an Euler-irregular index can be resolved by weight four.

Meštrović reports an exhaustive weight-two search below $10^7$ with three exceptions. Direct finite sums at these primes give the following residues. Anyone can reproduce each column using the expression below. [Meštrović, Table 1 and introduction](https://arxiv.org/abs/1212.3602)

| $p$ | $i$ | $\ell_2(i)$ | $\ell_4(i)$ |
|---:|---:|---:|---:|
| 149 | 44 | 0 | 143 |
| 241 | 64 | 0 | 105 |
| 2946901 | 722077 | 0 | 1422053 |

```python
def finite_li_at_i(p, i, m):
    assert i * i % p == p - 1
    powers = (1, i, -1, -i)
    return sum(powers[j % 4] * pow(j, -m, p) for j in range(1, p)) % p
```

Together with the reported search this excludes primitive fourth roots on the $(1,1)$ component throughout $7\le p<10^7$. For $p\equiv3\pmod4$ there are no fourth roots of order four in the residue field. The Euler-number specialization here is a written calculation using the Lean-checked Eulerian identity. Bounding the density of simultaneous Euler divisibilities would address just this order.


### A second digit at the three weight-two exceptions

Lift the displayed root $i$ to $i^2=-1\pmod{p^2}$ and put $q=p^2$. The weight-two unit moment
$$
M=\frac{1}{1-i}\sum_{1\le a<q,\ p\nmid a}i^a a^{-2}\pmod q
$$
has valuation exactly one at each of the three primes. In the order of the table, $M/p\bmod p$ is $85$, $103$ and $1795894$. Thus weight two alone excludes the fourth roots at these three primes when one uses a second digit. The passage to the Coleman value uses its prime-depleted measure formula: the integral of $x^{-2}$ over the units is $(1-p^{-2})\operatorname{Li}_2(i)$ for the measure with mass $i^a/(1-i^{p^r})$ on the class $a+p^r\mathbb Z_p$, $0\le a<p^r$. The displayed sum gives this moment modulo $q$ since $i^q=i$. Changing $i$ to $-i$ negates the moment by the substitution $a\mapsto q-a$. [Coleman, *Dilogarithms, regulators and p-adic L-functions*](https://www.digizeitschriften.de/download/pdf/356556735_0069/log29.pdf)

To evaluate the second digit in $O(p)$ summands, write $a=u+pb$. For $0\le b<p$, the sum of $i^b$ is $1$ and the sum of $b i^b$ is $(p-1)(1-i)/2$. Using $(u+pb)^{-2}\equiv u^{-2}-2pb u^{-3}\pmod q$ gives the following calculation.

```python
def second_digit(p, i):
    q = p * p
    i = (i - p * ((i*i + 1) // p) * pow(2*i, -1, p)) % q
    assert (i*i + 1) % q == 0
    powers = (1, i, -1, -i)
    correction = p * (p-1) * (1-i) % q
    total = 0
    for u in range(1, p):
        h = pow(u, -1, q)
        total += powers[u % 4] * (h*h % q) * (1 - correction*h % q)
    moment = total * pow(1-i, -1, q) % q
    assert moment % p == 0
    return moment // p
```

## Orders three, four and six at full precision

Fix a weight $k\in\{2,4\}$. For $d=3,4$ take $p\ge7$ with $p\equiv1\pmod d$, a primitive $d$-th root $\eta\in\mathbb Z_p$, and the primitive odd quadratic character $\chi$ of conductor $d$. Write $\omega$ for the Teichmüller character modulo $p$. With the convention $L_p(1-j,\psi)=(1-(\psi\omega^{-j})(p)p^{j-1})L(1-j,\psi\omega^{-j})$ using the primitive character in the Euler factor, the exact formula is
$$
2(1-p^{-k})\operatorname{Li}_k(\eta)
 = (\eta-\eta^{-1})L_p(k,\chi\omega^{1-k}).
$$
The branch $\chi\omega^{1-k}$ is even. Both displayed prefactors are nonzero. In particular the equality compares vanishing at a specific argument on a specified branch. [Coleman, §§VI–VII](https://www.digizeitschriften.de/download/pdf/356556735_0069/log29.pdf) · [Kubota–Leopoldt interpolation, equation (1.1)](https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/sum-expressions-for-kubotaleopoldt-padic-lfunctions/1DF77ECEC0EE657089F2E26C0F8AA351)

To see the normalization, the character transform of the additive weights is $\eta^a-\eta^{-a}=(\eta-\eta^{-1})\chi(a)$ for every integer $a$. For even weight the two inverse-root moments have opposite signs. Their difference thus contributes the factor 2. More explicitly, let $n_r=p^{r-1}(p-1)-k$. On the units modulo $p^r$, $a^{n_r}=a^{-k}$. The difference of the two full power moments at exponent $n_r$ is $(\eta-\eta^{-1})L(-n_r,\chi)$ by the character transform and the Bernoulli generating series. Removing multiples of $p$ multiplies it by $1-p^{n_r}$ since $\eta^p=\eta$. Interpolation and $-n_r\to k$ in $\mathbb Z_p$ give the formula. The single-root moment modulo $p^r$ can be evaluated directly as $(1-\eta)^{-1}\sum_{1\le a<p^r,\ p\nmid a}\eta^a a^{-k}$.

For a primitive **sixth** root $\xi$ put $\eta=\xi^2$ of order three. Then $-\xi=\eta^{-1}$. Doubling gives $\operatorname{Li}_k(\xi)+\operatorname{Li}_k(-\xi)=2^{1-k}\operatorname{Li}_k(\eta)$, and even-weight inversion gives $\operatorname{Li}_k(\eta^{-1})=-\operatorname{Li}_k(\eta)$. Hence
$$
\operatorname{Li}_2(\xi)=\tfrac32\operatorname{Li}_2(\xi^2),\qquad
\operatorname{Li}_4(\xi)=\tfrac98\operatorname{Li}_4(\xi^2).
$$
Both factors are $p$-adic units for $p\ge7$. This identifies the two vanishing tests at every precision. The odd character modulo six is induced from conductor three. Lean proves the scalar relation and equivalence of zeros from the distribution and inversion identities. [Lean declaration](../lean/BBPGrouping/TorsionDisc.lean) · [Coleman's functional equations](https://www.digizeitschriften.de/download/pdf/356556735_0069/log29.pdf)

Thus these three torsion orders give two conductor cases. For each conductor the fixed-order density question asks whether the split primes at which **both** $L_p(2,\chi\omega^{-1})$ and $L_p(4,\chi\omega^{-3})$ vanish form a set of Dirichlet density zero. Other torsion orders and the $(1,0)$ component enter separately.

### Conductor three below twenty million

For $p\ge7$, the weight-two and weight-four branch characters have quotient $\omega^2$, of order $(p-1)/2$. Hence each branch has its own Iwasawa power series. A fixed-branch zero count does not give the frequency of simultaneous zeros as $p$ varies.

Let $p\equiv1\pmod3$, let $\eta$ be a primitive cubic root and write $M_k=(1-p^{-k})\operatorname{Li}_k(\eta)$. With $h=p-k$ odd, the first digit is
$$
M_k\equiv -\frac{(\eta-\eta^{-1})3^{h-1}}{h}B_h(1/3)\pmod p.
$$
Indeed the unit moment is congruent to the power moment of exponent $h-1$. The Euler factor $1-p^{h-1}$ is $1$ modulo $p$. The formula for $L(1-h,\chi_{-3})$ gives $-3^{h-1}(B_h(1/3)-B_h(2/3))/h$, and reflection gives $B_h(2/3)=-B_h(1/3)$. All factors multiplying $B_h(1/3)$ in the displayed congruence are units.

Sun reports that $205129$ is the only prime $3<p<2\cdot10^7$ with $B_{p-2}(1/3)\equiv0\pmod p$. At that prime the Teichmüller root with residue $81187$ gives $M_2\equiv170025p\pmod{p^2}$ and $M_4\equiv30238\pmod p$. The inverse root gives the negatives. Thus, using Sun's reported range, weight two excludes primitive cubic and sixth roots on the $(1,1)$ component for every auxiliary prime $7\le p<2\cdot10^7$. At nonsplit primes these roots do not belong to $\mathbb Q_p$. [Sun, *Open Conjectures on Congruences*, Remark 17](https://www.researchgate.net/publication/336577970_Open_Conjectures_on_Congruences)

To reproduce the exceptional prime, group the unit moment modulo $q=p^2$ by $a=u+pb$. For $0\le b<p$ the sums of $z^b$ and $b z^b$ are $1$ and $(p-1)z/(z-1)$ respectively. The binomial expansion of $(u+pb)^{-k}$ then gives the following calculation. [Block sum identities in Lean](../lean/BBPGrouping/TorsionDisc.lean)

```python
def cubic_moment(p, residue, k):
    q = p*p
    z = pow(residue, p, q)
    assert (z*z + z + 1) % q == 0
    powers = (1, z, z*z % q)
    den = pow(1-z, -1, q)
    correction = k*p*(p-1)*z*den % q
    total = 0
    for u in range(1, p):
        inv = pow(u, -1, q)
        total += powers[u % 3] * pow(inv, k, q) * (1 + correction*inv % q)
    return total * den % q

p = 205129
assert cubic_moment(p, 81187, 2) == 170025*p
assert cubic_moment(p, 81187, 4) % p == 30238
```

## Reproducible finite check

In Sage the equivalent finite-polylogarithm gcd avoids constructing large integer Eulerian coefficients. This checks all 427 primes from 7 through 3000 and finds $G_p=1$ at each. This lies inside Lüdtke's published range.

```python
from sage.all import GF, PolynomialRing, prime_range

checked = 0
for prime in prime_range(7, 3001):
    p = int(prime)
    R = PolynomialRing(GF(p), "x")
    x = R.gen()
    inv = [0, 1]
    for j in range(2, p):
        inv.append(-(p // j) * inv[p % j] % p)
    l2 = R([a**2 % p for a in inv])
    l4 = R([a**4 % p for a in inv])
    M = (x**(p-1) - 1) // (x**2 - 1)
    assert M.gcd(l2).gcd(l4) == 1, p
    checked += 1
assert checked == 427
```
