# Solution to Problem 9 (final)

## Statement

Let \(n\ge 5\). Let \(A^{(1)},\dots,A^{(n)}\in \mathbb R^{3\times 4}\) be Zariski-generic.  
For \(\alpha,\beta,\gamma,\delta\in[n]\), define a tensor \(Q^{(\alpha\beta\gamma\delta)}\in\mathbb R^{3\times 3\times 3\times 3}\) by
\[
Q^{(\alpha\beta\gamma\delta)}_{ijkl}
=\det\!\begin{bmatrix}
A^{(\alpha)}(i,:)\\
A^{(\beta)}(j,:)\\
A^{(\gamma)}(k,:)\\
A^{(\delta)}(\ell,:)
\end{bmatrix},
\qquad i,j,k,\ell\in\{1,2,3\}.
\]
Given \(\lambda\in\mathbb R^{n\times n\times n\times n}\) with
\[
\lambda_{\alpha\beta\gamma\delta}\ne 0\iff (\alpha,\beta,\gamma,\delta)\ \text{are not all identical},
\]
consider the blockwise-scaled data \(\{T^{(\alpha\beta\gamma\delta)}\}\) where
\[
T^{(\alpha\beta\gamma\delta)}:=\lambda_{\alpha\beta\gamma\delta}\,Q^{(\alpha\beta\gamma\delta)}.
\]
(One scalar \(\lambda_{\alpha\beta\gamma\delta}\) multiplies the entire \(81\)-entry block \(Q^{(\alpha\beta\gamma\delta)}\).)

**Goal.** Construct a polynomial map \(F:\mathbb R^{81n^4}\to\mathbb R^N\), independent of the cameras, with coordinate degrees bounded independently of \(n\), such that for Zariski-generic cameras:
\[
F\bigl(\lambda_{\alpha\beta\gamma\delta}Q^{(\alpha\beta\gamma\delta)}\bigr)=0
\quad\Longleftrightarrow\quad
\exists\,u,v,w,x\in(\mathbb R^*)^n\ \text{s.t.}\ \lambda_{\alpha\beta\gamma\delta}=u_\alpha v_\beta w_\gamma x_\delta
\]
for all \((\alpha,\beta,\gamma,\delta)\) not all identical.

---

## 0. Reindexing as a single \((3n)^4\) tensor

Let
\[
P:=[n]\times\{1,2,3\},\qquad |P|=3n,
\]
and write \(p=(\alpha,i)\in P\). Stack the cameras into one matrix
\[
B\in\mathbb R^{(3n)\times 4},\qquad B_{(\alpha,i),:}=A^{(\alpha)}(i,:).
\]
Let \(r_p\in\mathbb R^4\) be the \(p\)-th row of \(B\).

Define a 4-tensor \(Q\in\mathbb R^{P\times P\times P\times P}\) by
\[
Q_{pqrs}:=\det\!\begin{bmatrix} r_p\\ r_q\\ r_r\\ r_s\end{bmatrix}.
\]
Then
\[
Q_{(\alpha,i),(\beta,j),(\gamma,k),(\delta,\ell)}=Q^{(\alpha\beta\gamma\delta)}_{ijkl}.
\]
Thus \(\mathbb R^{81n^4}\cong \mathbb R^{P^4}\cong \mathbb R^{(3n)^4}\) by coordinate permutation.

Given \(\lambda\), define \(T\in\mathbb R^{P^4}\) by blockwise scaling:
\[
T_{(\alpha,i),(\beta,j),(\gamma,k),(\delta,\ell)}:=\lambda_{\alpha\beta\gamma\delta}\,Q_{(\alpha,i),(\beta,j),(\gamma,k),(\delta,\ell)}.
\]

---

## 1. Rank-\(\le 4\) unfoldings of \(Q\)

For \(m\in\{1,2,3,4\}\), let \(Q_{(m)}\) denote the mode-\(m\) unfolding of \(Q\), a matrix of size \((3n)\times(3n)^3\).

### Lemma 1.1 (unfolding rank bound)
For each \(m\), \(\operatorname{rank}(Q_{(m)})\le 4\).

**Proof (mode 1).** Fix \(q,r,s\in P\). The column of \(Q_{(1)}\) indexed by \((q,r,s)\) is the vector \(c_{qrs}\in\mathbb R^{3n}\) with \((c_{qrs})_p=Q_{pqrs}\).
Because the determinant is linear in the first row, there exists a cofactor vector \(h(q,r,s)\in\mathbb R^4\) such that
\[
Q_{pqrs}=r_p\cdot h(q,r,s)\quad\text{for all }p.
\]
Thus \(c_{qrs}=Bh(q,r,s)\in\operatorname{col}(B)\), which has dimension \(\le 4\). Hence \(\operatorname{rank}(Q_{(1)})\le 4\). The other modes follow by symmetry. ∎

Let
\[
W:=\operatorname{col}(B)\subset\mathbb R^{3n}.
\]
For Zariski-generic cameras, \(\operatorname{rank}(B)=4\), so \(\dim W=4\).

---

## 2. Definition of the polynomial map \(F\) (degree 5)

For any tensor \(X\in\mathbb R^{P^4}\), let \(X_{(m)}\) be its mode-\(m\) unfolding.

**Define \(F(X)\)** to be the vector consisting of **all \(5\times 5\) minors** of each unfolding \(X_{(m)}\), for \(m=1,2,3,4\).

- Each coordinate is a \(5\times 5\) determinant, hence has total degree \(5\) in the entries of \(X\).
- \(F\) depends only on the input coordinates; it does not depend on the cameras.
- Degree bound \(5\) is independent of \(n\).

So \(F\) satisfies the first two bullet points of Problem 9.

We now prove the “iff” condition.

---

## 3. Forward direction: factorable \(\lambda\Rightarrow F(T)=0\)

Assume there exist \(u,v,w,x\in(\mathbb R^*)^n\) such that for all \((\alpha,\beta,\gamma,\delta)\) not all identical,
\[
\lambda_{\alpha\beta\gamma\delta}=u_\alpha v_\beta w_\gamma x_\delta.
\]
Define block-diagonal operators on \(\mathbb R^{3n}\):
\[
D(u):=\operatorname{diag}(u_1I_3,\dots,u_nI_3),
\]
and similarly \(D(v),D(w),D(x)\).

Then for \(p=(\alpha,i)\), \(q=(\beta,j)\), \(r=(\gamma,k)\), \(s=(\delta,\ell)\),
\[
T_{pqrs}=\lambda_{\alpha\beta\gamma\delta}Q_{pqrs}
=\bigl(D(u)\otimes D(v)\otimes D(w)\otimes D(x)\cdot Q\bigr)_{pqrs}.
\]
Thus each unfolding \(T_{(m)}\) is obtained from \(Q_{(m)}\) by left/right multiplication by diagonal matrices, so
\[
\operatorname{rank}(T_{(m)})=\operatorname{rank}(Q_{(m)})\le 4.
\]
Hence all \(5\times 5\) minors of all \(T_{(m)}\) vanish, i.e. \(F(T)=0\). ∎

---

## 4. Reverse direction: \(F(T)=0\Rightarrow \lambda\) factors (generic cameras)

Assume:
1. The cameras are Zariski-generic.
2. \(\lambda\) satisfies the support rule (diagonal zero; all other entries nonzero).
3. \(T=\lambda\cdot Q\) satisfies \(F(T)=0\).

Then for each \(m\),
\[
\operatorname{rank}(T_{(m)})\le 4.
\]

### 4.1 Generic spanning condition \((G3_m)\)

For mode 1, fix a triple \((\beta,\gamma,\delta)\). Consider the 27 columns of \(Q_{(1)}\) indexed by
\[
((\beta,j),(\gamma,k),(\delta,\ell))\quad\text{with }j,k,\ell\in\{1,2,3\}.
\]
These columns are \(Bh((\beta,j),(\gamma,k),(\delta,\ell))\) for cofactor vectors \(h\in\mathbb R^4\).

Define \((G3_1)\): for every \((\beta,\gamma,\delta)\) **not all equal**, these 27 columns span \(W=\operatorname{col}(B)\).

- \((G3_1)\) is Zariski-open (nonvanishing of a suitable \(4\times4\) minor of the \(3n\times 27\) column matrix).
- \((G3_1)\) is nonempty for each triple orbit type:
  - **Type A:** \((1,2,3)\) (all distinct) has an explicit witness (see below).
  - **Type B:** \((1,1,2)\) (two equal) has an explicit witness (see below).
  Relabeling camera indices sends each witness to any fixed triple of the same orbit type.
- Since the camera parameter space \((\mathbb C^{3\times4})^n\cong\mathbb C^{12n}\) is irreducible, and every nonempty Zariski-open subset is dense, we use the standard fact:

> **Fact (finite intersection on irreducible varieties).**  
> If \(X\) is irreducible and \(U_1,\dots,U_k\subseteq X\) are nonempty Zariski-open, then \(\bigcap_{i=1}^k U_i\neq\emptyset\).

Thus, for fixed \(n\), the intersection of the opens enforcing \((G3_1)\) simultaneously for all not-all-equal triples is nonempty Zariski-open.

By symmetry of the determinant in its four slots, the analogous conditions \((G3_m)\) for modes \(m=2,3,4\) are also nonempty Zariski-open; intersecting all of them remains nonempty Zariski-open.

From now on, assume the cameras lie in this nonempty Zariski-open set, and also satisfy:
- \(\operatorname{rank}(B)=4\) (so \(\dim W=4\)),
- each \(A^{(\alpha)}\) has rank 3.
These are also nonempty Zariski-open conditions.

#### Explicit witnesses for nonemptiness (mode 1)
Let \(e_1,e_2,e_3,e_4\) be the standard basis of \(\mathbb R^4\).

- **Type A (all distinct triple \((1,2,3)\)).** Take
  \[
  A^{(1)}=\begin{bmatrix}0&1&0&0\\ 0&0&1&0\\ 0&0&0&1\end{bmatrix},\quad
  A^{(2)}=\begin{bmatrix}1&0&0&0\\ 0&0&1&0\\ 0&0&0&1\end{bmatrix},\quad
  A^{(3)}=\begin{bmatrix}1&0&0&0\\ 0&1&0&0\\ 0&0&0&1\end{bmatrix}.
  \]
  For the triple \((1,2,3)\), among the 27 choices of \((j,k,\ell)\) one finds row triples \((e_2,e_3,e_4)\), \((e_1,e_3,e_4)\), \((e_1,e_2,e_4)\), \((e_1,e_2,e_3)\). Their cofactor vectors (Hodge duals of wedges) span \(\mathbb R^4\), hence the corresponding 27 columns span \(W\).

- **Type B (two equal triple \((1,1,2)\)).** Take
  \[
  A^{(1)}=\begin{bmatrix}0&1&0&0\\ 0&0&1&0\\ 0&0&0&1\end{bmatrix},\quad
  A^{(2)}=\begin{bmatrix}1&0&0&0\\ 0&1&0&0\\ 0&0&1&0\end{bmatrix}.
  \]
  For the triple \((1,1,2)\), among the 27 choices one can select four row triples whose cofactor vectors are \(\pm e_1,\pm e_2,\pm e_3,\pm e_4\), so the span is \(\mathbb R^4\) and hence the columns span \(W\).

These witnesses show the defining minors are not identically zero, proving nonemptiness.

---

### 4.2 Mode 1 implies separation in \(\alpha\)

Fix \((\beta,\gamma,\delta)\) not all equal. Define the block-diagonal matrix
\[
D_{\beta\gamma\delta}:=\operatorname{diag}(\lambda_{1\beta\gamma\delta}I_3,\dots,\lambda_{n\beta\gamma\delta}I_3).
\]
Because \((\beta,\gamma,\delta)\) is not all equal, for every \(\alpha\) the quadruple \((\alpha,\beta,\gamma,\delta)\) is not all identical, hence \(\lambda_{\alpha\beta\gamma\delta}\neq 0\); thus \(D_{\beta\gamma\delta}\) is invertible.

By \((G3_1)\), the 27 columns of \(Q_{(1)}\) corresponding to \((\beta,\gamma,\delta)\) span \(W\). In \(T_{(1)}\), those columns are obtained by multiplying the \(\alpha\)-blocks by \(\lambda_{\alpha\beta\gamma\delta}\), i.e. applying \(D_{\beta\gamma\delta}\). Hence those columns span \(D_{\beta\gamma\delta}W\).

Since \(F(T)=0\) implies \(\operatorname{rank}(T_{(1)})\le 4\), the column space \(\operatorname{col}(T_{(1)})\) has dimension \(\le 4\), but it contains \(D_{\beta\gamma\delta}W\), which has dimension 4. Therefore
\[
\operatorname{col}(T_{(1)})=D_{\beta\gamma\delta}W
\quad\text{for all }(\beta,\gamma,\delta)\text{ not all equal.}
\tag{4.1}
\]

Fix a reference triple \((\beta_0,\gamma_0,\delta_0)\) not all equal. Then (4.1) gives
\[
D_{\beta\gamma\delta}W=D_{\beta_0\gamma_0\delta_0}W,
\]
so
\[
M:=D_{\beta\gamma\delta}^{-1}D_{\beta_0\gamma_0\delta_0}
\]
stabilizes \(W\): \(MW=W\). Note \(M=\operatorname{diag}(s_1I_3,\dots,s_nI_3)\) where
\[
s_\alpha=\frac{\lambda_{\alpha\beta_0\gamma_0\delta_0}}{\lambda_{\alpha\beta\gamma\delta}}.
\]

#### Lemma 4.2 (block-scalar stabilizer rigidity)
Assume \(\operatorname{rank}(B)=4\) and each \(A^{(\alpha)}\) has rank 3.  
If \(M=\operatorname{diag}(s_1I_3,\dots,s_nI_3)\) satisfies \(MW=W=\operatorname{col}(B)\), then \(s_1=\cdots=s_n\).

**Proof.** Work over \(\mathbb C\) (valid for Zariski-generic statements). Since \(MW=W\) and \(B\) has full column rank, there exists \(R\in\mathrm{GL}_4(\mathbb C)\) with
\[
MB=BR.
\]
Restricting to the \(\alpha\)-th \(3\times4\) row block gives
\[
s_\alpha A^{(\alpha)}=A^{(\alpha)}R.
\]
Thus every row \(y\) in the row space of \(A^{(\alpha)}\) satisfies \(yR=s_\alpha y\), so the left eigenspace for eigenvalue \(s_\alpha\) has dimension at least 3. Two distinct eigenvalues would yield two distinct left eigenspaces of dimensions \(\ge 3\) whose direct sum has dimension \(\ge 6\), impossible in a 4D space. Hence all \(s_\alpha\) are equal. ∎

Applying Lemma 4.2 shows the ratio \(\lambda_{\alpha\beta_0\gamma_0\delta_0}/\lambda_{\alpha\beta\gamma\delta}\) is independent of \(\alpha\). Equivalently, there exist \(u\in(\mathbb C^*)^n\) and \(\mu\) such that
\[
\lambda_{\alpha\beta\gamma\delta}=u_\alpha\,\mu_{\beta\gamma\delta}
\qquad\text{whenever }(\beta,\gamma,\delta)\text{ are not all equal.}
\tag{4.2}
\]

---

### 4.3 Modes 2 and 3 imply separation in \(\beta\) and \(\gamma\)

Repeating the same argument with unfoldings \(T_{(2)}\) and \(T_{(3)}\) (using \((G3_2),(G3_3)\)) yields \(v,w\in(\mathbb C^*)^n\) and tensors \(\nu,\xi\) such that
\[
\lambda_{\alpha\beta\gamma\delta}=v_\beta\,\nu_{\alpha\gamma\delta}
\quad\text{whenever }(\alpha,\gamma,\delta)\text{ are not all equal,}
\tag{4.3}
\]
\[
\lambda_{\alpha\beta\gamma\delta}=w_\gamma\,\xi_{\alpha\beta\delta}
\quad\text{whenever }(\alpha,\beta,\delta)\text{ are not all equal.}
\tag{4.4}
\]

---

### 4.4 Propagate to full factorization \(u\otimes v\otimes w\otimes x\)

#### Step 1: obtain \(\lambda_{\alpha\beta\gamma\delta}=u_\alpha v_\beta\rho_{\gamma\delta}\) for \(\gamma\ne\delta\)

Fix \(\gamma\ne\delta\). Then for any \(\alpha,\beta\),
\((\beta,\gamma,\delta)\) and \((\alpha,\gamma,\delta)\) are not all equal, so (4.2) and (4.3) apply:
\[
u_\alpha\mu_{\beta\gamma\delta}=\lambda_{\alpha\beta\gamma\delta}=v_\beta\nu_{\alpha\gamma\delta}.
\]
Hence \(\mu_{\beta\gamma\delta}/v_\beta=\nu_{\alpha\gamma\delta}/u_\alpha\) depends only on \((\gamma,\delta)\). Thus there exists \(\rho_{\gamma\delta}\) such that
\[
\lambda_{\alpha\beta\gamma\delta}=u_\alpha v_\beta\,\rho_{\gamma\delta}\qquad(\gamma\ne\delta).
\tag{4.5}
\]

#### Step 2: split \(\rho_{\gamma\delta}=w_\gamma x_\delta\) for \(\gamma\ne\delta\)

Fix \(\delta\). Choose \(\alpha_0,\beta_0\) with \(\alpha_0\ne\delta\) (possible since \(n\ge 5\)). Then \((\alpha_0,\beta_0,\delta)\) are not all equal, so (4.4) applies:
\[
\lambda_{\alpha_0\beta_0\gamma\delta}=w_\gamma\,\xi_{\alpha_0\beta_0\delta}\quad\text{for all }\gamma.
\]
For \(\gamma\ne\delta\), (4.5) gives
\[
\lambda_{\alpha_0\beta_0\gamma\delta}=u_{\alpha_0}v_{\beta_0}\rho_{\gamma\delta}.
\]
Thus for all \(\gamma\ne\delta\),
\[
u_{\alpha_0}v_{\beta_0}\rho_{\gamma\delta}=w_\gamma\,\xi_{\alpha_0\beta_0\delta},
\]
so
\[
\rho_{\gamma\delta}=w_\gamma x_\delta,\qquad
x_\delta:=\frac{\xi_{\alpha_0\beta_0\delta}}{u_{\alpha_0}v_{\beta_0}}.
\]
Plug into (4.5) to get
\[
\lambda_{\alpha\beta\gamma\delta}=u_\alpha v_\beta w_\gamma x_\delta\qquad(\gamma\ne\delta).
\tag{4.6}
\]

#### Step 3: extend to \(\gamma=\delta\) off the diagonal

Fix \(g\in[n]\). Take \((\alpha,\beta,g,g)\) not all identical, i.e. \((\alpha,\beta)\ne(g,g)\). Choose \(\gamma\ne g\) (possible since \(n\ge 5\)). Then \(\gamma\ne g\), so (4.6) gives
\[
\lambda_{\alpha\beta\gamma g}=u_\alpha v_\beta w_\gamma x_g.
\]
Also, since \((\alpha,\beta,g)\) are not all equal, (4.4) applies with \(\delta=g\):
\[
\lambda_{\alpha\beta\gamma g}=w_\gamma\,\xi_{\alpha\beta g}\quad\text{for all }\gamma.
\]
Comparing for \(\gamma\ne g\) yields \(\xi_{\alpha\beta g}=u_\alpha v_\beta x_g\). Plugging \(\gamma=g\) gives
\[
\lambda_{\alpha\beta g g}=w_g\,\xi_{\alpha\beta g}=u_\alpha v_\beta w_g x_g.
\]
Together with (4.6), this proves
\[
\lambda_{\alpha\beta\gamma\delta}=u_\alpha v_\beta w_\gamma x_\delta
\]
for all \((\alpha,\beta,\gamma,\delta)\) not all identical.

---

## 5. Returning to real factors

All preceding steps are algebraic and hold for Zariski-generic real cameras. The factorization holds for the real tensor \(\lambda\), so one can choose real factors explicitly. Pick distinct indices \(a,b,c,d\in[n]\) (possible since \(n\ge 5\)). Define
\[
u_\alpha:=\lambda_{\alpha b c d},\qquad
v_\beta:=\frac{\lambda_{a\beta c d}}{u_a},\qquad
w_\gamma:=\frac{\lambda_{ab\gamma d}}{u_a v_b},\qquad
x_\delta:=\frac{\lambda_{abc\delta}}{u_a v_b w_c}.
\]
All denominators are nonzero because the corresponding quadruples have at least two distinct indices, hence are not all identical. Since \(\lambda\) is real, these \(u,v,w,x\) are real and nonzero, and they satisfy
\(\lambda_{\alpha\beta\gamma\delta}=u_\alpha v_\beta w_\gamma x_\delta\) on all not-all-identical quadruples.

---

## 6. Final conclusion

The map \(F:\mathbb R^{81n^4}\to\mathbb R^N\) defined as:

- reindex the input \(\{X^{(\alpha\beta\gamma\delta)}\}\) into \(X\in\mathbb R^{P^4}\cong\mathbb R^{(3n)^4}\),
- form the four unfoldings \(X_{(m)}\),
- output all \(5\times 5\) minors of each unfolding,

is independent of the cameras, has coordinate degree \(5\) (uniform in \(n\)), and for Zariski-generic cameras satisfies
\[
F\bigl(\lambda_{\alpha\beta\gamma\delta}Q^{(\alpha\beta\gamma\delta)}\bigr)=0
\quad\Longleftrightarrow\quad
\exists\,u,v,w,x\in(\mathbb R^*)^n\text{ s.t. }\lambda_{\alpha\beta\gamma\delta}=u_\alpha v_\beta w_\gamma x_\delta
\]
for all \((\alpha,\beta,\gamma,\delta)\) not all identical.

This answers Problem 9 in the affirmative with a uniform degree bound \(5\).
