# Proof-search solutions for the arend-lib benchmark

Best proof found for each of the 300 benchmark lemmas across the recorded runs: **222 proved (74%)**. Each `src/Bench_*.ard` module restates the lemmas of one arend-lib module (or class) with the found proof as its body; unproved lemmas keep `{?}`. The library typechecks against arend-lib (goals are not errors).

| module | proved |
|---|---|
| Bench_Algebra_Field_DiscreteField | 4 / 7 |
| Bench_Algebra_Group | 6 / 6 |
| Bench_Algebra_Group_AbGroup | 4 / 6 |
| Bench_Algebra_Group_AddGroup | 10 / 11 |
| Bench_Algebra_Group_Group | 2 / 2 |
| Bench_Algebra_Monoid_AbMonoid | 2 / 5 |
| Bench_Algebra_Monoid_AddMonoid | 11 / 17 |
| Bench_Algebra_Monoid_Monoid | 14 / 14 |
| Bench_Algebra_Ordered_AbsAbGroup | 0 / 3 |
| Bench_Algebra_Ordered_LatticeAbGroup | 8 / 13 |
| Bench_Algebra_Ordered_PosetAddGroup | 1 / 4 |
| Bench_Algebra_Ring_PseudoRing | 7 / 7 |
| Bench_Algebra_Ring_Ring | 1 / 2 |
| Bench_Algebra_Semiring_Semiring | 1 / 1 |
| Bench_Arith_Int | 15 / 19 |
| Bench_Arith_Nat | 49 / 71 |
| Bench_Data_Bool | 2 / 2 |
| Bench_Data_Fin | 8 / 8 |
| Bench_Data_List | 9 / 16 |
| Bench_Logic | 14 / 19 |
| Bench_Order_Lattice_BottomDistributiveLattice | 2 / 2 |
| Bench_Order_Lattice_BottomJoinSemilattice | 7 / 9 |
| Bench_Order_Lattice_DistributiveLattice | 3 / 4 |
| Bench_Order_Lattice_JoinSemilattice | 10 / 11 |
| Bench_Order_Lattice_Lattice | 1 / 1 |
| Bench_Order_Lattice_MeetSemilattice | 9 / 10 |
| Bench_Order_Lattice_TopMeetSemilattice | 3 / 3 |
| Bench_Order_LinearOrder | 0 / 1 |
| Bench_Order_LinearOrder_LinearLattice | 0 / 1 |
| Bench_Order_LinearOrder_TotalOrder | 4 / 8 |
| Bench_Order_PartialOrder | 2 / 2 |
| Bench_Order_StrictOrder_StrictPoset | 2 / 2 |
| Bench_Set | 10 / 12 |
| Bench_Set_Set | 1 / 1 |

## Proofs

| module | lemma | proof | run |
|---|---|---|---|
| Algebra_Field_DiscreteField | `finv-left` | `=> equation.cRing {finv-right x/=0}` | final run (current code, 10 s per lemma) |
| Algebra_Field_DiscreteField | `finv-Inv` | `=> Monoid.Inv.lmake _ (equation.cRing {DiscreteField.finv-left x/=0})` | final run (current code, 10 s per lemma) |
| Algebra_Field_DiscreteField | `nonZero-Inv` | `=> Monoid.Inv.lmake _ (equation.cRing {DiscreteField.finv-left x/=0})` | final run (current code, 10 s per lemma) |
| Algebra_Field_DiscreteField | `finv/=0` | `=> Algebra.Semiring.NonZeroSemiring.inv-nonZero (DiscreteField.finv-Inv x/=0)` | final run (current code, 10 s per lemma) |
| Algebra_Group | `conjugate-via-id` | `=> unfold conjugate (rewrite Group.inverse_ide equation)` | final run (current code, 10 s per lemma) |
| Algebra_Group | `commutator=ide<->comm` | `=> (\lam p => equation.group {pmap (\lam z => z * (h * {E} g)) p}, \lam p => unfold commutator (rewrite p (equation.group {p})))` | final run (current code, 10 s per lemma) |
| Algebra_Group | `comm_sym` | `=> equation.group {pmap inverse p}` | final run (current code, 10 s per lemma) |
| Algebra_Group | `comm_conjugate` | `=> equation.group {pmap (\lam z => z * h) p}` | final run (current code, 10 s per lemma) |
| Algebra_Group | `comm_inverse-right` | `=> Algebra.Group.comm_sym (Algebra.Group.comm_inverse-left (equation.group {Algebra.Group.comm_sym p}))` | final run (current code, 10 s per lemma) |
| Algebra_Group | `comm_inverse-left` | `=> Algebra.Group.comm_sym (Algebra.Group.comm_inverse-right (equation.group {Algebra.Group.comm_sym p}))` | final run (current code, 10 s per lemma) |
| Algebra_Group_AbGroup | `diff-cancel-left` | `=> rewrite AbGroup.negative_+-comm AbGroup.sum-cancel-left *> AddGroup.negative_-` | final run (current code, 10 s per lemma) |
| Algebra_Group_AbGroup | `negative_+-comm` | `=> rewrite AddGroup.negative_+ equation` | final run (current code, 10 s per lemma) |
| Algebra_Group_AbGroup | `diff_sum` | `=> pmap ((+) {A} x) AbGroup.negative_+-comm *> inv +-assoc` | final run (current code, 10 s per lemma) |
| Algebra_Group_AbGroup | `diff_diff` | `=> AbGroup.diff_sum *> pmap ((+) {A} (x - {_} y)) AddGroup.negative-isInv` | final run (current code, 10 s per lemma) |
| Algebra_Group_AddGroup | `cancel-left` | `=> cancel_*-left {toGroup A} _ {_} {_} p` | final run (current code, 10 s per lemma) |
| Algebra_Group_AddGroup | `cancel-right` | `=> cancel_*-right {toGroup A} _ {_} {_} p` | final run (current code, 10 s per lemma) |
| Algebra_Group_AddGroup | `negative-isInv` | `=> Group.inverse-isInv {toGroup A} {_}` | final run (current code, 10 s per lemma) |
| Algebra_Group_AddGroup | `negative_+` | `=> Group.inverse_* {toGroup A} {_} {_}` | final run (current code, 10 s per lemma) |
| Algebra_Group_AddGroup | `negative_-` | `=> rewrite AddGroup.negative_+ (rewrite AddGroup.negative-isInv idp)` | final run (current code, 10 s per lemma) |
| Algebra_Group_AddGroup | `minus_zro` | `=> unfold (-) (rewrite negative_zro equation)` | final run (current code, 10 s per lemma) |
| Algebra_Group_AddGroup | `fromZero` | `=> equation.addGroup {pmap (\lam z => z + y) x-y=0}` | final run (current code, 10 s per lemma) |
| Algebra_Group_AddGroup | `toZero` | `=> unfold (-) (equation.addGroup {pmap (\lam z => z + negative {A} y) x=y})` | final run (current code, 10 s per lemma) |
| Algebra_Group_AddGroup | `diff_+` | `=> inv +-assoc *> rewrite AddGroup.minus_+ idp` | final run (current code, 10 s per lemma) |
| Algebra_Group_AddGroup | `minus_+` | `=> +-assoc *> rewrite negative-left equation` | final run (current code, 10 s per lemma) |
| Algebra_Group_Group | `inverse-isInv` | `=> AddGroup.negative-isInv {AddGroup.fromGroup A} {_}` | final run (current code, 10 s per lemma) |
| Algebra_Group_Group | `inverse_*` | `=> AddGroup.negative_+ {AddGroup.fromGroup A} {_} {_}` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_AbMonoid | `FinSum_zro` | `=> \case FinSum_char x \with {   \| inP (e, p') => rewrite p' (AddMonoid.BigSum_zro (\lam j => p _)) }` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_AbMonoid | `FinSum-pred` | `=> \case FinSum_char a \with {   \| inP (e, p') => rewrite p' (AddMonoid.BigSum-pred P0 P+ (\lam j => p _)) }` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_AddMonoid | `*n-rdistr` | `\elim m   \| zero => equation   \| suc m => equation.addMonoid {*n-rdistr {A} {n} {m} {a}}` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_AddMonoid | `BigSum-ext` | `=> Monoid.BigProd-ext {toMonoid A} {_} {_} {_} p` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_AddMonoid | `BigSum_++` | `=> Monoid.BigProd_++ {toMonoid A} {_} {_}` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_AddMonoid | `BigSum_Big++` | `\elim ls   \| nil => idp   \| :: a ls => rewrite AddMonoid.BigSum_++ (equation.addMonoid {BigSum_Big++ {A} {ls}})` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_AddMonoid | `BigSum_++'` | `\elim l   \| nil => equation   \| :: a l => equation.addMonoid {BigSum_++' {A} {l} {n} {l'}}` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_AddMonoid | `BigSum-split` | `\elim n, l   \| zero, l => equation   \| suc n, :: a l => equation.addMonoid {BigSum-split {A} {n} {m} {l}}` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_AddMonoid | `BigSum_suc` | `=> Monoid.BigProd_suc {toMonoid A} {_} {_}` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_AddMonoid | `BigSum_suc-nat` | `=> rewrite AddMonoid.BigSum_suc (rewrite (mod_< linarith) idp)` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_AddMonoid | `BigSum_zro` | `=> Monoid.BigProd_ide {toMonoid A} {_} p` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_AddMonoid | `BigSum-unique` | `\elim l, i, p   \| nil, i, p => idp   \| :: a l, i, p => Monoid.BigProd-unique {toMonoid A} {_} _ p` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_AddMonoid | `BigSum-pred` | `\elim l, p   \| nil, p => P0   \| :: a l, p => P+ (p zero) (BigSum-pred P0 P+ (\lam j => p (suc j)))` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_Monoid | `pow_+` | `\elim m   \| zero => equation   \| suc m => equation.monoid {pow_+ {A} {a} {n} {m}}` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_Monoid | `pow_*` | `\elim m   \| zero => idp   \| suc m => rewrite Monoid.pow_+ (equation.monoid {pow_* {A} {a} {n} {m}})` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_Monoid | `pow-comm1` | `\elim n   \| zero => equation   \| suc n => equation.monoid {(p, pow-comm1 {A} {a} {b} p {n})}` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_Monoid | `pow-comm2` | `=> Monoid.pow-comm1 (equation.monoid {Monoid.pow-comm1 (inv p)})` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_Monoid | `pow-comm` | `\elim n   \| zero => equation   \| suc n => equation.monoid {(pow-comm {A} {a} {b} p {n}, Monoid.pow-comm1 (inv p))}` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_Monoid | `pow-left` | `\elim n   \| zero => equation   \| suc n => equation.monoid {pow-left {A} {a} {n}}` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_Monoid | `BigProd-ext` | `=> AddMonoid.BigSum-ext {AddMonoid.fromMonoid A} {_} {_} {_} p` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_Monoid | `BigProd_ide` | `=> AddMonoid.BigSum_zro {AddMonoid.fromMonoid A} {_} p` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_Monoid | `BigProd-unique` | `\elim l, i, p   \| nil, i, p => idp   \| :: a l, i, p => AddMonoid.BigSum-unique {AddMonoid.fromMonoid A} {_} _ p` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_Monoid | `BigProd_++` | `=> AddMonoid.BigSum_++ {AddMonoid.fromMonoid A} {_} {_}` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_Monoid | `BigProd_suc` | `=> AddMonoid.BigSum_suc {AddMonoid.fromMonoid A} {_} {_}` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_Monoid | `BigProd_replicate` | `\elim n   \| zero => idp   \| suc n => rewrite Monoid.BigProd_suc (equation.monoid {BigProd_replicate {A} {x} {n}})` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_Monoid | `IsCentral_*` | `=> \lam y' => equation.monoid {(yc y', xc y')}` | final run (current code, 10 s per lemma) |
| Algebra_Monoid_Monoid | `IsCentral_pow` | `=> \lam y => Monoid.pow-comm1 (xc _)` | final run (current code, 10 s per lemma) |
| Algebra_Ordered_LatticeAbGroup | `abs>=id` | `=> join-left` | final run (current code, 10 s per lemma) |
| Algebra_Ordered_LatticeAbGroup | `abs>=neg` | `=> join-right` | final run (current code, 10 s per lemma) |
| Algebra_Ordered_LatticeAbGroup | `abs_negative` | `=> unfold abs (rewrite AddGroup.negative-isInv JoinSemilattice.join-comm)` | final run (current code, 10 s per lemma) |
| Algebra_Ordered_LatticeAbGroup | `abs_-` | `=> rewriteI AddGroup.negative_- LatticeAbGroup.abs_negative` | final run (current code, 10 s per lemma) |
| Algebra_Ordered_LatticeAbGroup | `abs_-left` | `=> rewrite LatticeAbGroup.abs_- LatticeAbGroup.abs_-right` | final run (current code, 10 s per lemma) |
| Algebra_Ordered_LatticeAbGroup | `abs_-right` | `=> rewrite LatticeAbGroup.abs_- LatticeAbGroup.abs_-left` | final run (current code, 10 s per lemma) |
| Algebra_Ordered_LatticeAbGroup | `abs>=_-` | `=> rewrite LatticeAbGroup.abs_- LatticeAbGroup.abs>=id` | final run (current code, 10 s per lemma) |
| Algebra_Ordered_LatticeAbGroup | `abs-univ` | `=> join-univ p (rewrite AddGroup.negative_- q)` | final run (current code, 10 s per lemma) |
| Algebra_Ordered_PosetAddGroup | `negative_<=-conv` | `=> transport (\lam z => z <= {A} y) AddGroup.negative-isInv    (transport (\lam z => negative {A} (negative {A} x) <= {A} z) AddGroup.negative-isInv (PosetAddGroup.negative_<= p))` | final run (current code, 10 s per lemma) |
| Algebra_Ring_PseudoRing | `negative_*-left` | `=> inv PseudoRing.negative_* *> rewrite AddGroup.negative-isInv PseudoRing.negative_*-right` | final run (current code, 10 s per lemma) |
| Algebra_Ring_PseudoRing | `negative_*-right` | `=> inv PseudoRing.negative_* *> rewrite AddGroup.negative-isInv PseudoRing.negative_*-left` | final run (current code, 10 s per lemma) |
| Algebra_Ring_PseudoRing | `negative_*` | `=> rewrite PseudoRing.negative_*-left (rewrite PseudoRing.negative_*-right AddGroup.negative-isInv)` | final run (current code, 10 s per lemma) |
| Algebra_Ring_PseudoRing | `ldistr_-` | `=> unfold (-) (rewriteI PseudoRing.negative_*-right ldistr)` | final run (current code, 10 s per lemma) |
| Algebra_Ring_PseudoRing | `rdistr_-` | `=> unfold (-) (rewriteI PseudoRing.negative_*-left rdistr)` | final run (current code, 10 s per lemma) |
| Algebra_Ring_PseudoRing | `*_sum_diff` | `=> rewrite rdistr (rewrite PseudoRing.ldistr_- (rewrite PseudoRing.ldistr_- (equation.abGroup {AddGroup.toZero (inv p)})))` | final run (current code, 10 s per lemma) |
| Algebra_Ring_PseudoRing | `*_diff_sum` | `=> rewrite ldistr (rewrite PseudoRing.rdistr_- (rewrite PseudoRing.rdistr_- (equation.abGroup {p})))` | final run (current code, 10 s per lemma) |
| Algebra_Ring_Ring | `idempotent_LDiv` | `=> \case Monoid.LDiv.inv-right {d} \with {   \| q' => rewriteI q' (inv PseudoRing.negative_* *> equation.ring {pmap (\lam z => z * negative {A} (Monoid.DivBase.inv {d})) q}) }` | final run (current code, 10 s per lemma) |
| Algebra_Semiring_Semiring | `natCoef-comm` | `=> Algebra.Ring.RingHom.natComm _ _` | final run (current code, 10 s per lemma) |
| Arith_Int | `iabs_*` | `\elim x, y   \| pos x, pos x' => idp   \| pos x, neg x'' => idp   \| neg zero, pos x => idp   \| neg zero, neg x' => idp   \| neg (suc x'), pos x => idp   \| neg (suc x'), neg x'' => idp` | final run (current code, 10 s per lemma) |
| Arith_Int | `ldiv_iabs` | `=> Algebra.Domain.Euclidean.ldiv_int_nat _` | final run (current code, 10 s per lemma) |
| Arith_Int | `id<isuc` | `\elim x   \| pos x => linarith   \| neg zero => linarith   \| neg (suc x') => linarith` | final run (current code, 10 s per lemma) |
| Arith_Int | `pos_iabs` | `\elim x, y, y<=x   \| zero, y, y<=x => linarith   \| suc x, zero, y<=x => idp   \| suc x, suc y, y<=x => iabs.ofPos linarith` | final run (current code, 10 s per lemma) |
| Arith_Int | `neg_iabs` | `\elim x, y, x<=y   \| zero, y, x<=y => idp   \| suc x, zero, x<=y => linarith   \| suc x, suc y, x<=y => neg_iabs linarith` | final run (current code, 10 s per lemma) |
| Arith_Int | `iabs_-_suc` | `\elim n, i, p   \| n, zero, p => idp   \| zero, suc i, p => linarith   \| suc n, suc i, p => iabs_-_suc linarith` | final run (current code, 10 s per lemma) |
| Arith_Int | `zro-id=neg` | `=> idp` | final run (current code, 10 s per lemma) |
| Arith_Int | `-'=-` | `\elim n, m, p   \| zero, m, p => linarith   \| suc n, zero, p => idp   \| suc n, suc m, p => -'=- linarith` | final run (current code, 10 s per lemma) |
| Arith_Int | `unpos` | `=> pmap iabs p` | final run (current code, 10 s per lemma) |
| Arith_Int | `pos<pos` | `=> linarith` | final run (current code, 10 s per lemma) |
| Arith_Int | `neg<neg` | `=> linarith` | final run (current code, 10 s per lemma) |
| Arith_Int | `pos<=pos` | `=> linarith` | final run (current code, 10 s per lemma) |
| Arith_Int | `neg<=pos` | `=> linarith` | final run (current code, 10 s per lemma) |
| Arith_Int | `pos/<=neg` | `=> Arith.Int.unpos linarith` | final run (current code, 10 s per lemma) |
| Arith_Int | `neg<=neg` | `=> linarith` | final run (current code, 10 s per lemma) |
| Arith_Nat | `suc_pred` | `=> triEquals (\case \elim n, \elim n/=0 \with {  \| zero, n/=0 => contradiction  \| suc n, n/=0 => Arith.Int.IntRing.minus__})` | final run (current code, 10 s per lemma) |
| Arith_Nat | `-'0` | `\elim n   \| zero => idp   \| suc n => idp` | final run (current code, 10 s per lemma) |
| Arith_Nat | `-'+` | `\elim m   \| zero => Arith.Nat.-'0   \| suc m => -'+` | final run (current code, 10 s per lemma) |
| Arith_Nat | `-'id` | `=> Arith.Nat.-'=0 linarith` | final run (current code, 10 s per lemma) |
| Arith_Nat | `-'-'l` | `\elim a, b   \| zero, b => idp   \| suc a, zero => idp   \| suc a, suc b => -'-'l` | final run (current code, 10 s per lemma) |
| Arith_Nat | `-'_<` | `\elim n, m, p   \| zero, m, p => contradiction   \| suc n, zero, p => p   \| suc n, suc m, p => suc<suc (-'_< p)` | final run (current code, 10 s per lemma) |
| Arith_Nat | `<_-'` | `\elim n, m, p   \| zero, m, p => contradiction   \| suc n, zero, p => p   \| suc n, suc m, p => \case p \with {     \| suc<suc x => <_-' x   }` | final run (current code, 10 s per lemma) |
| Arith_Nat | `id<suc` | `\elim n   \| zero => zero<suc   \| suc n => suc<suc id<suc` | final run (current code, 10 s per lemma) |
| Arith_Nat | `id/=suc` | `\elim n   \| zero => \lam p => contradiction   \| suc n => \lam p => id/=suc {n} (pmap pred p)` | reruns after the printer fix for recursive calls under a lambda |
| Arith_Nat | `nonZero>0` | `\elim n, n/=0   \| zero, n/=0 => contradiction   \| suc n, n/=0 => zero<suc` | final run (current code, 10 s per lemma) |
| Arith_Nat | `fin_<` | `\elim n, x   \| zero, x => contradiction   \| suc n, zero => zero<suc   \| suc n, suc x => suc<suc (fin_< _)` | final run (current code, 10 s per lemma) |
| Arith_Nat | `toFin=id` | `\elim k, n, p   \| k, zero, p => contradiction   \| zero, suc n, p => idp   \| suc k, suc n, p => pmap suc toFin=id` | final run (current code, 10 s per lemma) |
| Arith_Nat | `toFin=fin` | `\elim n, k   \| zero, k => contradiction   \| suc n, zero => idp   \| suc n, suc k => pmap (\lam (z : Fin n) => suc z) toFin=fin` | final run (current code, 10 s per lemma) |
| Arith_Nat | `mod_Fin=mod` | `\elim n, p   \| zero, p => contradiction   \| suc n, p => idp` | final run (current code, 10 s per lemma) |
| Arith_Nat | `fin_nat-inj` | `\elim n, x, y, p   \| zero, x, y, p => contradiction   \| suc n, zero, zero, p => idp   \| suc n, zero, suc y, p => contradiction   \| suc n, suc x, zero, p => contradiction   \| suc n, suc x, suc y, p => rewrite (fin_nat-inj {n} {x} {y} (pmap pred p)) idp` | reruns after the printer fix for recursive calls under a lambda |
| Arith_Nat | `fin_nat-ineq` | `\elim n, x, y, p   \| zero, x, y, p => contradiction   \| suc n, zero, y, p => \lam p' => (\case \elim y, \elim p, \elim p' \with {     \| zero, p, p' => contradiction     \| suc y, p, p' => contradiction   })   \| suc n, suc x, zero, p => contradiction   \| suc n, suc x, suc y, p => \lam p' => (\case pmap pred p' \with {     \| q => p (Arith.Nat.fin_nat-inj p')   })` | reruns after the printer fix for recursive calls under a lambda |
| Arith_Nat | `zero<=_` | `=> linarith` | final run (current code, 10 s per lemma) |
| Arith_Nat | `suc<=suc` | `=> linarith` | final run (current code, 10 s per lemma) |
| Arith_Nat | `-'-'r_id` | `\elim n, k, k<=n   \| zero, k, k<=n => linarith   \| suc n, zero, k<=n => Arith.Nat.-'id   \| suc n, suc k, k<=n => -'_inv k<=n` | final run (current code, 10 s per lemma) |
| Arith_Nat | `<=_exists` | `\elim n, m, p   \| n, zero, p => linarith   \| zero, suc m, p => idp   \| suc n, suc m, p => rewrite (<=_exists {n} {m} linarith) idp` | final run (current code, 10 s per lemma) |
| Arith_Nat | `-'<=id` | `\elim n, m   \| zero, m => linarith   \| suc n, zero => linarith   \| suc n, suc m => -'<=id {n} {m} <=∘ linarith` | final run (current code, 10 s per lemma) |
| Arith_Nat | `-'_<=+` | `\elim n, m   \| zero, m => linarith   \| suc n, zero => linarith   \| suc n, suc m => Arith.Nat.suc<=suc -'_<=+` | final run (current code, 10 s per lemma) |
| Arith_Nat | `-'+-comm` | `\elim k   \| zero => idp   \| suc k => rewriteI (-'+-comm {_} {_} {k} p) (-'_suc linarith)` | final run (current code, 10 s per lemma) |
| Arith_Nat | `-'-monotone-left` | `\elim n, m, k, p   \| zero, m, k, p => linarith   \| suc n, zero, k, p => linarith   \| suc n, suc m, zero, p => p   \| suc n, suc m, suc k, p => -'-monotone-left linarith` | final run (current code, 10 s per lemma) |
| Arith_Nat | `-'-monotone-right` | `\elim n, m, k, p   \| n, m, zero, p => linarith   \| n, zero, suc k, p => Arith.Nat.-'<=id   \| zero, suc m, suc k, p => linarith   \| suc n, suc m, suc k, p => -'-monotone-right linarith` | final run (current code, 10 s per lemma) |
| Arith_Nat | `-'_<-monotone-left` | `\elim n, m, k, p, q   \| zero, m, k, p, q => Arith.Nat.<_-' q   \| suc n, zero, k, p, q => contradiction   \| suc n, suc m, zero, p, q => p   \| suc n, suc m, suc k, p, q => \case p \with {     \| suc<suc x => -'_<-monotone-left x (unsuc< q)   }` | final run (current code, 10 s per lemma) |
| Arith_Nat | `-'_<=` | `\elim n, m, p   \| zero, m, p => linarith   \| suc n, zero, p => contradiction   \| suc n, suc m, p => Arith.Nat.suc<=suc (-'_<= p)` | final run (current code, 10 s per lemma) |
| Arith_Nat | `-'=0` | `\elim n, m, p   \| zero, m, p => idp   \| suc n, zero, p => linarith   \| suc n, suc m, p => -'=0 linarith` | final run (current code, 10 s per lemma) |
| Arith_Nat | `suc_<_<=` | `\elim m, p   \| zero, p => contradiction   \| suc m, p => Arith.Nat.<_suc_<= linarith` | final run (current code, 10 s per lemma) |
| Arith_Nat | `<_suc_<=` | `\elim n, m, p   \| zero, m, p => linarith   \| suc n, zero, p => linarith   \| suc n, suc m, p => \case p \with {     \| suc<suc x => Arith.Nat.suc_<_<= x   }` | final run (current code, 10 s per lemma) |
| Arith_Nat | `suc_<=_<` | `=> linarith` | final run (current code, 10 s per lemma) |
| Arith_Nat | `<=_<_suc` | `=> linarith` | final run (current code, 10 s per lemma) |
| Arith_Nat | `id<=suc` | `=> linarith` | final run (current code, 10 s per lemma) |
| Arith_Nat | `mod<=left` | `=> transport (\lam z => n mod m <= {_} z) (divModProp n m) linarith` | final run (current code, 10 s per lemma) |
| Arith_Nat | `mod<right` | `=> Arith.Nat.-'_< (\case \elim m, \elim m/=0 \with {  \| zero, m/=0 => contradiction  \| suc m, m/=0 => Arith.Nat.<_-' (Arith.Nat.fin_< _)})` | final run (current code, 10 s per lemma) |
| Arith_Nat | `mod_<` | `=> rewrite (Arith.Nat.div_< n<m) idp *> {_} {_} {m * n div m + n mod m} {_} divModProp n m` | final run (current code, 10 s per lemma) |
| Arith_Nat | `toFin'=id` | `\elim n, p   \| zero, p => contradiction   \| suc n, p => Arith.Nat.mod_< p` | final run (current code, 10 s per lemma) |
| Arith_Nat | `mod_Fin_<` | `\elim n, p, q   \| zero, p, q => contradiction   \| suc n, p, q => Arith.Nat.mod_< q` | final run (current code, 10 s per lemma) |
| Arith_Nat | `mod_Fin=id` | `\elim n, k, p   \| zero, k, p => contradiction   \| suc n, k, p => Arith.Nat.fin_mod_id _` | final run (current code, 10 s per lemma) |
| Arith_Nat | `fin_mod_id` | `=> Data.Fin.nat_fin_= (Arith.Nat.mod_< (Arith.Nat.fin_< _))` | final run (current code, 10 s per lemma) |
| Arith_Nat | `natUnit` | `=> Arith.Nat.natAssociates-areEqual    (\new LDiv {  \| M => NatSemiring  \| val => m  \| elem => 1  \| inv => n  \| inv-right => rewriteI p *-comm}) Monoid.LDiv.ide-div` | final run (current code, 10 s per lemma) |
| Arith_Nat | `ldiv*div=id` | `=> rewrite (Arith.Nat.div_mod m\|n) idp *> {_} {_} {m * n div m + n mod m} {_} divModProp n m` | final run (current code, 10 s per lemma) |
| Arith_Nat | `id_mod` | `=> Arith.Nat.div_mod Monoid.LDiv.id-div` | final run (current code, 10 s per lemma) |
| Arith_Nat | `n*_+_mod_n` | `=> Arith.Nat.n*_+_mod_n=mod.nat *> Arith.Nat.mod_< r<n` | final run (current code, 10 s per lemma) |
| Arith_Nat | `n*_+_mod_n=mod` | `=> Data.Fin.nat_fin_= Arith.Nat.n*_+_mod_n=mod.nat` | final run (current code, 10 s per lemma) |
| Arith_Nat | `mod_+-left` | `=> Arith.Nat.mod_+-cong-right (Arith.Nat.fin_mod_id _)` | final run (current code, 10 s per lemma) |
| Arith_Nat | `mod_+-right` | `=> Arith.Nat.mod_+-cong-left (Arith.Nat.fin_mod_id _)` | final run (current code, 10 s per lemma) |
| Arith_Nat | `mod_*-left` | `\elim b   \| zero => idp   \| suc b => Arith.Nat.mod_+-right *> Arith.Nat.mod_+-cong-right mod_*-left` | final run (current code, 10 s per lemma) |
| Arith_Nat | `mod_suc` | `=> Arith.Nat.fin_nat-inj (rewrite (Arith.Nat.mod_< p) (inv (Arith.Nat.mod_< (suc<suc p))))` | final run (current code, 10 s per lemma) |
| Data_Bool | `not-isInv` | `\elim b   \| false => idp   \| true => idp` | final run (current code, 10 s per lemma) |
| Data_Bool | `true/=false` | `=> contradiction` | final run (current code, 10 s per lemma) |
| Data_Fin | `unfsuc` | `=> Set.Fin.FinSet.suc-isInj _ _ p` | final run (current code, 10 s per lemma) |
| Data_Fin | `fsuc/=` | `\elim n, x, y, p   \| zero, x, y, p => \lam p' => contradiction   \| suc n, x, y, p => \lam p' => p (Data.Fin.unfsuc p')` | final run (current code, 10 s per lemma) |
| Data_Fin | `fsuc/=0` | `=> contradiction` | final run (current code, 10 s per lemma) |
| Data_Fin | `fsuc/=-conv` | `\elim n, x, y, p   \| zero, x, y, p => \lam p' => contradiction   \| suc n, zero, zero, p => \lam p' => contradiction   \| suc n, zero, suc y, p => \lam p' => contradiction   \| suc n, suc x, y, p => \lam p' => p (rewrite p' idp)` | final run (current code, 10 s per lemma) |
| Data_Fin | `nat_fin_=` | `=> Arith.Nat.fin_nat-inj p` | final run (current code, 10 s per lemma) |
| Data_Fin | `fin_nat_/=` | `\elim n, x, y, p   \| zero, x, y, p => contradiction   \| suc n, x, y, p => \lam p' => p (Data.Fin.nat_fin_= p')` | final run (current code, 10 s per lemma) |
| Data_Fin | `fsuc_fpred` | `\elim x, p   \| zero, p => contradiction   \| suc x, p => idp` | final run (current code, 10 s per lemma) |
| Data_Fin | `fsuc_fpredP` | `\elim x, p   \| zero, p => contradiction   \| suc x, p => idp` | final run (current code, 10 s per lemma) |
| Data_List | `length_++` | `\elim l   \| nil => idp   \| :: x l => pmap suc length_++` | final run (current code, 10 s per lemma) |
| Data_List | `length_replicate` | `\elim n   \| zero => idp   \| suc n => pmap suc length_replicate` | final run (current code, 10 s per lemma) |
| Data_List | `all-map` | `\elim l, a   \| nil, a => all-nil   \| :: x l, a => \case a \with {     \| all-cons p x' => all-cons p (all-map _ x')   }` | final run (current code, 10 s per lemma) |
| Data_List | `all-implies` | `\elim l, a, p   \| nil, a, p => all-nil   \| :: x l, a, p => \case a \with {     \| all-cons p' x' => \case p \with {       \| all-cons p'' x'' => all-cons (p'' p') (all-implies x' x'')     }   }` | final run (current code, 10 s per lemma) |
| Data_List | `all-forall` | `\elim l   \| nil => all-nil   \| :: x l => all-cons (p _) (all-forall p)` | final run (current code, 10 s per lemma) |
| Data_List | `allC-tail` | `=> \case \elim l, \elim a \with {   \| nil, a => allC-nil   \| x :: l, a => \case a \with {     \| allC-cons p x' => x'   } }` | final run (current code, 10 s per lemma) |
| Data_List | `count_++` | `\elim l   \| nil => idp   \| :: x l => rewrite (count_++ {_} {l} {_} {_}) (\case \elim l' \with {  \| nil => idp  \| x' :: l' => mcases {1} () \with {  \| yes p => idp  \| no p => idp}})` | final run (current code, 10 s per lemma) |
| Data_List | `InList_++-left` | `\elim l, p   \| nil, p => contradiction   \| :: x l, p => InList.~_::.InList_:: InList_++-left p` | final run (current code, 10 s per lemma) |
| Data_List | `InList_++-right` | `\elim l   \| nil => p   \| :: x l => there (InList_++-right p)` | final run (current code, 10 s per lemma) |
| Logic | `/=-sym` | `=> contradiction` | final run (current code, 10 s per lemma) |
| Logic | `prop-isProp` | `=> \lam a => \lam a' => Logic.prop-pi` | final run (current code, 10 s per lemma) |
| Logic | `set-pi` | `=> Logic.prop-pi` | final run (current code, 10 s per lemma) |
| Logic | `<->_=` | `=> (\lam p => ext p, \lam p => rewrite p Logic.<->refl)` | final run (current code, 10 s per lemma) |
| Logic | `<->refl` | `=> (\lam p => p, \lam p => p)` | final run (current code, 10 s per lemma) |
| Logic | `<->trans` | `=> \case f \with {   \| (p, p') => \case g \with {     \| (p'', p''') => (\lam p'''' => p'' (p p''''), \lam p'''' => p' (p''' p''''))   } }` | final run (current code, 10 s per lemma) |
| Logic | `<->sym` | `=> \case f \with {   \| (p, p') => (p', p) }` | final run (current code, 10 s per lemma) |
| Logic | `TSetIm-elim` | `=> \case s \with {   \| inP (a, x) => rewriteI x (c _) }` | final run (current code, 10 s per lemma) |
| Logic | `SetIm-con` | `=> Logic.SetIm-cone _ Pa` | final run (current code, 10 s per lemma) |
| Logic | `SetIm-cone` | `=> Logic.SetIm-con Pa` | final run (current code, 10 s per lemma) |
| Logic | `SetIm-elim` | `=> \case s \with {   \| inP (a, x) => \case \elim a, \elim x \with {     \| (a, x'), x => rewriteI x (c x')   } }` | final run (current code, 10 s per lemma) |
| Logic | `SetIm_o` | `=> ext (\lam b => Logic.propExt (\lam p => (\case p \with {  \| inP (a, x) => rewriteI x (Logic.SetIm-con (unfold SetIm (Logic.TSetIm-con _)))}))   (\lam p => (\case p \with {  \| inP (a, x) => \case \elim a, \elim x \with {    \| (a, p'), x => \case p' \with {       \| inP (a', x') => unfold SetIm (rewriteI x (rewriteI x' (Logic.TSetIm-con _)))    }  }})))` | final run (current code, 10 s per lemma) |
| Logic | `SetIm_TSetIm` | `=> ext (\lam b => Logic.propExt (\lam p => (\case p \with {  \| inP (a, x) => \case \elim a, \elim x \with {    \| (a, p'), x => \case p' \with {       \| inP (a', x') => rewriteI x (rewriteI x' (Logic.TSetIm-con _))    }  }}))   (\lam p => (\case p \with {  \| inP (a, x) => rewriteI x (Logic.SetIm-con (Logic.TSetIm-con _))})))` | final run (current code, 10 s per lemma) |
| Logic | `propExt` | `=> ext (f, g)` | final run (current code, 10 s per lemma) |
| Order_Lattice_BottomDistributiveLattice | `bottom-ldistr` | `=> MeetSemilattice.meet-comm *> BottomDistributiveLattice.bottom-rdistr` | final run (current code, 10 s per lemma) |
| Order_Lattice_BottomDistributiveLattice | `bottom-rdistr` | `=> MeetSemilattice.meet_<= bottom-univ` | final run (current code, 10 s per lemma) |
| Order_Lattice_BottomJoinSemilattice | `bottom-right` | `=> JoinSemilattice.join-comm *> bottom-left` | final run (current code, 10 s per lemma) |
| Order_Lattice_BottomJoinSemilattice | `BigJoin-cond` | `=> JoinSemilattice.Big_<=_join1 _` | final run (current code, 10 s per lemma) |
| Order_Lattice_BottomJoinSemilattice | `BigJoin-univ` | `\elim l, p   \| nil, p => bottom-univ   \| :: a l, p => rewriteI BottomJoinSemilattice.FinJoin=BigJoin (BottomJoinSemilattice.FinJoin-univ p)` | final run (current code, 10 s per lemma) |
| Order_Lattice_BottomJoinSemilattice | `FinJoin=BigJoin` | `=> <=-antisymmetric (BottomJoinSemilattice.FinJoin-univ BottomJoinSemilattice.BigJoin-cond)    (BottomJoinSemilattice.BigJoin-univ (\lam j => BottomJoinSemilattice.FinJoin-cond _))` | final run (current code, 10 s per lemma) |
| Order_Lattice_BottomJoinSemilattice | `BigJoin_EPerm` | `=> AbMonoid.BigSum_EPerm {toMonoid A} {_} {_} e` | final run (current code, 10 s per lemma) |
| Order_Lattice_BottomJoinSemilattice | `BigJoin_++` | `=> AddMonoid.BigSum_++ {toMonoid A} {_} {_}` | final run (current code, 10 s per lemma) |
| Order_Lattice_BottomJoinSemilattice | `BigJoin_join` | `=> AbMonoid.BigSum_+ {toMonoid A} {_} {_} {_}` | final run (current code, 10 s per lemma) |
| Order_Lattice_DistributiveLattice | `meet-ldistr` | `=> <=-antisymmetric ldistr>= Lattice.ldistr<=` | final run (current code, 10 s per lemma) |
| Order_Lattice_DistributiveLattice | `meet-rdistr` | `=> MeetSemilattice.meet-comm *>  rewrite DistributiveLattice.meet-ldistr (rewrite MeetSemilattice.meet-comm (pmap ((∨) {A} (y ∧ {A} x)) MeetSemilattice.meet-comm))` | final run (current code, 10 s per lemma) |
| Order_Lattice_DistributiveLattice | `rdistr>=` | `=> rewriteI DistributiveLattice.meet-rdistr <=-refl` | final run (current code, 10 s per lemma) |
| Order_Lattice_JoinSemilattice | `Big_join-cond` | `=> JoinSemilattice.Big_<=_join _` | final run (current code, 10 s per lemma) |
| Order_Lattice_JoinSemilattice | `join-monotone` | `=> join-univ (p <=∘ join-left) (q <=∘ join-right)` | final run (current code, 10 s per lemma) |
| Order_Lattice_JoinSemilattice | `join-idemp` | `=> JoinSemilattice.join_<= <=-refl` | final run (current code, 10 s per lemma) |
| Order_Lattice_JoinSemilattice | `join-comm` | `=> <=-antisymmetric (join-univ join-right join-left) (join-univ join-right join-left)` | final run (current code, 10 s per lemma) |
| Order_Lattice_JoinSemilattice | `join_<=` | `=> <=-antisymmetric (join-univ x<=y <=-refl) join-right` | final run (current code, 10 s per lemma) |
| Order_Lattice_JoinSemilattice | `join_<='` | `=> rewriteI p join-left` | final run (current code, 10 s per lemma) |
| Order_Lattice_JoinSemilattice | `Big_<=_join0` | `\elim l   \| nil => <=-refl   \| :: a l => Big_<=_join0 {A} {l} {x} <=∘ join-right` | final run (current code, 10 s per lemma) |
| Order_Lattice_JoinSemilattice | `Big_<=_join1` | `\elim l, i   \| nil, i => contradiction   \| :: a l, zero => join-left   \| :: a l, suc i => Big_<=_join1 {A} {l} {x} i <=∘ join-right` | final run (current code, 10 s per lemma) |
| Order_Lattice_JoinSemilattice | `Big_<=_join` | `=> JoinSemilattice.Big_join-cond` | final run (current code, 10 s per lemma) |
| Order_Lattice_JoinSemilattice | `Big_join-univ` | `\elim l, f   \| nil, f => p   \| :: a l, f => join-univ (f zero) (Big_join-univ p (\lam i => f (suc i)))` | final run (current code, 10 s per lemma) |
| Order_Lattice_Lattice | `ldistr<=` | `=> join-univ (MeetSemilattice.meet-monotone <=-refl join-left) (MeetSemilattice.meet-monotone <=-refl join-right)` | final run (current code, 10 s per lemma) |
| Order_Lattice_MeetSemilattice | `Big_meet-cond` | `\elim j   \| zero => MeetSemilattice.Big_<=_meet0   \| suc j => MeetSemilattice.Big_<=_meet1 _` | final run (current code, 10 s per lemma) |
| Order_Lattice_MeetSemilattice | `meet-idemp` | `=> MeetSemilattice.meet_<= <=-refl` | final run (current code, 10 s per lemma) |
| Order_Lattice_MeetSemilattice | `meet-comm` | `=> <=-antisymmetric (meet-univ meet-right meet-left) (meet-univ meet-right meet-left)` | final run (current code, 10 s per lemma) |
| Order_Lattice_MeetSemilattice | `meet-monotone` | `=> meet-univ (meet-left <=∘ p) (meet-right <=∘ q)` | final run (current code, 10 s per lemma) |
| Order_Lattice_MeetSemilattice | `meet_<=` | `=> <=-antisymmetric meet-left (meet-univ <=-refl x<=y)` | final run (current code, 10 s per lemma) |
| Order_Lattice_MeetSemilattice | `meet_<='` | `=> rewriteI p meet-right` | final run (current code, 10 s per lemma) |
| Order_Lattice_MeetSemilattice | `Big_<=_meet0` | `\elim l   \| nil => <=-refl   \| :: a l => meet-right <=∘ Big_<=_meet0 {A} {l} {x}` | final run (current code, 10 s per lemma) |
| Order_Lattice_MeetSemilattice | `Big_<=_meet1` | `\elim l, i   \| nil, i => contradiction   \| :: a l, zero => meet-left   \| :: a l, suc i => meet-right <=∘ Big_<=_meet1 {A} {l} {x} i` | final run (current code, 10 s per lemma) |
| Order_Lattice_MeetSemilattice | `Big_meet-univ` | `\elim l, f   \| nil, f => p   \| :: a l, f => meet-univ (f zero) (Big_meet-univ p (\lam i => f (suc i)))` | final run (current code, 10 s per lemma) |
| Order_Lattice_TopMeetSemilattice | `top-right` | `=> equation` | final run (current code, 10 s per lemma) |
| Order_Lattice_TopMeetSemilattice | `BigMeet-cond` | `=> MeetSemilattice.Big_<=_meet1 _` | final run (current code, 10 s per lemma) |
| Order_Lattice_TopMeetSemilattice | `BigMeet-univ` | `=> MeetSemilattice.Big_meet-univ top-univ p` | final run (current code, 10 s per lemma) |
| Order_LinearOrder_TotalOrder | `meet-isMin` | `=> \case totality x y \with {   \| byLeft p => byLeft (meet_<= p)   \| byRight p' => byRight (meet-comm *> meet_<= p') }` | final run (current code, 10 s per lemma) |
| Order_LinearOrder_TotalOrder | `meet-prop` | `=> \case TotalOrder.meet-isMin x y \with {   \| byLeft p => rewriteI p in Px   \| byRight p' => rewriteI p' in Py }` | final run (current code, 10 s per lemma) |
| Order_LinearOrder_TotalOrder | `join-isMax` | `=> \case totality x y \with {   \| byLeft p => byRight (join_<= p)   \| byRight p' => byLeft (join-comm *> join_<= p') }` | final run (current code, 10 s per lemma) |
| Order_LinearOrder_TotalOrder | `join-prop` | `=> \case TotalOrder.join-isMax x y \with {   \| byLeft p => rewriteI p in Px   \| byRight p' => rewriteI p' in Py }` | final run (current code, 10 s per lemma) |
| Order_PartialOrder | `=_<=` | `=> rewrite p <=-refl` | final run (current code, 10 s per lemma) |
| Order_PartialOrder | `=<=` | `=> rewriteI p in q` | final run (current code, 10 s per lemma) |
| Order_StrictOrder_StrictPoset | `<_/=` | `=> contradiction` | final run (current code, 10 s per lemma) |
| Order_StrictOrder_StrictPoset | `>_/=` | `=> contradiction` | final run (current code, 10 s per lemma) |
| Set | `dec-separated` | `=> \case d \with {   \| yes p => p   \| no p' => contradiction }` | final run (current code, 10 s per lemma) |
| Set | `negated-dec` | `=> isNegated (\lam p => p (f (no (\lam p' => p (f (yes p'))))))` | final run (current code, 10 s per lemma) |
| Set | `dec_decide` | `=> \new Decide {   \| E => E   \| decide => d }` | final run (current code, 10 s per lemma) |
| Set | `dec_yes_reduce` | `=> prop-pi` | final run (current code, 10 s per lemma) |
| Set | `dec_no_reduce` | `=> prop-pi` | final run (current code, 10 s per lemma) |
| Set | `Dec_\|\|` | `=> \case d \with {   \| yes p => yes (byLeft p)   \| no p' => \case e \with {     \| yes p => yes (byRight p)     \| no p'' => no contradiction   } }` | final run (current code, 10 s per lemma) |
| Set | `NotDec` | `=> \case d \with {   \| yes p => no contradiction   \| no p' => yes p' }` | final run (current code, 10 s per lemma) |
| Set | `decideEq=_reduce` | `=> Set.dec_yes_reduce _` | final run (current code, 10 s per lemma) |
| Set | `decideEq/=_reduce` | `=> prop-pi` | final run (current code, 10 s per lemma) |
| Set | `=-dec` | `=> Set.==_= so` | final run (current code, 10 s per lemma) |
| Set_Set | `apartNotEqual` | `=> contradiction` | final run (current code, 10 s per lemma) |
