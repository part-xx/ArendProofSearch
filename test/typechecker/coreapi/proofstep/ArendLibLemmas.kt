package typechecker.coreapi.proofstep

/**
 * Lemmas of arend-lib whose proofs only apply definitions, rewrite and split cases, restated in
 * `test-lib-std/src/Lib*.ard` with their proofs removed (the comments there give the originals).
 */
object ArendLibLemmas {
  class Lemma(
    /** The restated lemma in test-lib-std. */
    val name: String,
    /** The name of the original in arend-lib, without its namespace. */
    val original: String,
    val module: String,
    /** Where the original is in arend-lib. */
    val source: String,
    /** The global names the original proof applies or rewrites with. */
    val premises: List<String>,
    /** The decision functions the original proof splits on. */
    val splitters: List<String> = emptyList(),
  ) {
    /** The module of the original, e.g. `Order.Lattice` for `Order/Lattice.ard:51`. */
    val sourceModule: String = source.substringBefore(".ard").replace('/', '.')

    /** Whether [candidate] is the original itself, which must not be used to prove its restatement. */
    fun isOriginal(candidate: PremiseCandidate): Boolean =
      candidate.module == sourceModule && (candidate.name == original || candidate.name.endsWith(".$original"))
  }

  val all = listOf(
    // Logic, Set, Bool, Paths
    Lemma("set-pi'", "set-pi", "LibLogic", "Logic.ard:64", listOf("prop-pi")),
    Lemma("dec_yes_reduce'", "dec_yes_reduce", "LibLogic", "Set.ard:39", listOf("prop-pi")),
    Lemma("decideEq=_reduce'", "decideEq=_reduce", "LibLogic", "Set.ard:152", listOf("prop-pi")),
    Lemma("=-dec'", "=-dec", "LibLogic", "Set.ard:164", listOf("==_=")),
    Lemma("propExt-conv'", "conv", "LibLogic", "Logic.ard:169", listOf("propExt.dir", "inv")),
    Lemma("not-isInv'", "not-isInv", "LibLogic", "Data/Bool.ard:22", listOf()),
    Lemma("So-fromSo'", "fromSo", "LibLogic", "Data/Bool.ard:11", listOf()),
    Lemma("or-toOr'", "toOr", "LibLogic", "Data/Bool.ard:46", listOf("byLeft", "byRight")),
    Lemma("or-fromOr'", "fromOr", "LibLogic", "Data/Bool.ard:50", listOf()),
    Lemma("TruncP-remove''", "remove'", "LibLogic", "Logic.ard:30", listOf()),
    Lemma("OR-fromOr'", "fromOr", "LibLogic", "Logic.ard:99", listOf("byLeft", "byRight")),
    Lemma("OR-toOr'", "toOr", "LibLogic", "Logic.ard:103", listOf("inP", "inl", "inr")),
    Lemma("OR-flip'", "flip", "LibLogic", "Logic.ard:107", listOf("byLeft", "byRight")),
    Lemma("sym'", "sym", "LibLogic", "Paths.ard:20", listOf("inv")),
    // Nat
    Lemma("<=_<_suc'", "<=_<_suc", "LibNat", "Arith/Nat.ard:371", listOf("suc_<=_<", "suc<=suc")),
    Lemma("unsuc<'", "unsuc<", "LibNat", "Arith/Nat.ard:59", listOf()),
    Lemma("-'0'", "-'0", "LibNat", "Arith/Nat.ard:35", listOf()),
    Lemma("suc<=suc'", "suc<=suc", "LibNat", "Arith/Nat.ard:250", listOf("<=-less", "suc<suc", "<=-refl"), splitters = listOf("<=-dec")),
    Lemma("NatBSemilattice-ldistr0'", "ldistr0", "LibNat", "Arith/Nat.ard:240", listOf()),
    // Int
    Lemma("ipred_isuc'", "ipred_isuc", "LibInt", "Arith/Int.ard:30", listOf()),
    Lemma("zro-id=neg'", "zro-id=neg", "LibInt", "Arith/Int.ard:410", listOf()),
    Lemma("id<isuc'", "id<isuc", "LibInt", "Arith/Int.ard:382", listOf("pos<pos", "neg<neg", "id<suc")),
    // Lattices and orders
    Lemma("meet-idemp'", "meet-idemp", "LibOrder", "Order/Lattice.ard:51", listOf("<=-antisymmetric", "meet-left", "meet-univ", "<=-refl")),
    Lemma("meet-comm'", "meet-comm", "LibOrder", "Order/Lattice.ard:54", listOf("<=-antisymmetric", "meet-univ", "meet-right", "meet-left")),
    Lemma("meet_<='", "meet_<=", "LibOrder", "Order/Lattice.ard:65", listOf("<=-antisymmetric", "meet-left", "meet-univ", "<=-refl")),
    Lemma("join-comm'", "join-comm", "LibOrder", "Order/Lattice.ard:118", listOf("<=-antisymmetric", "join-univ", "join-right", "join-left")),
    Lemma("join_<='", "join_<=", "LibOrder", "Order/Lattice.ard:128", listOf("<=-antisymmetric", "join-univ", "<=-refl", "join-right")),
    Lemma("top-right'", "top-right", "LibOrder", "Order/Lattice.ard:206", listOf("<=-antisymmetric", "meet-left", "meet-univ", "<=-refl", "top-univ")),
    Lemma("=_<='", "=_<=", "LibOrder", "Order/PartialOrder.ard:65", listOf("<=-refl")),
    Lemma("LinearOrder-dec<'", "dec<", "LibOrder", "Order/LinearOrder.ard:273", listOf("yes", "no"), splitters = listOf("LinearOrder.dec<_<=")),
    Lemma("TotalOrder-meet-isMin'", "meet-isMin", "LibOrder", "Order/LinearOrder.ard:38", listOf("byLeft", "byRight", "<=-antisymmetric", "meet-left", "meet-univ", "meet-right", "<=-refl"), splitters = listOf("TotalOrder.totality")),
    // Algebra
    Lemma("AddGroup-toZero'", "toZero", "LibAlgebra", "Algebra/Group.ard:234", listOf("negative-right")),
    Lemma("CMonoid-pow_*-comm'", "pow_*-comm", "LibAlgebra", "Algebra/Monoid.ard:482", listOf("Monoid.pow-comm", "*-comm")),
    Lemma("LatticeAbGroup-abs>=id'", "abs>=id", "LibAlgebra", "Algebra/Ordered.ard:138", listOf("join-left")),
  )
}
