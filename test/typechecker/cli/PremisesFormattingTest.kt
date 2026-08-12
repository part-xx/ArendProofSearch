package typechecker.cli

import typechecker.cli.proofstep.CliLLMStepGenerator
import kotlin.test.Test
import kotlin.test.assertFalse
import kotlin.test.assertTrue

/**
 * Class/record premises must not be shown to the model as classes: only their fields
 * are listed, each tagged with the classes it can be accessed on.
 */
class PremisesFormattingTest {

    private val premises = listOf(
        """\func inv {A : \Type} {a a' : A} (p : a = a') : a' = a""",
        """\record DivBase {M : Monoid} (\coerce val : M) (elem inv : M)""",
        """\record LDiv \extends DivBase
                        | inv-right : val * inv = elem """,
        """\record RInv \extends LDiv
                        | elem => ide""",
        """\class Irr {M : CMonoid} (\coerce e : M) (notInv : Not (Inv e))
                        | isIrr {x y : M} : e = x * y -> Inv x || Inv y"""
    )

    private fun premisesBlock(): String {
        val cli = FakeCli()
        val generator = CliLLMStepGenerator(cli, "M:D", premises, llmClient = ScriptedLLMClient(emptyList()))
        val preprompt = CliLLMStepGenerator::class.java.getDeclaredField("preprompt")
            .apply { isAccessible = true }.get(generator) as String
        return preprompt
    }

    @Test
    fun classesAreReplacedByTheirFields() {
        val block = premisesBlock()
        println(block)

        assertFalse(block.contains("\\record DivBase"), "class premises must not be printed")
        assertFalse(block.contains("\\class Irr"), "class premises must not be printed")
        assertTrue(block.contains("\\func inv {A"), "non-class premises are printed as before")

        // Header fields, including inherited ones, tagged with every owning class.
        assertTrue(block.contains("val : M  [field of DivBase, LDiv, RInv]"), block)
        assertTrue(block.contains("elem : M  [field of DivBase, LDiv, RInv]"), block)
        assertTrue(block.contains("inv : M  [field of DivBase, LDiv, RInv]"), block)
        // Bar-clause field of LDiv, inherited by RInv.
        assertTrue(block.contains("inv-right : val * inv = elem  [field of LDiv, RInv]"), block)
        // Field implementations (| elem => ide) declare nothing new.
        assertFalse(block.contains("elem => ide"), block)
        assertTrue(block.contains("isIrr {x y : M} : e = x * y -> Inv x || Inv y  [field of Irr]"), block)
    }
}
