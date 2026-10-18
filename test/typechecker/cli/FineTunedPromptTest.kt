package typechecker.cli

import typechecker.cli.proofstep.CliLLMStepGenerator
import kotlin.test.Test
import kotlin.test.assertEquals

class FineTunedPromptTest {
    @Test
    fun `fine tuned prompt matches the Python training representation`() {
        val prompt = CliLLMStepGenerator.fineTunedArendPrompt(
            context = listOf("x : Nat", "p : x = 0"),
            premises = listOf("\\func inv {A : \\Type} (p : a = b) : b = a\n  => {?hidden_proof}"),
            expectedType = "0 = x"
        )

        assertEquals(
            "['x : Nat', 'p : x = 0'] ['\\\\func inv {A : \\\\Type} (p : a = b) : b = a\\n  => {?hidden_proof}'] 0 = x",
            prompt
        )
    }

    @Test
    fun `fine tuned prompt uses Python quote selection`() {
        val prompt = CliLLMStepGenerator.fineTunedArendPrompt(
            context = listOf("x's type"),
            premises = emptyList(),
            expectedType = "P x"
        )

        assertEquals("[\"x's type\"] [] P x", prompt)
    }
}
