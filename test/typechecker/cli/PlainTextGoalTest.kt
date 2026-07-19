package typechecker.cli

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotEquals
import kotlin.test.assertTrue

class PlainTextGoalTest {

    @Test
    fun `toString includes id and expected type`() {
        val goal = PlainTextGoal("2", "a + b = b + a", emptyList(), "M:D")
        val str = goal.toString()
        assertTrue(str.contains("2"))
        assertTrue(str.contains("a + b = b + a"))
    }

    @Test
    fun `toString includes context bindings when present`() {
        val bindings = listOf(
            ContextBinding("x", "Nat"),
            ContextBinding("y", "Nat")
        )
        val goal = PlainTextGoal("0", "x = y", bindings, "M:D")
        val str = goal.toString()
        assertTrue(str.contains("x : Nat"))
        assertTrue(str.contains("y : Nat"))
    }

    @Test
    fun `toString omits context section when no bindings`() {
        val goal = PlainTextGoal("0", "Nat", emptyList(), "M:D")
        val str = goal.toString()
        assertTrue(!str.contains("|"))
    }

    @Test
    fun `fields are accessible`() {
        val bindings = listOf(ContextBinding("a", "Nat"))
        val goal = PlainTextGoal("5", "Bool", bindings, "TestMod:myFunc")
        assertEquals("5", goal.id)
        assertEquals("Bool", goal.expectedType)
        assertEquals(bindings, goal.contextBindings)
        assertEquals("TestMod:myFunc", goal.moduleDef)
    }
}
