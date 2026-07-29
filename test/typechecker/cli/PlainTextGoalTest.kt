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

    @Test
    fun `goals with same content but different ids are equal`() {
        val bindings = listOf(ContextBinding("n", "Nat"))
        val g1 = PlainTextGoal("1", "n = n", bindings, "M:D")
        val g2 = PlainTextGoal("3", "n = n", bindings, "M:D")
        assertEquals(g1, g2)
        assertEquals(g1.hashCode(), g2.hashCode())
    }

    @Test
    fun `goals differ by expected type`() {
        val g1 = PlainTextGoal("0", "n = n", emptyList(), "M:D")
        val g2 = PlainTextGoal("0", "n = m", emptyList(), "M:D")
        assertNotEquals(g1, g2)
    }

    @Test
    fun `goals differ by context bindings`() {
        val g1 = PlainTextGoal("0", "n = n", listOf(ContextBinding("n", "Nat")), "M:D")
        val g2 = PlainTextGoal("0", "n = n", listOf(ContextBinding("n", "Bool")), "M:D")
        val g3 = PlainTextGoal("0", "n = n", emptyList(), "M:D")
        assertNotEquals(g1, g2)
        assertNotEquals(g1, g3)
    }

    @Test
    fun `goals differ by moduleDef`() {
        val g1 = PlainTextGoal("0", "Nat", emptyList(), "M:D")
        val g2 = PlainTextGoal("0", "Nat", emptyList(), "M:E")
        assertNotEquals(g1, g2)
    }

    @Test
    fun `goal usable as map key across branches`() {
        // The same subgoal arising in two branches (different positional ids)
        // must hit the same map entry.
        val fromBranch1 = PlainTextGoal("1", "k = 1", listOf(ContextBinding("k", "Nat")), "M:D")
        val fromBranch2 = PlainTextGoal("2", "k = 1", listOf(ContextBinding("k", "Nat")), "M:D")
        val stepsByGoal = mutableMapOf<PlainTextGoal, String>()
        stepsByGoal[fromBranch1] = "[APPLY natUnit]"
        assertEquals("[APPLY natUnit]", stepsByGoal[fromBranch2])
    }
}
