package typechecker.coreapi.proofstep

import org.arend.ext.module.ModulePath
import org.arend.server.ArendChecker
import org.arend.server.ArendServer
import typechecker.Proof
import typechecker.ProofStep
import java.io.File
// LLM dependencies - commented out for build
// Uncomment later to use JetBrains/koog or other LLM backend
//import ai.koog.agents.core.agent.AIAgent
//import ai.koog.prompt.llm.LLModel
//import org.example.org.jetbrains.ai.kotlin.playbook.createLiteLLMModel
//import org.example.org.jetbrains.ai.kotlin.playbook.createLiteLLMPromptExecutor
//import org.jetbrains.ai.kotlin.playbook.LITELLM_API_KEY
//import org.jetbrains.ai.kotlin.playbook.LITELLM_URL
import extractStep
import typechecker.LLMClient
import typechecker.FallbackLLMClient
import org.json.JSONObject
import org.json.JSONArray
import kotlinx.coroutines.runBlocking
import org.arend.core.context.binding.Binding
import org.arend.core.context.binding.EvaluatingBinding
import org.arend.core.expr.ClassCallExpression
import org.arend.ext.concrete.definition.FunctionKind
import org.arend.ext.core.ops.NormalizationMode
import org.arend.ext.error.GeneralError
import org.arend.ext.error.ListErrorReporter
import org.arend.ext.prettyprinting.PrettyPrinterConfig
import org.arend.ext.reference.Precedence
import org.arend.frontend.parser.BuildVisitor
import org.arend.frontend.repl.CommonCliRepl
import org.arend.naming.reference.FullModuleReferable
import org.arend.naming.resolving.typing.AbstractBody
import org.arend.naming.resolving.typing.TypedReferable
import org.arend.naming.resolving.visitor.ExpressionResolveNameVisitor
import org.arend.term.concrete.Concrete
import org.arend.term.concrete.ConcreteExpressionFactory
import org.arend.term.concrete.SearchConcreteVisitor
import org.arend.term.prettyprint.ToAbstractVisitor
import org.arend.typechecking.visitor.CheckTypeVisitor
import org.arend.typechecking.visitor.DesugarVisitor
import org.arend.typechecking.visitor.SyntacticDesugarVisitor
import typechecker.coreapi.ArendGoal
import typechecker.coreapi.ArendProof

class LLMStepGenerator(
  checker: ArendChecker,
  server: ArendServer,
  libName: String,
  modulePath: ModulePath
): BaseStepGenerator(checker, server, libName, modulePath) {
  private val systemPrompt = "You are an assistant for writing in the proof assistant language Arend. Answer concisely. Metas are like tactics in Lean. Remember that you have the following tactics. Metas rewrite, rewriteI, and rewriteF work just like the rewriting mechanism in other languages, such as Coq or Idris (in Agda, rewrite is allowed only in the LHS of a clause, so it's different).\n" +
          "rewrite p t : T where p : a = b replaces occurrences of a in T with a variable obtaining a type T[x/a] and returns transportInv (\\lam x => T[x/a]) p t. Note that T is the expected type from the context, not the type of t. When the expected type is unknown, the type of t will be used instead of T.\n" +
          "rewriteF is like rewrite but it enforces to use the type of t instead of the expected type.\n" +
          "rewriteI p t is equivalent to rewrite (inv p) t.\n" +
          "To any of the metas above it is possible to add specification of numbers of occurrences. For example, rewrite {i1, i2, … ik} p t : T rewrites only occurrences with numbers i1, i2, … ik where occurrence ij is the number of occurrence after all previous occurrences have been replaced.\n" +
          "Examples \n" +
          "\\lemma +-assoc (a b c : Nat) : a + b + c = a + (b + c) \\elim c\n" +
          "  | 0 => idp\n" +
          "  | suc c => rewrite (+-assoc a b c) idp\n" +
          "\n" +
          "\\lemma +-comm-rw (a b : Nat) : a + b = b + a\n" +
          "  | 0, 0 => idp\n" +
          "  | 0, suc b => rewrite (+-comm-rw 0 b) idp\n" +
          "  | suc a, 0 => rewriteI (+-comm-rw a 0) idp\n" +
          "  | suc a, suc b => rewrite (+-comm-rw \$ suc a) \$\n" +
          "       rewriteI (+-comm-rw a b) \$ rewriteI (+-comm-rw a \$ suc b) idp\n" +
          "\n" +
          "\\lemma test1 (x y : Nat) (p : x = 0) (q : 0 = y) : x = y => rewrite p q\n" +
          "\n" +
          "\\lemma test2 (x y : Nat) (p : 0 = x) (q : 0 = y) : x = y => rewriteI p q\n" +
          "\n" +
          "\\lemma test3 (x y : Nat) (p : 0 = x) (q : 0 = y) : x = y => rewriteF p q\n" +
          "\n" +
          "\\lemma test5 (x y : Nat) (p : 0 = x) (q : 0 = y) => rewrite p q\n" +
          "\n" +
          "\\lemma test6 {A : \\Set} (x : A) (f : A -> A) (h : \\Pi (z : A) -> f z = z) : f (f x) = x\n" +
          "  => rewrite h (rewrite h idp)\n" +
          "\n" +
          "\\lemma test7 {A : Nat} (x y : A) (f : A -> A) : f (x + y) = f (y + x)\n" +
          "  => rewrite +-comm-rw idp\n" +
          "\n" +
          "\n" +
          "Meta ext proves goals of the form a = {A} a'. It expects (at most) one argument and the type of this argument is called 'subgoal'. The expected type is called 'goal'.\n" +
          "If the goal is f = {\\Pi (x_1 : A_1) … (x_n : A_n) -> B} g, then the subgoal is \\Pi(x_1 : A_1) … (x_n : A_n) -> f x_1 … x_n = g x_1 … x_n\n" +
          "If the goal is t = {\\Sigma (x_1 : A_1) … (x_n : A_n) (y_1 : B_1 x_1 … x_n) … (y_k :B_k x_1 … x_n) (z_1 : C_1) … (z_m : C_m)} s, where C_i : \\Prop and they can depend on x_j and y_l for all i, j, and l, then the subgoal is \\Sigma (p_1 : t.1 =s.1) … (p_n : t.n = s.n) D_1 … D_k, where D_j is equal to coe (\\lam i => B (p_1 @i) … (p_n @ i)) t.{k + j - 1} right = s.{k + j - 1}\n" +
          "If the goal is t = {R} s, where R is a record, then the subgoal is defined in the same way as for \\Sigma-types It is also possible to use the following syntax in this case: ext R { | f_1 => e_1 … | f_l => e_l }, which is equivalent to ext (e_1, … e_l)\n" +
          "If the goal is A = {\\Prop} B, then the subgoal is \\Sigma (A -> B) (B -> A)\n" +
          "If the goal is A = {\\Type} B, then the subgoal is Equiv {A} {B}\n" +
          "If the goal is x = {P} y, where P : \\Prop, then the argument for ext should be omitted.\n" +
          "Meta simplify simplifies the expected type.\n" +
          "\\func test1 {M : Monoid} (x : M) : x = x * ide\n" +
          "  => simplify\n" +
          "\n" +
          "\n" +
          "\\func test6 {R : Ring} (x : R) : negative (x * x) = x * negative x\n" +
          "  => simplify\n" +
          "\n" +
          "Meta equation\n" +
          "equation a_1 … a_n proves an equation a_0 = a_{n+1} using a_1, … a_n as intermediate steps. A proof of a_i = a_{i+1} can be specified as implicit arguments between them.using, usingOnly, and hiding with a single argument can be used instead of a proof to control the context. The first implicit argument can be either a universe or a subclass of either Monoid, AddMonoid, or Order.Lattice.Bounded.MeetSemilattice. In the former case, the meta will prove an equality in a type without using any additional structure on it. In the latter case, the meta will prove an equality using only structure available in the specified class.\n" +
          "The general principle of the equation meta in Arend is consistent across algebraic structures: the solver first checks if the Left Hand Side and Right Hand Side are syntactically identical. If not, it converts both sides into a canonical normal form. If the normal forms are identical, the proof is complete; otherwise, it produces a subgoal requiring a proof that the two normal forms are equal. You can use equation in p to transform a complex proof p into a simpler proof of these normal forms. However, the operational logic and how hypotheses are applied differ based on the structure's properties. For rigid structures like Monoids, the solver acts like a text editor: hypotheses perform direct substitutions based on exact pattern matching. An integer argument before a hypothesis (e.g., 2 p) specifies the exact position of the occurrence to replace. For Commutative Monoids, order matters less, so integer arguments specify the count of occurrences to replace. For structures with inverses, like Groups and Rings, the solver acts like a calculator. Instead of text substitution, hypotheses are applied arithmetically to cancel out terms. Here, integer arguments represent coefficients or exponents; for example, 2 p in a Group raises the hypothesis to the second power, while in a Ring it multiplies the equation by 2. Negative integers are allowed here to represent inverses or subtraction. Boolean Rings use a specific logic of ideal reduction. Thus, while the user interface is universal, the underlying engine shifts from structural replacement in monoids to arithmetic manipulation in groups and rings. You have \n" +
          "Equation.monoid, equation.addMonoid, equation.cMonoid, equation.abMonoid, equation.cMonoidAuto, equation.group, equation.addGroup, equation.cGroup, equation.abGroup,equation.semiring, equation.cSemiring, equation.ring, equation.cRing, equation.cRingAuto, equation.bRing\n" +
          "\n" +
          "Meta linarith\n" +
          "This meta solves systems of linear equations in ordered rings using Fourier–Motzkin elimination.\n" +
          "\n" +
          "Forms of case expressions:\n" +
          "Basic form: \\case e_1, ... e_n \\with {\n" +
          "  | p_1^1, ... p_n^1 => d_1\n" +
          "  ...\n" +
          "  | p_1^k, ... p_n^k => d_k\n" +
          "}\n" +
          "If one of the expressions e_1, … e_n is a variable, keyword \\elim can be specified before it. " +
          "This variable will be evaluated from the context in the clauses. More importantly, it will be " +
          "substituted in the types of other arguments and the result type of the case expression. Thus, the" +
          " following two snippets are equivalent if e : E and the result type of the case expression is A." +
          "\\case \\elim x, e \\with {\n" +
          "  | pat, pat' => result\n" +
          "}" +
          "\\case x \\as x, e : E \\return A \\with {\n" +
          "  | pat, pat' => result\n" +
          "}"

  private val liteLLMModelId: String = "openai/gpt-4o"
  // LLM dependencies - commented out for build
  // Uncomment later to use JetBrains/koog or other LLM backend
  //private val executor = createLiteLLMPromptExecutor(LITELLM_URL, LITELLM_API_KEY)
  //private val llmModel: LLModel = createLiteLLMModel(liteLLMModelId)
  private val preprompt: String
  private val llmClient: LLMClient = FallbackLLMClient()

  init {
    val examples = parseConcatenatedJson(File("src/examples.json"))
    val examplesPrompt = examples.fold("") { acc, map ->
      acc + "\n" +
              "context: ${map["Context"]}\nexpected type: ${map["Expected type"]}"+
              "\n" + "CORRECT COMPLETION EXPRESSION is: ${map["Expression"]}"}
    val examplePremises = HashSet<String>()
    examples.forEach { examplePremises.addAll((it["Premises"] as List<String>).map { "$it\n" }) }
    examplePremises.removeIf { it.contains("fin-last-or") }
    println(examplePremises)
    preprompt = "I am going to give you a snippet of code in the formal verification language Arend. " +
            "You have to guess the completion of just one step (definition or tactic application). Use {?} " +
            "for arguments where a nontrivial proof is expected (but not where a non-proof term is expected). " +
            "First, output a short plan describing your reasoning for proving the goal. " +
            "Then, suggest the first step. Wrap the term in [TERM] and [/TERM] tags. " +
            "For example:\nPlan: We need to case split on i, then handle each case separately.\n[TERM]\\case \\elim i \\with { | zero => {?} | suc i' => {?} }[/TERM]\n" +
            "Dont create nested cases with the same variable like in the example \\case \\elim i \\with { | zero => \\case \\elim i ...}" +
            "Never use \\case i for individual variables!! Use \\case \\elim i instead!!\n" +
            "Dont wrap your output in anything like ```arend etc. " +
            "Now, I am going to give you examples of such successful completions." +
            "Premises: \n$examplePremises\n" +
            "Examples:\n$examplesPrompt\n"
  }

  companion object {
    fun extractTermFromResponse(response: String): String? {
      val startTag = "[TERM]"
      val endTag = "[/TERM]"
      val startIndex = response.indexOf(startTag)
      if (startIndex == -1) return null
      val termStart = startIndex + startTag.length
      val endIndex = response.indexOf(endTag, termStart)
      if (endIndex == -1) return null
      return response.substring(termStart, endIndex).trim()
    }

    fun parseConcatenatedJson(file: File): List<Map<String, Any?>> {
      val text = file.readText()
      val results = mutableListOf<Map<String, Any?>>()
      var index = 0
      while (index < text.length) {
        val start = text.indexOf('{', index)
        if (start == -1) break

        var braceCount = 0
        var inString = false
        var escape = false
        var end = -1

        for (i in start until text.length) {
          val char = text[i]
          if (escape) {
            escape = false
            continue
          }
          if (char == '\\') {
            escape = true
            continue
          }
          if (char == '\"') {
            inString = !inString
            continue
          }
          if (!inString) {
            if (char == '{') braceCount++
            if (char == '}') {
              braceCount--
              if (braceCount == 0) {
                end = i
                break
              }
            }
          }
        }

        if (end != -1) {
          val jsonString = text.substring(start, end + 1)
          val jsonObject = JSONObject(jsonString)
          results.add(jsonObject.toMapValue())
          index = end + 1
        } else {
          break
        }
      }
      return results
    }

    fun JSONObject.toMapValue(): Map<String, Any?> {
      val map = mutableMapOf<String, Any?>()
      val keys = this.keys()
      while (keys.hasNext()) {
        val key = keys.next()
        map[key] = this.get(key).toAnyValue()
      }
      return map
    }

    fun Any.toAnyValue(): Any? {
      return when (this) {
        is JSONObject -> this.toMapValue()
        is JSONArray -> {
          val list = mutableListOf<Any?>()
          for (i in 0 until this.length()) {
            list.add(this.get(i).toAnyValue())
          }
          list
        }
        null -> null
        is Boolean -> this
        is Number -> this
        is String -> this
        else -> this.toString()
      }
    }

  }

  fun printContext(context: Set<Binding>): String {
    return context.joinToString("\n") {
      val type = it.type.normalize(NormalizationMode.RNF).toString()
      val bind =
        if (it.type is ClassCallExpression) it.name + " : " + type.substringBefore("{") else it.name + " : " + type
      if (it is EvaluatingBinding) bind + " => " + it.expression else bind
    }
  }

  private fun collectParentCaseVariables(expr: Concrete.Expression): List<String> {
    val result = mutableListOf<String>()
    val visitor = object : SearchConcreteVisitor<Void?, Boolean>() {
      override fun visitGoal(expr: Concrete.GoalExpression, params: Void?): Boolean = true

      override fun visitCase(expr: Concrete.CaseExpression, params: Void?): Boolean {
        var goalInClauses = false
        for (clause in expr.clauses) {
          val body = clause.expression
          if (body != null && body.accept(this, null) == true) {
            goalInClauses = true
          }
        }
        if (goalInClauses) {
          for (arg in expr.arguments) {
            result.add(arg.expression.toString())
          }
        }
        return goalInClauses
      }
    }
    expr.accept(visitor, null)
    return result
  }

  private fun containsForbiddenCase(expr: Concrete.Expression, forbiddenVars: Set<String>): Boolean {
    if (forbiddenVars.isEmpty()) return false
    val visitor = object : SearchConcreteVisitor<Void?, Boolean>() {
      override fun visitCase(expr: Concrete.CaseExpression, params: Void?): Boolean {
        for (arg in expr.arguments) {
          if (arg.expression.toString() in forbiddenVars) return true
        }
        for (clause in expr.clauses) {
          val body = clause.expression
          if (body != null && body.accept(this, null) == true) return true
        }
        return false
      }
    }
    return expr.accept(visitor, null) == true
  }

  private fun getCurrentProofExpr(currentProof: Proof<ArendGoal>?): Concrete.Expression {
    return (currentProof as? ArendProof)?.getProof() ?: ConcreteExpressionFactory.cGoal("", null)
  }

  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val moduleLocation = getModuleLocation() ?: return emptyList()
    val factory = goal.typechecker.factory

    val currentProofExpr = getCurrentProofExpr(currentProof)
    val context = printContext(HashSet(goal.typechecker.context.values))
    val parentCaseVars = collectParentCaseVariables(currentProofExpr)
    val parentCasesInfo = if (parentCaseVars.isNotEmpty()) {
      "\nIMPORTANT: The following variables have already been cased on in parent expressions: ${parentCaseVars.joinToString(", ")}. " +
              "Do NOT create a \\case expression on any of these variables again. Use a different approach or different variables."
    } else ""
    var currentPrompt = preprompt + "provide CORRECT COMPLETION EXPRESSION for \n"+ "context: ${context}\nexpected type: ${goal.expectedType}\n" +
    //        "current definition: \\lemma fin-last-or {k : Nat} (i : Fin (suc k)) : (i NatOrder.< k) || (i = finLast k)\n" +
            "current proof: ${currentProofExpr}\n" + parentCasesInfo +
            "\nReminder: you can use {?} for subexpressions (but not for the whole expression). Dont try to solve everything at once."

    println("Expected type: " + goal.expectedType)
    println("Context: $context")
    repeat(50) { attempt ->
      println("Attempt ${attempt + 1}")
      // LLM dependencies - commented out for build
      // Uncomment later to use JetBrains/koog or other LLM backend
      //val agent = AIAgent(
      //  executor = executor,
      //  systemPrompt = systemPrompt,
      //  llmModel = llmModel,
      //  temperature = 0.7,
      //)
      //val response = runBlocking { agent.run(currentPrompt) }
      val response = runBlocking { llmClient.generateResponse(systemPrompt, currentPrompt) }
      println("The response:\n${response.chunked(120).joinToString("\n")}")
      val term = extractTermFromResponse(response)
      if (term == null) {
        println("Could not extract term from response")
        currentPrompt += "\n\nYour previous response did not contain a term wrapped in [TERM]...[/TERM] tags. Please provide your answer with the term wrapped in [TERM] and [/TERM] tags."
        return@repeat
      }
      println("Extracted term: $term")

      val errorReporter = ListErrorReporter()
      var step: Concrete.Expression? = null
      try {
        val parser = CommonCliRepl.createParser(term!!, moduleLocation, errorReporter)
        val visitor = BuildVisitor(moduleLocation, errorReporter)
        val exprContext = parser.expr()
        var concreteExpr: Concrete.Expression? = visitor.visitExpr(exprContext)
        val contextSave = goal.typechecker.saveTypecheckingContext()

        // if (term.startsWith("fin-last-or")) errorReporter.report(GeneralError(GeneralError.Level.ERROR, "Termination check failed."))

        if (concreteExpr != null && !errorReporter.errorList.any { it.level == GeneralError.Level.ERROR }) {
          val scope = getScope()
          if (scope != null) {
            val typedReferables = contextSave.localContext().keys.map { TypedReferable(it, AbstractBody(0, it, 0)) }
            val resolveVisitor = ExpressionResolveNameVisitor(scope, typedReferables, server.typingInfo, errorReporter, null, null)
            concreteExpr = concreteExpr!!.accept(resolveVisitor, null)
            if (concreteExpr != null) {
              concreteExpr = SyntacticDesugarVisitor.desugar(concreteExpr, errorReporter)
              concreteExpr = DesugarVisitor.desugar(concreteExpr, errorReporter)
            }
          }
        }

        if (concreteExpr != null && !errorReporter.errorList.any { it.level == GeneralError.Level.ERROR }) {
          if (containsForbiddenCase(concreteExpr!!, parentCaseVars.toSet())) {
            errorReporter.report(GeneralError(GeneralError.Level.ERROR, "Expression contains a nested \\case on an already-cased variable: ${parentCaseVars.joinToString(", ")}"))
          }
        }

        if (concreteExpr != null && !errorReporter.errorList.any { it.level == GeneralError.Level.ERROR }) {
          step = extractStep(concreteExpr) as? Concrete.Expression

          val branchTC = CheckTypeVisitor.loadTypecheckingContext(contextSave, errorReporter)
          val typecheckingResult = step?.let { branchTC.typecheck(step, goal.expectedType) }

          if (term != step.toString()) {
            currentPrompt += "\n\nYour guess ${term} has been simplified to ${step}."
          }
          if (typecheckingResult != null && !branchTC.status.hasErrors()) {
            println("typechecked successfully!")

            val moduleRef = FullModuleReferable(moduleLocation)
            val functionRef = factory.global(moduleRef, "llm_goal_" + term.hashCode().xor(goal.expectedType.toString().hashCode()), Precedence.DEFAULT, null, null)
            val concreteParameters = branchTC.context.map {
              val typeExpr = ToAbstractVisitor.convert(it.value.typeExpr, PrettyPrinterConfig.DEFAULT)
              Concrete.TelescopeParameter(it.value, true, listOf(it.key), typeExpr, false)
            }

            val proofDef = factory.function(
              functionRef,
              FunctionKind.FUNC,
              concreteParameters,
              ToAbstractVisitor.convert(goal.expectedType, PrettyPrinterConfig.DEFAULT),
              null,
              factory.body(step!!)
            ) as Concrete.FunctionDefinition

            val arendProof = ArendProof(proofDef, ArendGoal(goal.expectedType, branchTC, goal.sourceNode))
            return listOf(ProofStep(arendProof, 1.0))
          }
        }
      } catch (e: Exception) {
        errorReporter.report(GeneralError(GeneralError.Level.ERROR, e.message ?: e.toString()))
      }

      val errors = errorReporter.errorList.filter { it.level == GeneralError.Level.ERROR }
      if (errors.isNotEmpty()) {
        val errorMsg = errors.joinToString("\n") { it.toString() }
        println("Errors: $errorMsg")

        currentPrompt += "\n\nPrevious (simplified) guess: $step\nResulted in errors:\n$errorMsg\nPlease provide a CORRECT COMPLETION EXPRESSION wrapped in [TERM]...[/TERM] tags." + "Reminder: you can use {?} for subexpressions (but not for the whole expression), " +
                "for example for clauses in \\case. Dont try to solve everything at once."
      }
    }

    return emptyList()
  }

}
