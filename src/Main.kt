import org.apache.commons.cli.CommandLine
import org.apache.commons.cli.DefaultParser
import org.apache.commons.cli.Option
import org.apache.commons.cli.Options
import org.apache.commons.cli.ParseException
import org.arend.error.DummyErrorReporter
import org.arend.ext.error.ListErrorReporter
import org.arend.ext.module.FullName
import org.arend.ext.module.ModuleLocation
import org.arend.frontend.library.CliServerRequester
import org.arend.frontend.library.FileSourceLibrary
import org.arend.frontend.library.LibraryManager
import org.arend.frontend.library.SourceLibrary
import org.arend.frontend.source.PreludeResourceSource
import org.arend.prelude.Prelude
import org.arend.server.ArendServer
import org.arend.server.ProgressReporter
import org.arend.server.impl.ArendServerImpl
import org.arend.term.concrete.Concrete
import org.arend.term.concrete.Concrete.ResolvableDefinition
import org.arend.term.group.ConcreteGroup
import org.arend.typechecking.computation.UnstoppableCancellationIndicator
import org.arend.core.expr.Expression
import org.arend.ext.ArendExtension
import org.arend.ext.error.ErrorReporter
import org.arend.server.ArendServerResolveListener
import org.arend.typechecking.instance.pool.GlobalInstancePool
import org.arend.typechecking.result.TypecheckingResult
import org.arend.typechecking.visitor.ArendCheckerFactory
import org.arend.typechecking.visitor.CheckTypeVisitor
import org.arend.util.FileUtils
import org.arend.util.FileUtils.modulePath
import search.best_first.BestFirstSearch
import typechecker.impl.ArendGoal
import typechecker.impl.ArendProof
import typechecker.impl.proofstep.HeuristicStepGenerator
import typechecker.impl.proofstep.LLMStepGenerator
import java.nio.file.Path
import java.nio.file.Paths
import java.util.Objects
import java.util.function.Supplier
import kotlin.system.exitProcess

private fun parseArgs(args: Array<String>): CommandLine? {
  try {
    val cmdOptions = Options()
    cmdOptions.addOption(
      Option.builder("L").longOpt("libdir").hasArg().argName("dir").desc("directory containing libraries").build()
    )

    return DefaultParser().parse(cmdOptions, args)
  } catch (e: ParseException) {
    System.err.println(e.message)
    return null
  }
}

fun main(args: Array<String>) {
  try {
    val cmdLine: CommandLine = parseArgs(args) ?: throw IllegalArgumentException("Missing required argument: -L <libdir>")
    val libDir: Path = Paths.get(cmdLine.getOptionValues("L")[0])
    val testFilename = "testPS"

    val errorReporter = ListErrorReporter()
    val libraryManager = LibraryManager(errorReporter)
    val server: ArendServer = ArendServerImpl(CliServerRequester(libraryManager), false, false, true)
    server.addReadOnlyModule(
      Prelude.MODULE_LOCATION,
      Supplier { Objects.requireNonNull<ConcreteGroup?>(PreludeResourceSource().loadGroup(DummyErrorReporter.INSTANCE)) })
    server.addErrorReporter(errorReporter)

    val library: SourceLibrary =
      FileSourceLibrary.fromConfigFile(libDir.resolve(FileUtils.LIBRARY_CONFIG_FILE), false, ListErrorReporter())


    libraryManager.updateLibrary(library, server)

    fun loadDependencies(lib: SourceLibrary) {
      for (dependencyName in lib.libraryDependencies) {
        if (libraryManager.containsLibrary(dependencyName)) continue
        val depConfigFile = libDir.resolve(dependencyName).resolve(FileUtils.LIBRARY_CONFIG_FILE)
        if (java.nio.file.Files.exists(depConfigFile)) {
          val depLibrary = FileSourceLibrary.fromConfigFile(depConfigFile, false, ListErrorReporter())
          if (depLibrary != null) {
            libraryManager.updateLibrary(depLibrary, server)
            // Load all source modules from the dependency library
            for (mod in depLibrary.findModules(false)) {
              depLibrary.getSource(mod, false)?.load(server, errorReporter)
            }
            loadDependencies(depLibrary)
          }
        }
      }
    }
    loadDependencies(library)

    val modulePath = modulePath(testFilename)

    // Also load all source modules from the main library itself
    for (mod in library.findModules(false)) {
      if (mod != modulePath) {
        library.getSource(mod, false)?.load(server, errorReporter)
      }
    }
    val module = ModuleLocation(
      library.libraryName,
      ModuleLocation.LocationKind.SOURCE,
      modulePath
    )
    val checker = server.getCheckerFor(
      listOf(module)
    )
    library.getSource(modulePath, false)?.load(server, errorReporter)
    val group: ConcreteGroup = server.getRawGroup(module) ?: throw IllegalArgumentException("Module not found: $modulePath")
    checker.resolveAll(UnstoppableCancellationIndicator.INSTANCE, ProgressReporter.empty())

    // Typecheck all loaded modules (dependencies) so their definitions are available
    val allModules = server.modules.toList()
    if (allModules.isNotEmpty()) {
      val allChecker = server.getCheckerFor(allModules)
      allChecker.typecheck(UnstoppableCancellationIndicator.INSTANCE, ProgressReporter.empty())
    }

    group.traverseGroup { x ->
      x.definition?.let {
        if (it is Concrete.FunctionDefinition) {
          checker.typecheck(
            FullName(module, it.data.refLongName),
            {
                errorReporter,
                pool,
                arendExtension,
                listener ->
                  object : CheckTypeVisitor(errorReporter, pool, arendExtension, listener) {
                    override fun visitGoal(expr: Concrete.GoalExpression, expectedType: Expression): TypecheckingResult {
                      val bestFirstSearch = BestFirstSearch(LLMStepGenerator(checker, server, library.libraryName, modulePath))
                      val goal = ArendGoal( expectedType, this, expr)
                      val proof = bestFirstSearch.search(goal) as? ArendProof
                      if (proof != null) {
                        println("Found proof: " + proof.getProof())
                      }
                      return super.visitGoal(expr, expectedType)
                    }
                  }
            },
            null, errorReporter, UnstoppableCancellationIndicator.INSTANCE,
            ProgressReporter.empty()
          )
        }
      }
    }

    //println(errorReporter.errorList.joinToString("\n"))
  } catch (e: Exception) {
    e.printStackTrace()
  }
}