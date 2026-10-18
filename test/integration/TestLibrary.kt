package integration

import org.arend.error.DummyErrorReporter
import org.arend.ext.error.ListErrorReporter
import org.arend.ext.module.ModuleLocation
import org.arend.frontend.library.BinaryLoader
import org.arend.frontend.library.CliServerRequester
import org.arend.frontend.library.FileSourceLibrary
import org.arend.frontend.library.LibraryManager
import org.arend.frontend.library.SourceLibrary
import org.arend.frontend.source.PreludeResourceSource
import org.arend.prelude.Prelude
import org.arend.server.ArendServer
import org.arend.server.ProgressReporter
import org.arend.server.impl.ArendServerImpl
import org.arend.term.group.ConcreteGroup
import org.arend.typechecking.computation.UnstoppableCancellationIndicator
import org.arend.util.FileUtils
import org.arend.util.FileUtils.modulePath
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths

/** A test Arend library, resolved and typechecked through the core API. */
class TestLibrary(val server: ArendServer, val libraryName: String) {
  class Module(val server: ArendServer, val libraryName: String, val group: ConcreteGroup, val location: ModuleLocation)

  fun module(name: String): Module? {
    val location = ModuleLocation(libraryName, ModuleLocation.LocationKind.SOURCE, modulePath(name))
    val group = server.getRawGroup(location) ?: return null
    return Module(server, libraryName, group, location)
  }

  companion object {
    private val projectDir: Path = Paths.get(System.getProperty("user.dir"))

    /** `test-lib`: no dependencies. */
    val testLibDir: Path = projectDir.resolve("test-lib")

    /** `test-lib-std`: depends on arend-lib. */
    val testLibStdDir: Path = projectDir.resolve("test-lib-std")

    /** The directory containing arend-lib: `-Darend.lib.path`'s parent, or the Arend checkout next to this project. */
    val arendLibsDir: Path? by lazy {
      val arendLib = System.getProperty("arend.lib.path")?.takeIf { it.isNotBlank() }?.let(Paths::get)
        ?: projectDir.resolveSibling("arend-lang-new/Arend/arend-lib")
      if (Files.exists(arendLib.resolve(FileUtils.LIBRARY_CONFIG_FILE))) arendLib.toAbsolutePath().normalize().parent else null
    }

    /** The Arend CLI jar: `-Darend.jar`, or the full jar of the Arend build next to this project. */
    val cliJar: Path? by lazy {
      System.getProperty("arend.jar")?.let { return@lazy Paths.get(it) }
      val libs = projectDir.resolveSibling("arend-lang-new/Arend/cli/build/libs")
      if (!Files.isDirectory(libs)) return@lazy null
      Files.list(libs).use { paths ->
        paths.filter { it.fileName.toString().matches(Regex("cli-.*-full\\.jar")) }.toList().maxByOrNull { it.fileName.toString() }
      }
    }

    private val cached = HashMap<Path, TestLibrary>()

    /** Loads `test-lib`, or returns null (with the reason printed) if it cannot be loaded. */
    fun load(): TestLibrary? = load(testLibDir)

    /** Loads `test-lib-std` with arend-lib, or returns null (with the reason printed) if it cannot be loaded. */
    fun loadStd(): TestLibrary? {
      val libsDir = arendLibsDir ?: run {
        println("SKIPPED: arend-lib not found; set -Darend.lib.path")
        return null
      }
      return load(testLibStdDir, listOf(libsDir))
    }

    /**
     * Loads the library at [dir] and its dependencies, found in [libDirs], the way the CLI does:
     * dependencies first, then the library's modules are resolved, the binaries of the
     * dependencies they import are loaded, and the library's own modules are typechecked.
     */
    fun load(dir: Path, libDirs: List<Path> = emptyList()): TestLibrary? {
      cached[dir]?.let { return it }

      val configFile = dir.resolve(FileUtils.LIBRARY_CONFIG_FILE)
      if (!Files.exists(configFile)) {
        println("SKIPPED: library not found at $dir")
        return null
      }

      val errorReporter = ListErrorReporter()
      val libraryManager = LibraryManager(errorReporter)
      val server: ArendServer = ArendServerImpl(CliServerRequester(libraryManager), false, false, true)
      server.addReadOnlyModule(
        Prelude.MODULE_LOCATION,
        { PreludeResourceSource().loadGroup(DummyErrorReporter.INSTANCE)!! }
      )
      server.addErrorReporter(errorReporter)

      fun readLibrary(config: Path): SourceLibrary? {
        val libraryErrors = ListErrorReporter()
        return FileSourceLibrary.fromConfigFile(config, false, libraryErrors) ?: run {
          println("SKIPPED: FileSourceLibrary.fromConfigFile returned null for $config: ${libraryErrors.errorList}")
          null
        }
      }

      val library = readLibrary(configFile) ?: return null
      val loaded = mutableListOf<SourceLibrary>()
      // A library's extension is set up when it is loaded, so dependencies have to come first
      fun loadWithDependencies(lib: SourceLibrary): Boolean {
        if (libraryManager.containsLibrary(lib.libraryName)) return true
        for (dependency in lib.libraryDependencies) {
          val dependencyConfig = libDirs.map { it.resolve(dependency).resolve(FileUtils.LIBRARY_CONFIG_FILE) }.find(Files::exists)
            ?: run {
              println("SKIPPED: dependency $dependency of ${lib.libraryName} not found in $libDirs")
              return false
            }
          if (!loadWithDependencies(readLibrary(dependencyConfig) ?: return false)) return false
        }
        libraryManager.updateLibrary(lib, server)
        loaded.add(lib)
        return true
      }
      if (!loadWithDependencies(library)) return null

      val locations = library.findModules(false).map { ModuleLocation(library.libraryName, ModuleLocation.LocationKind.SOURCE, it) }
      server.getCheckerFor(locations).resolveAll(UnstoppableCancellationIndicator.INSTANCE, ProgressReporter.empty())
      // Binaries refer to Prelude's definitions, so Prelude has to be loaded before them
      server.getCheckerFor(listOf(Prelude.MODULE_LOCATION)).typecheck(UnstoppableCancellationIndicator.INSTANCE, ProgressReporter.empty())
      val binaryLoader = BinaryLoader(libraryManager)
      for (lib in loaded) {
        if (lib != library) binaryLoader.loadBinaryCache(lib, server)
      }
      server.getCheckerFor(locations).typecheck(UnstoppableCancellationIndicator.INSTANCE, ProgressReporter.empty())

      return TestLibrary(server, library.libraryName).also { cached[dir] = it }
    }
  }
}
