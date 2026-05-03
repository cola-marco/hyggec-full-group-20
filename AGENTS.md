# hyggec AI Agent Guidelines

## Architecture Overview
hyggec is an F# didactic compiler for the Hygge programming language, targeting RISC-V assembly. The compilation pipeline follows: **Lexer → Parser → Typechecker → ANF Transform → Code Generator (RISC-V) → Peephole Optimizer → RARS Simulation**.

Key components in `src/`:
- `Lexer.fs`, `Parser.fs`: Front-end parsing
- `Typechecker.fs`: Static type checking with error reporting
- `ANF.fs`: A-normal form transformation for codegen
- `RISCVCodegen.fs`, `ANFRISCVCodegen.fs`: Assembly generation (use ANF variant for register allocation)
- `Interpreter.fs`: Direct execution of Hygge programs
- `Peephole.fs`: Post-codegen optimizations
- `RARS.fs`: Integration with RISC-V simulator

Data flows from Hygge source (`.hyg` files) through typed AST to RISC-V assembly, with ANF enabling efficient register-constrained codegen.

## Critical Workflows
- **Build & Test**: Run `./hyggec test` to build and execute full test suite (auto-rebuilds on source changes)
- **Interpret Programs**: `./hyggec interpret --typecheck --verbose examples/filename.hyg` for execution with logging
- **Compile to Assembly**: `./hyggec compile --anf --registers 8 --optimize 1 examples/filename.hyg` outputs RISC-V code
- **Simulate**: `./hyggec rars examples/filename.hyg` compiles and launches RARS simulator
- **Manual Build**: `dotnet build` (avoids script overhead for debugging)

Test failures in `tests/` subdirectories indicate phase-specific issues (e.g., `tests/typechecker/fail/` for type errors).

## Project-Specific Conventions
- **Test Organization**: Tests are `.hyg` files in `tests/{lexer,parser,typechecker,interpreter,codegen,codegen-anf}/{fail,pass}/`. Pass tests must succeed, fail tests must error appropriately.
- **ANF Codegen**: Always use `--anf` flag for compilation; specify `--registers` (3-18, default 18) for register allocation constraints.
- **Error Handling**: Type errors reported with position info; use `Util.formatMsg` for consistent formatting.
- **Logging**: Controlled by `--verbose` or `--log-level debug`; use `Log.debug/info/error` for diagnostics.
- **File Parsing**: All commands start with `Util.parseFile` for consistent AST loading.

## Integration Points
- **RARS Simulator**: Requires Java JRE; `lib/rars.jar` bundled; launched via `RARS.launch` for testing compiled code.
- **External Dependencies**: CommandLineParser.FSharp for CLI, Expecto for testing framework.
- **VS Code Setup**: Use Ionide extension with inlay hints disabled to preserve indentation-sensitive code alignment.

## Key Files & Examples
- `src/Program.fs`: Command dispatch and pipeline orchestration
- `examples/helloworld.hyg`: Basic I/O program
- `examples/fibonacci-imperative.hyg`: Control flow example
- `tests/typechecker/pass/structs.hyg`: Type system usage
- `src/Test.fs`: Test runner logic for phase-specific validation</content>
<parameter name="filePath">/home/primesoup/Documents/Uni/MSc/CompCon/hyggec-full-group-20/AGENTS.md
