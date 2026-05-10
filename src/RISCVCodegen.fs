// hyggec - The didactic compiler for the Hygge programming language.
// Copyright (C) 2023 Technical University of Denmark
// Author: Alceste Scalas <alcsc@dtu.dk>
// Released under the MIT license (see LICENSE.md for details)

/// Functions to generate RISC-V assembly code from a typed Hygge AST.
module RISCVCodegen

open AST
open RISCV
open Type
open Typechecker
open ASTUtil


/// Exit code used in the generated assembly to signal an assertion violation.
let assertExitCode = 42 // Must be non-zero

/// Maximum depth used when recursively printing structure values in assertion diagnostics.
/// Handles nested structures while preventing infinite output for recursive values.
let internal assertStructPrintDepth = 6


let internal floatToWord (f: float32) : int32 =
    let b = System.BitConverter.GetBytes(f)
    if not System.BitConverter.IsLittleEndian then System.Array.Reverse(b)
    System.BitConverter.ToInt32(b)


/// Storage information for variables.
[<RequireQualifiedAccess; StructuralComparison; StructuralEquality>]
type internal Storage =
    /// The variable is stored in an integer register.
    | Reg of reg: Reg
    /// The variable is stored in a floating-point register.
    | FPReg of fpreg: FPReg
    /// The variable is stored in memory, in a location marked with a
    /// label in the compiled assembly code.
    | Label of label: string
    /// Variable stored on stack at offset from fp
    | Frame of offset: int


/// Code generation environment.
type internal CodegenEnv = {
    /// Target register number for the result of non-floating-point expressions.
    Target: uint
    /// Target register number for the result of floating-point expressions.
    FPTarget: uint
    /// Storage information about known variables.
    VarStorage: Map<string, Storage>
}

let rec internal isCV (varName, (scope: Node<'a,'b>)) =
    match scope.Expr with
    | Lambda(args, body) ->
        if List.exists (fun (name, _) -> name = varName) args then false
        else isCV(varName, body)
    | Var(name) -> name = varName
    | UnitVal | BoolVal(_) | IntVal(_) | FloatVal(_) | StringVal(_) | Pointer(_) -> false
    | Let(name, init, scope) | LetT(name, _, init, scope) | LetMut(name, init, scope) ->
        let cvInit = isCV(varName, init)
        let cvScope = if name = varName then false else isCV(varName, scope)
        cvInit || cvScope
    | BinNumOp(_, lhs, rhs) | BinLogicOp(_, lhs, rhs) | BinRelOp(_, lhs, rhs) ->
        isCV(varName, lhs) || isCV(varName, rhs)
    | Sqrt(arg) | Not(arg) | Print(arg) | PrintLn(arg) | Assertion(arg)
    | Ascription(_, arg) | UnionCons(_, arg) | ArrayLength(arg) | Copy(arg) | DeepCopy(arg) ->
        isCV(varName, arg)
    | If(cond, ifTrue, ifFalse) ->
        isCV(varName, cond) || isCV(varName, ifTrue) || isCV(varName, ifFalse)
    | Seq(nodes) ->
        List.exists (fun n -> isCV(varName, n)) nodes
    | Type(_, _, scope) ->
        isCV(varName, scope)
    | While(cond, body) | DoWhile(body, cond) | ArrayCons(cond, body) ->
        isCV(varName, cond) || isCV(varName, body)
    | For(name, init, cond, step, body) ->
        isCV(varName, init) ||
        if name = varName then false
        else isCV(varName, cond) || isCV(varName, step) || isCV(varName, body)
    | Application(expr, args) ->
        isCV(varName, expr) || List.exists (fun a -> isCV(varName, a)) args
    | StructCons(fields) ->
        List.exists (fun (_, n) -> isCV(varName, n)) fields
    | FieldSelect(target, _) ->
        isCV(varName, target)
    | Assign(target, expr) ->
        isCV(varName, target) || isCV(varName, expr)
    | Match(expr, cases) ->
        isCV(varName, expr) || List.exists (fun (_, v, cont) ->
            if v = varName then false else isCV(varName, cont)) cases
    | ArrayElem(name, index) ->
        isCV(varName, name) || isCV(varName, index)
    | ReadInt | ReadFloat -> false


/// Code generation function: compile the expression in the given AST node so
/// that it writes its results on the 'Target' and 'FPTarget' generic register
/// numbers (specified in the given codegen 'env'ironment).  IMPORTANT: the
/// generated code must never modify the contents of register numbers lower than
/// the given targets.
let rec internal doCodegen (env: CodegenEnv) (node: TypedAST): Asm =
    match node.Expr with
    | UnitVal -> Asm() // Nothing to do

    | BoolVal(v) ->
        /// Boolean constant turned into integer 1 if true, or 0 if false
        let value = if v then 1 else 0
        Asm(RV.LI(Reg.r(env.Target), value), $"Bool value '%O{v}'")

    | IntVal(v) ->
        Asm(RV.LI(Reg.r(env.Target), v))

    | FloatVal(v) ->
        // We convert the float value into its bytes, and load it as immediate
        let bytes = System.BitConverter.GetBytes(v)
        if (not System.BitConverter.IsLittleEndian)
            then System.Array.Reverse(bytes) // RISC-V is little-endian
        let word: int32 = System.BitConverter.ToInt32(bytes)
        Asm([ (RV.LI(Reg.r(env.Target), word), $"Float value %f{v}")
              (RV.FMV_W_X(FPReg.r(env.FPTarget), Reg.r(env.Target)), "") ])

    | StringVal(v) ->
        // Label marking the string constant in the data segment
        let label = Util.genSymbol "string_val"
        Asm().AddData(label, Alloc.String(v))
             .AddText(RV.LA(Reg.r(env.Target), label))

    | Var(name) ->
        // To compile a variable, we inspect its type and where it is stored
        match node.Type with
        | t when (isSubtypeOf node.Env t TUnit)
            -> Asm() // A unit-typed variable is just ignored
        | t when (isSubtypeOf node.Env t TFloat) ->
            match (env.VarStorage.TryFind name) with
            | Some(Storage.FPReg(fpreg)) ->
                Asm(RV.FMV_S(FPReg.r(env.FPTarget), fpreg),
                    $"Load variable '%s{name}'")
            | Some(Storage.Frame(offset)) ->
                Asm(RV.FLW_S(FPReg.r(env.FPTarget), Imm12(offset), Reg.fp),
                    $"Load float variable '%s{name}' from stack frame")
            | Some(Storage.Label(lab)) ->
                Asm([ (RV.LA(Reg.r(env.Target), lab),
                       $"Load address of variable '%s{name}'")
                      (RV.LW(Reg.r(env.Target), Imm12(0), Reg.r(env.Target)),
                       $"Load value of variable '%s{name}'")
                      (RV.FMV_W_X(FPReg.r(env.FPTarget), Reg.r(env.Target)),
                       $"Transfer '%s{name}' to fp register") ])
            | Some(Storage.Reg(_)) as st ->
                failwith $"BUG: variable %s{name} of type %O{t} has unexpected storage %O{st}"
            | None -> failwith $"BUG: float variable without storage: %s{name}"
        | t ->  // Default case for variables holding integer-like values
            match (env.VarStorage.TryFind name) with
            | Some(Storage.Reg(reg)) ->
                Asm(RV.MV(Reg.r(env.Target), reg), $"Load variable '%s{name}'")
            | Some(Storage.Frame(offset)) ->
                Asm(RV.LW(Reg.r(env.Target), Imm12(offset), Reg.fp),
                    $"Load variable '%s{name}' from stack frame")
            | Some(Storage.Label(lab)) ->
                match (expandType node.Env node.Type) with
                    | TFun(_,_) ->
                        Asm(RV.LA(Reg.r(env.Target), lab),
                            $"Load variable '%s{name}' (labmda term)")
                    | _ ->
                        Asm([ (RV.LA(Reg.r(env.Target), lab),
                               $"Load address of variable '%s{name}'")
                              (RV.LW(Reg.r(env.Target), Imm12(0), Reg.r(env.Target)),
                               $"Load value of variable '%s{name}'") ])
            | Some(Storage.FPReg(_)) as st ->
                failwith $"BUG: variable %s{name} of type %O{t} has unexpected storage %O{st}"
            | None -> failwith $"BUG: variable without storage: %s{name}"

    | BinNumOp(op, lhs, rhs) ->
        // Code generation for most binary numerical operations is very
        // similar: we compile the lhs and rhs giving them different target
        // registers, and then apply the relevant assembly operation(s) on their
        // results.

        /// Generated code for the lhs expression
        let lAsm = doCodegen env lhs
        // The generated code depends on the type of operation being computed
        match node.Type with
        | t when (isSubtypeOf node.Env t TInt) ->
            /// Target register for the rhs expression
            let rtarget = env.Target + 1u
            /// Generated code for the rhs expression
            let rAsm = doCodegen {env with Target = rtarget} rhs
            /// Generated code for the numerical operation
            let opAsm =
                match op with
                | NumericalOp.Add ->
                    Asm(RV.ADD(Reg.r(env.Target),
                               Reg.r(env.Target), Reg.r(rtarget)))
                | NumericalOp.Sub ->
                    Asm(RV.SUB(Reg.r(env.Target),
                               Reg.r(env.Target), Reg.r(rtarget)))  
                | NumericalOp.Mult ->
                    Asm(RV.MUL(Reg.r(env.Target),
                               Reg.r(env.Target), Reg.r(rtarget)))
                | NumericalOp.Div ->
                    Asm(RV.DIV(Reg.r(env.Target),
                               Reg.r(env.Target), Reg.r(rtarget)))
                | NumericalOp.Mod ->
                    Asm(RV.REM(Reg.r(env.Target),
                               Reg.r(env.Target), Reg.r(rtarget)))
            // Put everything together
            lAsm ++ rAsm ++ opAsm
        | t when (isSubtypeOf node.Env t TFloat) ->
            /// Target register for the rhs expression
            let rfptarget = env.FPTarget + 1u
            /// Generated code for the rhs expression
            let rAsm = doCodegen {env with FPTarget = rfptarget} rhs
            /// Generated code for the numerical operation
            let opAsm =
                match op with
                | NumericalOp.Add ->
                    Asm(RV.FADD_S(FPReg.r(env.FPTarget),
                                  FPReg.r(env.FPTarget), FPReg.r(rfptarget)))
                | NumericalOp.Sub ->
                    Asm(RV.FSUB_S(FPReg.r(env.FPTarget),
                                  FPReg.r(env.FPTarget), FPReg.r(rfptarget)))
                | NumericalOp.Mult ->
                    Asm(RV.FMUL_S(FPReg.r(env.FPTarget),
                                  FPReg.r(env.FPTarget), FPReg.r(rfptarget)))
                | NumericalOp.Div ->
                    Asm(RV.FDIV_S(FPReg.r(env.FPTarget),
                                  FPReg.r(env.FPTarget), FPReg.r(rfptarget)))
                | NumericalOp.Mod ->
                    failwith "Remainder operation not defined for TFloat. This should not happen."
            // Put everything together
            lAsm ++ rAsm ++ opAsm
        | t ->
            failwith $"BUG: numerical operation codegen invoked on invalid type %O{t}"

    | Sqrt(arg) ->
        // First, generate code for the argument in the floating-point target
        let argAsm = doCodegen env arg
        // Compute square root using RISC-V floating-point sqrt instruction
        let sqrtAsm = Asm(RV.FSQRT_S(FPReg.r(env.FPTarget), FPReg.r(env.FPTarget)))
        // Combine argument code and sqrt instruction
        argAsm ++ sqrtAsm        

    | BinLogicOp(LogicOp.AndS, lhs, rhs) ->
        let endLabel = Util.genSymbol "ands_end"
        (doCodegen env lhs)
            .AddText(
                RV.BEQZ(Reg.r(env.Target), endLabel),"short-circuit and, if lhs is false skip rhs"
                )
            ++ (doCodegen env rhs)
            .AddText(
                RV.LABEL(endLabel)
            )

    | BinLogicOp(LogicOp.OrS, lhs, rhs) ->
        let endLabel = Util.genSymbol "ors_end"
        (doCodegen env lhs)
            .AddText(
                RV.BNEZ(Reg.r(env.Target), endLabel),"short-circuit or, if lhs is true skip rhs"
                )
            ++ (doCodegen env rhs)
            .AddText(
                RV.LABEL(endLabel)
            )

    | BinLogicOp(op, lhs, rhs) ->
        // Code generation for binary logical operations is very similar: we
        // compile the lhs and rhs giving them different target registers, and
        // then apply the relevant assembly operation(s) on their results.

        /// Generated code for the lhs expression
        let lAsm = doCodegen env lhs
        /// Target register for the rhs expression
        let rtarget = env.Target + 1u
        /// Generated code for the rhs expression
        let rAsm = doCodegen {env with Target = rtarget} rhs
        /// Generated code for the logical operation
        let opAsm =
            match op with
            | LogicOp.And ->
                Asm(RV.AND(Reg.r(env.Target), Reg.r(env.Target), Reg.r(rtarget)))
            | LogicOp.Or ->
                Asm(RV.OR(Reg.r(env.Target), Reg.r(env.Target), Reg.r(rtarget)))
            | LogicOp.Xor ->
                Asm(RV.XOR(Reg.r(env.Target), Reg.r(env.Target), Reg.r(rtarget)))            
            | LogicOp.AndS -> failwith "Not Implemented"
            | LogicOp.OrS -> failwith "Not Implemented"
        // Put everything together
        lAsm ++ rAsm ++ opAsm

    | Not(arg) ->
        /// Generated code for the argument expression (note that we don't need
        /// to increase its target register)
        let asm = doCodegen env arg
        asm.AddText(RV.SEQZ(Reg.r(env.Target), Reg.r(env.Target)))

    | BinRelOp(op, lhs, rhs) ->
        // Code generation for binary relations between numbers is very similar:
        // we compile the lhs and rhs giving them different target registers,
        // and then apply the relevant assembly operation(s) on their results.

        /// Generated code for the lhs expression
        let lAsm = doCodegen env lhs
        // The generated code depends on the lhs and rhs types
        match lhs.Type with
        | t when (isSubtypeOf lhs.Env t TInt) ->
            // Our goal is to write 1 (true) or 0 (false) in the register
            // env.Target, depending on the result of the comparison between
            // the lhs and rhs.  To achieve this, we perform a conditional
            // branch depending on whether the lhs and rhs are equal (or the lhs
            // is less than the rhs):
            // - if the comparison is true, we jump to a label where we write
            //   1 in the target register, and continue
            // - if the comparison is false, we write 0 in the target register
            //   and we jump to a label marking the end of the generated code

            /// Target register for the rhs expression
            let rtarget = env.Target + 1u
            /// Generated code for the rhs expression
            let rAsm = doCodegen {env with Target = rtarget} rhs

            /// Human-readable prefix for jump labels, describing the kind of
            /// relational operation we are compiling
            let labelName = match op with
                            | RelationalOp.Eq -> "eq"
                            | RelationalOp.Less -> "less"
                            | RelationalOp.LessEq -> "lesseq"
                            | RelationalOp.Greater -> "greater"
            /// Label to jump to when the comparison is true
            let trueLabel = Util.genSymbol $"%O{labelName}_true"
            /// Label to mark the end of the comparison code
            let endLabel = Util.genSymbol $"%O{labelName}_end"

            /// Codegen for the relational operation between lhs and rhs
            let opAsm =
                match op with
                | RelationalOp.Eq ->
                    Asm(RV.BEQ(Reg.r(env.Target), Reg.r(rtarget), trueLabel))
                | RelationalOp.Less ->
                    Asm(RV.BLT(Reg.r(env.Target), Reg.r(rtarget), trueLabel))
                | RelationalOp.LessEq ->
                    Asm(RV.BLE(Reg.r(env.Target), Reg.r(rtarget), trueLabel))
                | RelationalOp.Greater ->
                    Asm(RV.BGT(Reg.r(env.Target), Reg.r(rtarget), trueLabel))

            // Put everything together
            (lAsm ++ rAsm ++ opAsm)
                .AddText([
                    (RV.LI(Reg.r(env.Target), 0), "Comparison result is false")
                    (RV.J(endLabel), "")
                    (RV.LABEL(trueLabel), "")
                    (RV.LI(Reg.r(env.Target), 1), "Comparison result is true")
                    (RV.LABEL(endLabel), "")
                ])
        | t when (isSubtypeOf lhs.Env t TFloat) ->
            /// Target register for the rhs expression
            let rfptarget = env.FPTarget + 1u
            /// Generated code for the rhs expression
            let rAsm = doCodegen {env with FPTarget = rfptarget} rhs
            /// Generated code for the relational operation
            let opAsm =
                match op with
                | RelationalOp.Eq ->
                    Asm(RV.FEQ_S(Reg.r(env.Target), FPReg.r(env.FPTarget), FPReg.r(rfptarget)))
                | RelationalOp.Less ->
                    Asm(RV.FLT_S(Reg.r(env.Target), FPReg.r(env.FPTarget), FPReg.r(rfptarget)))
                | RelationalOp.LessEq ->
                    Asm(RV.FLE_S(Reg.r(env.Target), FPReg.r(env.FPTarget), FPReg.r(rfptarget)))
                | RelationalOp.Greater ->
                    Asm(RV.FLT_S(Reg.r(env.Target), FPReg.r(rfptarget), FPReg.r(env.FPTarget)))
            // Put everything together
            (lAsm ++ rAsm ++ opAsm)
        | t ->
            failwith $"BUG: relational operation codegen invoked on invalid type %O{t}"

    | ReadInt ->
        (beforeSysCall [Reg.a0] [])
            .AddText([
                (RV.LI(Reg.a7, 5), "RARS syscall: ReadInt")
                (RV.ECALL, "")
                (RV.MV(Reg.r(env.Target), Reg.a0), "Move syscall result to target")
            ])
            ++ (afterSysCall [Reg.a0] [])

    | ReadFloat ->
        (beforeSysCall [] [FPReg.fa0])
            .AddText([
                (RV.LI(Reg.a7, 6), "RARS syscall: ReadFloat")
                (RV.ECALL, "")
                (RV.FMV_S(FPReg.r(env.FPTarget), FPReg.fa0), "Move syscall result to target")
            ])
            ++ (afterSysCall [] [FPReg.fa0])

    | Print(arg) ->
        /// Compiled code for the 'print' argument, leaving its result on the
        /// generic register 'target' or 'fptarget' (depending on its type)
        let argCode = doCodegen env arg
        // The generated code depends on the 'print' argument type
        match arg.Type with
        | t when (isSubtypeOf arg.Env t TBool) ->
            let strTrue = Util.genSymbol "true"
            let strFalse = Util.genSymbol "false"
            let printFalse = Util.genSymbol "print_true"
            let printExec = Util.genSymbol "print_execute"
            argCode.AddData(strTrue, Alloc.String("true"))
                .AddData(strFalse, Alloc.String("false"))
                ++ (beforeSysCall [Reg.a0] [])
                  .AddText([
                    (RV.BEQZ(Reg.r(env.Target), printFalse), "")
                    (RV.LA(Reg.a0, strTrue), "String to print via syscall")
                    (RV.J(printExec), "")
                    (RV.LABEL(printFalse), "")
                    (RV.LA(Reg.a0, strFalse), "String to print via syscall")
                    (RV.LABEL(printExec), "")
                    (RV.LI(Reg.a7, 4), "RARS syscall: PrintString")
                    (RV.ECALL, "")
                  ])
                  ++ (afterSysCall [Reg.a0] [])
        | t when (isSubtypeOf arg.Env t TInt) ->
            argCode
            ++ (beforeSysCall [Reg.a0] [])
                .AddText([
                    (RV.MV(Reg.a0, Reg.r(env.Target)), "Copy to a0 for printing")
                    (RV.LI(Reg.a7, 1), "RARS syscall: PrintInt")
                    (RV.ECALL, "")
                ])
                ++ (afterSysCall [Reg.a0] [])
        | t when (isSubtypeOf arg.Env t TFloat) ->
            argCode
            ++ (beforeSysCall [] [FPReg.fa0])
                .AddText([
                    (RV.FMV_S(FPReg.fa0, FPReg.r(env.FPTarget)), "Copy to fa0 for printing")
                    (RV.LI(Reg.a7, 2), "RARS syscall: PrintFloat")
                    (RV.ECALL, "")
                ])
                ++ (afterSysCall [] [FPReg.fa0])
        | t when (isSubtypeOf arg.Env t TString) ->
            argCode
            ++ (beforeSysCall [Reg.a0] [])
                .AddText([
                    (RV.MV(Reg.a0, Reg.r(env.Target)), "Copy to a0 for printing")
                    (RV.LI(Reg.a7, 4), "RARS syscall: PrintString")
                    (RV.ECALL, "")
                ])
                ++ (afterSysCall [Reg.a0] [])
        | t ->
            failwith $"BUG: Print codegen invoked on unsupported type %O{t}"

    | PrintLn(arg) ->
        // Recycle codegen for Print above, then also output a newline
        (doCodegen env {node with Expr = Print(arg)})
        ++ (beforeSysCall [Reg.a0] [])
            .AddText([
                (RV.LI(Reg.a7, 11), "RARS syscall: PrintChar")
                (RV.LI(Reg.a0, int('\n')), "Character to print (newline)")
                (RV.ECALL, "")
            ])
            ++ (afterSysCall [Reg.a0] [])

    | If(condition, ifTrue, ifFalse) ->
        /// Label to jump to when the 'if' condition is true
        let labelTrue = Util.genSymbol "if_true"
        /// Label to jump to when the 'if' condition is false
        let labelFalse = Util.genSymbol "if_false"
        /// Label to mark the end of the if..then...else code
        let labelEnd = Util.genSymbol "if_end"
        // Compile the 'if' condition; if the result is true (i.e., not zero)
        // then jump to 'labelTrue', execute the 'ifTrue' code, and finally jump
        // to 'labelEnd' (thus skipping the code under 'labelFalse'). Otherwise
        // (i.e., when the 'if' condition result is false) jump to 'labelFalse'
        // and execute the 'ifFalse' code. Here we use a register to load the
        // address of a label (using the instruction LA) and then jump to it
        // (using the instruction JR): this way, the label address can be very
        // far from the jump instruction address --- and this can be important
        // if the compilation of 'ifTrue' and/or 'ifFalse' produces a large
        // amount of assembly code
        (doCodegen env condition)
            .AddText([ (RV.BNEZ(Reg.r(env.Target), labelTrue),
                        "Jump when 'if' condition is true")
                       (RV.LA(Reg.r(env.Target), labelFalse),
                        "Load the address of the 'false' branch of the 'if' code")
                       (RV.JR(Reg.r(env.Target)),
                        "Jump to the 'false' branch of the 'if' code")
                       (RV.LABEL(labelTrue),
                        "Beginning of the 'true' branch of the 'if' code") ])
            ++ (doCodegen env ifTrue)
                .AddText([ (RV.LA(Reg.r(env.Target + 1u), labelEnd),
                            "Load the address of the end of the 'if' code")
                           (RV.JR(Reg.r(env.Target + 1u)),
                            "Jump to skip the 'false' branch of 'if' code")
                           (RV.LABEL(labelFalse),
                            "Beginning of the 'false' branch of the 'if' code") ])
                ++ (doCodegen env ifFalse)
                    .AddText(RV.LABEL(labelEnd), "End of the 'if' code")

    | Seq(nodes) ->
        // We collect the code of each sequence node by folding over all nodes
        let folder (asm: Asm) (node: TypedAST) =
            asm ++ (doCodegen env node)
        List.fold folder (Asm()) nodes

    | Type(_, _, scope) ->
        // A type alias does not produce any code --- but its scope does
        doCodegen env scope

    | Ascription(_, node) ->
        // A type ascription does not produce code --- but the type-annotated
        // AST node does
        doCodegen env node

    | Assertion(arg) ->
        /// Label to jump to when the assertion is true
        let passLabel = Util.genSymbol "assert_true"

        /// The variables whose runtime values should be reported if this
        /// assertion fails.  We use the existing AST utility for free variables:
        /// variables bound inside the assertion expression itself are not part of
        /// the surrounding runtime context and should therefore not be printed.
        let freeVarNames =
            freeVars arg
            |> Set.toList
            |> List.sort

        /// Compile-time part of the assertion diagnostic.  The runtime values of
        /// the variables listed below are appended by generated code only on the
        /// failing path.
        let failHeader =
            $"Assertion failure at "
            + $"%d{node.Pos.Begin.Line}:%d{node.Pos.Begin.Column}"
            + $"-%d{node.Pos.End.Line}:%d{node.Pos.End.Column}\n"
            + $"expression: %s{formatAssertionExpr arg}\n"

        /// Generated code that prints the runtime values of all free variables
        /// appearing in the failed assertion expression.
        let valueDiagnostics = codegenAssertionValues env arg freeVarNames

        // Check the assertion, and jump to 'passLabel' if it is true.
        // Otherwise, print a detailed diagnostic and terminate.
        (doCodegen env arg)
            .AddText([
                (RV.ADDI(Reg.r(env.Target), Reg.r(env.Target), Imm12(-1)), "")
                (RV.BEQZ(Reg.r(env.Target), passLabel), "Jump if assertion OK")
            ])
            ++ (printStringLiteral failHeader)
            ++ valueDiagnostics
            .AddText([
                (RV.LI(Reg.a7, 93), "RARS syscall: Exit2")
                (RV.LI(Reg.a0, assertExitCode), "Assertion violation exit code")
                (RV.ECALL, "")
                (RV.LABEL(passLabel), "")
            ])

    // Special case for compiling a function with a given immutable name in the
    // input source file.  We recognise this case by checking whether the
    // 'Let...' declares 'name' as a Lambda expression with a TFun type
    | Let(name, {Node.Expr = Lambda(args, body);
                 Node.Type = TFun(targs, _)}, scope)
    | LetT(name, _, {Node.Expr = Lambda(args, body);
                     Node.Type = TFun(targs, _)}, scope) ->
        /// Assembly label to mark the position of the compiled function body.
        /// For readability, we make the label similar to the function name
        let funLabel = Util.genSymbol $"fun_%s{name}"

        /// Names of the lambda term arguments
        let (argNames, _) = List.unzip args
        /// List of pairs associating each function argument to its type
        let argNamesTypes = List.zip argNames targs
        /// Compiled function body
        let bodyCode = compileFunction argNamesTypes body env

        /// Compiled function code where the function label is located just
        /// before the 'bodyCode', and everything is placed at the end of the
        /// Text segment (i.e. in the "PostText")
        let funCode =
            (Asm(RV.LABEL(funLabel), $"Code for function '%s{name}'")
                ++ bodyCode).TextToPostText

        /// Storage info where the name of the compiled function points to the
        /// label 'funLabel'
        let varStorage2 = env.VarStorage.Add(name, Storage.Label(funLabel))

        // Finally, compile the 'let...'' scope with the newly-defined function
        // label in the variables storage, and append the 'funCode' above. The
        // 'scope' code leaves its result in the the 'let...' target register
        (doCodegen {env with VarStorage = varStorage2} scope)
            ++ funCode

    | Let(name, init, scope)
    | LetT(name, _, init, scope)
    | LetMut(name, init, scope) ->
        /// 'let...' initialisation code, which leaves its result in the
        /// 'target' register (which we overwrite at the end of the 'scope'
        /// execution)
        let initCode = doCodegen env init
        match init.Type with
        | t when (isSubtypeOf init.Env t TUnit) ->
            // The 'init' produces a unit value, i.e. nothing: we can keep using
            // the same target registers, and we don't need to update the
            // variables-to-registers mapping.
            initCode ++ (doCodegen env scope)
        | t when (isSubtypeOf init.Env t TFloat) ->
            /// Target register for compiling the 'let' scope
            let scopeTarget = env.FPTarget + 1u
            /// Variable storage for compiling the 'let' scope
            let scopeVarStorage =
                env.VarStorage.Add(name, Storage.FPReg(FPReg.r(env.FPTarget)))
            /// Environment for compiling the 'let' scope
            let scopeEnv = { env with FPTarget = scopeTarget
                                                 VarStorage = scopeVarStorage }
            initCode
                ++ (doCodegen scopeEnv scope)
                    .AddText(RV.FMV_S(FPReg.r(env.FPTarget),
                                    FPReg.r(scopeTarget)),
                            "Move result of 'let' scope expression into target register")
        | _ ->  // Default case for integer-like initialisation expressions
            /// Target register for compiling the 'let' scope
            let scopeTarget = env.Target + 1u
            /// Variable storage for compiling the 'let' scope
            let scopeVarStorage =
                env.VarStorage.Add(name, Storage.Reg(Reg.r(env.Target)))
            /// Environment for compiling the 'let' scope
            let scopeEnv = { env with Target = scopeTarget
                                               VarStorage = scopeVarStorage }
            initCode
                ++ (doCodegen scopeEnv scope)
                    .AddText(RV.MV(Reg.r(env.Target), Reg.r(scopeTarget)),
                            "Move 'let' scope result to 'let' target register")

    | Assign(lhs, rhs) ->
        match lhs.Expr with
        | Var(name) ->
            /// Code for the 'rhs', leaving its result in the target register
            let rhsCode = doCodegen env rhs
            match rhs.Type with
            | t when (isSubtypeOf rhs.Env t TUnit) ->
                rhsCode // No assignment to perform
            | _ ->
                match (env.VarStorage.TryFind name) with
                | Some(Storage.Reg(reg)) ->
                    rhsCode.AddText(RV.MV(reg, Reg.r(env.Target)),
                                    $"Assignment to variable %s{name}")
                | Some(Storage.FPReg(reg)) ->
                    rhsCode.AddText(RV.FMV_S(reg, FPReg.r(env.FPTarget)),
                                    $"Assignment to variable %s{name}")
                | Some(Storage.Label(lab)) ->
                    match rhs.Type with
                    | t when (isSubtypeOf rhs.Env t TFloat) ->
                        rhsCode.AddText([ (RV.LA(Reg.r(env.Target), lab),
                                           $"Load address of variable '%s{name}'")
                                          (RV.FSW_S(FPReg.r(env.FPTarget), Imm12(0),
                                                    Reg.r(env.Target)),
                                           $"Transfer value of '%s{name}' to memory") ])
                    | _ ->
                        rhsCode.AddText([ (RV.LA(Reg.r(env.Target + 1u), lab),
                                           $"Load address of variable '%s{name}'")
                                          (RV.SW(Reg.r(env.Target), Imm12(0),
                                                 Reg.r(env.Target + 1u)),
                                           $"Transfer value of '%s{name}' to memory") ])
                | None -> failwith $"BUG: variable without storage: %s{name}"                
                | Some(value) -> failwith "Not Implemented"
        | FieldSelect(target, field) ->
            /// Assembly code for computing the 'target' object of which we are
            /// selecting the 'field'.  We write the computation result (which
            /// should be a struct memory address) in the target register.
            let selTargetCode = doCodegen env target
            /// Code for the 'rhs', leaving its result in the target+1 register
            let rhsCode = doCodegen {env with Target = env.Target + 1u} rhs
            match (expandType target.Env target.Type) with
            | TStruct(fields) ->
                /// Names of the struct fields
                let (fieldNames, _) = List.unzip fields
                /// Offset of the selected struct field from the beginning of
                /// the struct
                let offset = List.findIndex (fun f -> f = field) fieldNames
                /// Assembly code that performs the field value assignment
                let assignCode =
                    match rhs.Type with
                    | t when (isSubtypeOf rhs.Env t TUnit) ->
                        Asm() // Nothing to do
                    | t when (isSubtypeOf rhs.Env t TFloat) ->
                        Asm(RV.FSW_S(FPReg.r(env.FPTarget), Imm12(offset * 4),
                                     Reg.r(env.Target)),
                            $"Assigning value to struct field '%s{field}'")
                    | _ ->
                        Asm([(RV.SW(Reg.r(env.Target + 1u), Imm12(offset * 4),
                                    Reg.r(env.Target)),
                              $"Assigning value to struct field '%s{field}'")
                             (RV.MV(Reg.r(env.Target), Reg.r(env.Target + 1u)),
                              "Copying assigned value to target register")])
                // Put everything together
                selTargetCode ++ rhsCode ++ assignCode
            | t ->
                failwith $"BUG: field selection on invalid object type: %O{t}"
        | ArrayElem(arrayExpr, indexExpr) ->
            /// Compile the array expression to get the pointer in target register
            let arrayCode = doCodegen env arrayExpr
            /// Compile the index expression to target+1 register
            let indexCode = doCodegen {env with Target = env.Target + 1u} indexExpr
            /// Compile the rhs to target+2 register, leaving the index in target+1
            let rhsCode = doCodegen {env with Target = env.Target + 2u} rhs
            /// Calculate element address: base + 4 + index*4
            let addrCalcCode =
                Asm([
                    (RV.ADDI(Reg.r(env.Target + 3u), Reg.r(env.Target + 1u), Imm12(1)), "offset_index = 1 + index")
                    (RV.SLLI(Reg.r(env.Target + 3u), Reg.r(env.Target + 3u), Shamt(2u)), "offset_index = offset_index * 4")
                    (RV.ADD(Reg.r(env.Target + 3u), Reg.r(env.Target), Reg.r(env.Target + 3u)), "element_addr = base + offset")
                ])
            /// Assembly code that performs the array element assignment
            let assignCode =
                match rhs.Type with
                | t when (isSubtypeOf rhs.Env t TUnit) ->
                    Asm()
                | t when (isSubtypeOf rhs.Env t TFloat) ->
                    Asm(RV.FSW_S(FPReg.r(env.FPTarget), Imm12(0), Reg.r(env.Target + 3u)),
                        "Store float value to array element")
                | _ ->
                    Asm(RV.SW(Reg.r(env.Target + 2u), Imm12(0), Reg.r(env.Target + 3u)),
                        "Store value to array element")
            /// Put everything together
            arrayCode ++ indexCode ++ rhsCode ++ addrCalcCode ++ assignCode
        | _ ->
            failwith ($"BUG: assignment to invalid target:%s{Util.nl}"
                      + $"%s{PrettyPrinter.prettyPrint lhs}")

    | While(cond, body) ->
        /// Label to mark the beginning of the 'while' loop
        let whileBeginLabel = Util.genSymbol "while_loop_begin"
        /// Label to mark the beginning of the 'while' loop body
        let whileBodyBeginLabel = Util.genSymbol "while_body_begin"
        /// Label to mark the end of the 'while' loop
        let whileEndLabel = Util.genSymbol "while_loop_end"
        // Check the 'while' condition, jump to 'whileEndLabel' if it is false.
        // Here we use a register to load the address of a label (using the
        // instruction LA) and then jump to it (using the instruction LR): this
        // way, the label address can be very far from the jump instruction
        // address --- and this can be important if the compilation of 'body'
        // produces a large amount of assembly code
        Asm(RV.LABEL(whileBeginLabel))
            ++ (doCodegen env cond)
                .AddText([
                    (RV.BNEZ(Reg.r(env.Target), whileBodyBeginLabel),
                     "Jump to loop body if 'while' condition is true")
                    (RV.LA(Reg.r(env.Target), whileEndLabel),
                     "Load address of label at the end of the 'while' loop")
                    (RV.JR(Reg.r(env.Target)), "Jump to the end of the loop")
                    (RV.LABEL(whileBodyBeginLabel),
                     "Body of the 'while' loop starts here")
                ])
            ++ (doCodegen env body)
            .AddText([
                (RV.LA(Reg.r(env.Target), whileBeginLabel),
                 "Load address of label at the beginning of the 'while' loop")
                (RV.JR(Reg.r(env.Target)), "Jump to the end of the loop")
                (RV.LABEL(whileEndLabel), "")
            ])

    | DoWhile(body, cond) ->
        /// Label to mark the beginning of the 'do...while' loop body
        let doWhileBodyBeginLabel = Util.genSymbol "dowhile_body_begin"
        /// Label to mark the beginning of the condition check
        let doWhileCondBeginLabel = Util.genSymbol "dowhile_cond_begin"
        /// Label to mark the end of the 'do...while' loop
        let doWhileEndLabel = Util.genSymbol "dowhile_loop_end"
        Asm(RV.LABEL(doWhileBodyBeginLabel))
            ++ (doCodegen env body)
            .AddText([
                (RV.LA(Reg.r(env.Target), doWhileCondBeginLabel),
                "Load address of label at the condition check of the 'do...while' loop")
                (RV.JR(Reg.r(env.Target)), "Jump to the condition check")
                (RV.LABEL(doWhileCondBeginLabel),
                "Condition of the 'do...while' loop starts here")
            ])
            ++ (doCodegen env cond)
            .AddText([
                (RV.BNEZ(Reg.r(env.Target), doWhileBodyBeginLabel),
                "Jump to loop body if 'do...while' condition is true")
                (RV.LABEL(doWhileEndLabel), "")
            ])
        
    | For(name, init, cond, step, body) ->
        let initCode = doCodegen env init
        
        let loopTarget = env.Target + 1u
        let loopVarStorage = env.VarStorage.Add(name, Storage.Reg(Reg.r(env.Target)))
        let loopEnv = { env with Target = loopTarget; VarStorage = loopVarStorage }

        /// Label to mark the beginning of the 'for' loop
        let forBeginLabel = Util.genSymbol "for_loop_begin"
        /// Label to mark the beginning of the 'for' loop body
        let forBodyBeginLabel = Util.genSymbol "for_body_begin"
        /// Label to mark the end of the 'for' loop
        let forEndLabel = Util.genSymbol "for_loop_end"

        initCode
        ++ Asm(RV.LABEL(forBeginLabel))
            ++ (doCodegen loopEnv cond)
                .AddText([
                    (RV.BNEZ(Reg.r(loopEnv.Target), forBodyBeginLabel),
                    "Jump to loop body if 'for' condition is true")
                    (RV.LA(Reg.r(loopEnv.Target), forEndLabel),
                    "Load address of label at the end of the 'for' loop")
                    (RV.JR(Reg.r(loopEnv.Target)), "Jump to the end of the loop")
                    (RV.LABEL(forBodyBeginLabel),
                    "Body of the 'for' loop starts here")
                ])
            ++ (doCodegen loopEnv body)
            ++ (doCodegen loopEnv step)
            .AddText([
                (RV.LA(Reg.r(loopEnv.Target), forBeginLabel),
                "Load address of label at the beginning of the 'for' loop")
                (RV.JR(Reg.r(loopEnv.Target)), "Jump to the end of the loop")
                (RV.LABEL(forEndLabel), "")
            ])

    | IncDec(op, name) ->
        let isPost = 
            match op with
                | IncDecOp.PostInc | IncDecOp.PostDec -> true
                | _ -> false

        match (env.VarStorage.TryFind name) with
        | Some(Storage.Reg(reg)) ->
            let delta = match op with
                        | IncDecOp.PreInc | IncDecOp.PostInc -> 1
                        | IncDecOp.PreDec | IncDecOp.PostDec -> -1
            Asm([
                if isPost then
                    (RV.MV(Reg.r(env.Target), reg),          "Save original value into target register")
                (RV.ADDI(reg, reg, Imm12(delta)),             "Increment/decrement variable in place")
                if not isPost then
                    (RV.MV(Reg.r(env.Target), reg),          "Move result to target register") ])

        | Some(Storage.FPReg(fpreg)) ->
            let delta = match op with
                        | IncDecOp.PreInc | IncDecOp.PostInc -> 1.0f
                        | IncDecOp.PreDec | IncDecOp.PostDec -> -1.0f
            let deltaWord = floatToWord delta
            Asm([
                if isPost then
                    (RV.FMV_S(FPReg.r(env.FPTarget), fpreg),            "Save original value into target fp register")
                (RV.LI(Reg.r(env.Target), deltaWord),                    "Load delta as IEEE 754")
                (RV.FMV_W_X(FPReg.r(env.FPTarget + 1u), Reg.r(env.Target)), "Move delta to fp register")
                (RV.FADD_S(fpreg, fpreg, FPReg.r(env.FPTarget + 1u)),   "Increment/decrement float variable in place")
                if not isPost then
                    (RV.FMV_S(FPReg.r(env.FPTarget), fpreg),            "Move result to target fp register") ])

        | Some(Storage.Label(lab)) ->
            match node.Type with
            | t when (isSubtypeOf node.Env t TInt) ->
                let delta = match op with
                            | IncDecOp.PreInc | IncDecOp.PostInc -> 1
                            | IncDecOp.PreDec | IncDecOp.PostDec -> -1
                Asm([
                    (RV.LA(Reg.r(env.Target + 2u), lab),                                    $"Load address of variable '%s{name}'")
                    (RV.LW(Reg.r(env.Target + 1u), Imm12(0), Reg.r(env.Target + 2u)),      $"Load value of variable '%s{name}'")
                    (RV.ADDI(Reg.r(env.Target), Reg.r(env.Target + 1u), Imm12(delta)),     "Compute incremented/decremented value")
                    (RV.SW(Reg.r(env.Target), Imm12(0), Reg.r(env.Target + 2u)),           "Store updated value back to memory")
                    if isPost then
                        (RV.MV(Reg.r(env.Target), Reg.r(env.Target + 1u)),                  "Move result to target register") ])
            | t when (isSubtypeOf node.Env t TFloat) ->
                let delta = match op with
                            | IncDecOp.PreInc | IncDecOp.PostInc -> 1.0f
                            | IncDecOp.PreDec | IncDecOp.PostDec -> -1.0f
                let deltaWord = floatToWord delta
                Asm([
                    (RV.LA(Reg.r(env.Target), lab),                                      $"Load address of variable '%s{name}'")
                    (RV.LW(Reg.r(env.Target + 1u), Imm12(0), Reg.r(env.Target)),         $"Load raw bits of variable '%s{name}'")
                    (RV.FMV_W_X(FPReg.r(env.FPTarget), Reg.r(env.Target + 1u)),          "Move original bits to fp register")
                    (RV.LI(Reg.r(env.Target + 1u), deltaWord),                           "Load delta bits")
                    (RV.FMV_W_X(FPReg.r(env.FPTarget + 1u), Reg.r(env.Target + 1u)),    "Move delta bits to fp register")
                    (RV.FADD_S(FPReg.r(env.FPTarget + 1u), FPReg.r(env.FPTarget),
                                FPReg.r(env.FPTarget + 1u)),                              "Compute incremented/decremented float value")
                    (RV.FMV_X_W(Reg.r(env.Target + 1u), FPReg.r(env.FPTarget + 1u)),    "Move updated bits to integer register")
                    (RV.SW(Reg.r(env.Target + 1u), Imm12(0), Reg.r(env.Target)),         $"Store updated float value back to memory")
                    // FPTarget holds original, FPTarget+1 holds new
                    if not isPost then
                        (RV.FMV_S(FPReg.r(env.FPTarget), FPReg.r(env.FPTarget + 1u)),    "Move result to target fp register") ])
            | t -> failwith $"BUG: IncDec on invalid type %O{t}"
        | None -> failwith $"BUG: variable without storage: %s{name}"        
        | Some(value) -> failwith "Not Implemented"


    | Lambda(args, body) ->
        /// Label to mark the position of the lambda term body
        let funLabel = Util.genSymbol "lambda"

        /// Names of the Lambda arguments
        let (argNames, _) = List.unzip args

        /// List of pairs associating each Lambda argument to its type.  We
        /// retrieve the type of each argument by looking into the environment
        /// used to type-check the Lambda 'body'
        let argNamesTypes = List.map (fun a -> (a, body.Env.Vars[a])) argNames

        /// Compiled function body
        let bodyCode = compileFunction argNamesTypes body env

        /// Compiled function code where the function label is located just
        /// before the 'bodyCode', and everything is placed at the end of the
        /// text segment (i.e. in the "PostText")
        let funCode =
            (Asm(RV.LABEL(funLabel), "Lambda term (i.e. function instance) code")
                ++ bodyCode).TextToPostText // Move to the end of text segment

        // Finally, load the function address (label) in the target register
        Asm(RV.LA(Reg.r(env.Target), funLabel), "Load lambda function address")
            ++ funCode

    | Application(expr, args) ->
        /// Integer registers to be saved on the stack before executing the
        /// function call, and restored when the function returns.  The list of
        /// saved registers excludes the target register for this application.
        /// Note: the definition of 'saveRegs' uses list comprehension:
        /// https://en.wikibooks.org/wiki/F_Sharp_Programming/Lists#Using_List_Comprehensions
        let saveRegs =
            List.except [Reg.r(env.Target)]
                        (Reg.ra :: [for i in 0u..7u do yield Reg.a(i)]
                         @ [for i in 0u..6u do yield Reg.t(i)])

        /// Assembly code for the expression being applied as a function
        let appTermCode =
            Asm().AddText(RV.COMMENT("Load expression to be applied as a function"))
            ++ (doCodegen env expr)

        /// Indexed list of argument expressions.
        let indexedArgs: List<int * TypedAST> = List.indexed args

        /// Count how many arguments must be passed on the stack before the call.
        /// Integer and floating-point arguments use separate register counters:
        /// a0-a7 for integers and fa0-fa7 for floats. Only arguments beyond
        /// those limits need stack slots.
        let countStackArgs ((intArgCount, floatArgCount, stackArgCount): int * int * int) (arg: TypedAST) =
            match arg.Type with
            | t when isSubtypeOf arg.Env t TFloat ->
                if floatArgCount < 8 then
                    (intArgCount, floatArgCount + 1, stackArgCount)
                else
                    (intArgCount, floatArgCount + 1, stackArgCount + 1)

            | _ ->
                if intArgCount < 8 then
                    (intArgCount + 1, floatArgCount, stackArgCount)
                else
                    (intArgCount + 1, floatArgCount, stackArgCount + 1)

        let (_, _, stackArgCount) =
            List.fold countStackArgs (0, 0, 0) args

        /// Each Hygge value occupies one word, so each stack argument uses 4 bytes.
        let stackArgBytes = stackArgCount * 4

       /// Compile each argument into reusable temporary registers r(target+1)
        /// or fr(fptarget+1), then immediately move it to the correct argument
        /// register or store it in its stack slot. This avoids needing one
        /// temporary register per argument.
        let compileAndLoadArg
            ((asm, intArgCount, floatArgCount, stackArgCount): Asm * int * int * int)
            ((i, arg): int * TypedAST) =

            match arg.Type with
            | t when isSubtypeOf arg.Env t TFloat ->
                let argCode =
                    doCodegen { env with
                                    Target = env.Target + 1u
                                    FPTarget = env.FPTarget + 1u } arg

                if floatArgCount < 8 then
                    let moveCode =
                        Asm(
                            RV.FMV_S(
                                FPReg.fa(uint floatArgCount),
                                FPReg.r(env.FPTarget + 1u)
                            ),
                            $"Load float function call argument %d{i + 1}"
                        )

                    (asm ++ argCode ++ moveCode,
                    intArgCount,
                    floatArgCount + 1,
                    stackArgCount)
                else
                    let offset = stackArgCount * 4

                    let storeCode =
                        Asm(
                            RV.FSW_S(
                                FPReg.r(env.FPTarget + 1u),
                                Imm12(offset),
                                Reg.sp
                            ),
                            $"Store float function call stack argument %d{i + 1}"
                        )

                    (asm ++ argCode ++ storeCode,
                    intArgCount,
                    floatArgCount + 1,
                    stackArgCount + 1)

            | _ ->
                let argCode =
                    doCodegen { env with
                                    Target = env.Target + 1u } arg

                if intArgCount < 8 then
                    let moveCode =
                        Asm(
                            RV.MV(
                                Reg.a(uint intArgCount),
                                Reg.r(env.Target + 1u)
                            ),
                            $"Load integer function call argument %d{i + 1}"
                        )

                    (asm ++ argCode ++ moveCode,
                    intArgCount + 1,
                    floatArgCount,
                    stackArgCount)
                else
                    let offset = stackArgCount * 4

                    let storeCode =
                        Asm(
                            RV.SW(
                                Reg.r(env.Target + 1u),
                                Imm12(offset),
                                Reg.sp
                            ),
                            $"Store integer function call stack argument %d{i + 1}"
                        )

                    (asm ++ argCode ++ storeCode,
                    intArgCount + 1,
                    floatArgCount,
                    stackArgCount + 1)

        let (argsCode, _, _, _) =
            List.fold compileAndLoadArg (Asm(), 0, 0, 0) indexedArgs

        let allocateStackArgs =
            if stackArgBytes = 0 then
                Asm()
            else
                Asm(RV.ADDI(Reg.sp, Reg.sp, Imm12(-stackArgBytes)),
                    "Allocate stack space for function call arguments")

        let freeStackArgs =
            if stackArgBytes = 0 then
                Asm()
            else
                Asm(RV.ADDI(Reg.sp, Reg.sp, Imm12(stackArgBytes)),
                    "Free stack space for function call arguments")

        /// The stack space for overflow arguments must be allocated before
        /// argsCode runs, because argsCode stores stack-passed arguments at
        /// offsets from sp.
        let callCode =
            appTermCode
               .AddText(RV.COMMENT("Before function call: save caller-saved registers"))
               ++ (saveRegisters saveRegs [])
               ++ allocateStackArgs
               ++ argsCode // Code to load arg values into arg registers
               .AddText(RV.JALR(Reg.ra, Imm12(0), Reg.r(env.Target)), "Function call")
               ++ freeStackArgs

        /// Code that handles the function return value (if any)
        let retCode =
            match node.Type with
            | t when isSubtypeOf node.Env t TFloat ->
                Asm(RV.FMV_S(FPReg.r(env.FPTarget), FPReg.fa0),
                    "Copy float function return value to target register")
            | t when isSubtypeOf node.Env t TUnit ->
                Asm()
            | _ ->
                Asm(RV.MV(Reg.r(env.Target), Reg.a0),
                    "Copy function return value to target register")

        // Put everything together, and restore the caller-saved registers
        callCode
            .AddText(RV.COMMENT("After function call"))
            ++ retCode
            .AddText(RV.COMMENT("Restore caller-saved registers"))
                  ++ (restoreRegisters saveRegs [])

    | StructCons(fields) ->
        // To compile a structure constructor, we allocate heap space for the
        // whole struct instance, and then compile its field initialisations
        // one-by-one, storing each result in the corresponding heap location.
        // The struct heap address will end up in the 'target' register - i.e.
        // the register will contain a pointer to the first element of the
        // allocated structure
        let (fieldNames, fieldInitNodes) = List.unzip fields
        /// Generate the code that initialises a struct field, and accumulates
        /// the result.  This function is folded over all indexed struct fields,
        /// to produce the assembly code that initialises all fields.
        let folder = fun (acc: Asm) (fieldOffset: int, fieldInit: TypedAST) ->
            /// Code that initialises a single struct field.  Each field init
            /// result is compiled by targeting the register (target+1u),
            /// because the 'target' register holds the base memory address of
            /// the struct.  After the init result for a field is computed, we
            /// copy it into its heap location, by adding the field offset
            /// (multiplied by 4, i.e. the word size) to the base struct address
            let fieldInitCode: Asm =
                match fieldInit.Type with
                | t when (isSubtypeOf fieldInit.Env t TUnit) ->
                    Asm() // Nothing to do
                | t when (isSubtypeOf fieldInit.Env t TFloat) ->
                    Asm(RV.FSW_S(FPReg.r(env.FPTarget), Imm12(fieldOffset * 4),
                                 Reg.r(env.Target)),
                        $"Initialize struct field '%s{fieldNames.[fieldOffset]}'")
                | _ ->
                    Asm(RV.SW(Reg.r(env.Target + 1u), Imm12(fieldOffset * 4),
                              Reg.r(env.Target)),
                        $"Initialize struct field '%s{fieldNames.[fieldOffset]}'")
            acc ++ (doCodegen {env with Target = env.Target + 1u} fieldInit)
                ++ fieldInitCode
        /// Assembly code for initialising each field of the struct, by folding
        /// the 'folder' function above over all indexed struct fields (we use
        /// the index to know the offset of a field from the beginning of the
        /// struct)
        let fieldsInitCode =
            List.fold folder (Asm()) (List.indexed fieldInitNodes)

        /// Assembly code that allocates space on the heap for the new
        /// structure, through an 'Sbrk' system call.  The size of the structure
        /// is computed by multiplying the number of fields by the word size (4)
        let structAllocCode =
            (beforeSysCall [Reg.a0] [])
                .AddText([
                    (RV.LI(Reg.a0, fields.Length * 4),
                     "Amount of memory to allocate for a struct (in bytes)")
                    (RV.LI(Reg.a7, 9), "RARS syscall: Sbrk")
                    (RV.ECALL, "")
                    (RV.MV(Reg.r(env.Target), Reg.a0),
                     "Move syscall result (struct mem address) to target")
                ])
                ++ (afterSysCall [Reg.a0] [])

        // Put everything together: allocate heap space, init all struct fields
        structAllocCode ++ fieldsInitCode

    | FieldSelect(target, field) ->
        // To compile a field selection, we first execute the 'target' object of
        // the field selection, whose code is expected to leave a struct memory
        // address in the environment's 'target' register; then use the 'target'
        // type to determine the memory offset where the selected field is
        // located, and retrieve its value.

        /// Generated code for the target object whose field is being selected
        let selTargetCode = doCodegen env target
        /// Assembly code to access the struct field in memory (depending on the
        /// 'target' type) and leave its value in the target register
        let fieldAccessCode =
            match (expandType node.Env target.Type) with
            | TStruct(fields) ->
                let (fieldNames, fieldTypes) = List.unzip fields
                let offset = List.findIndex (fun f -> f = field) fieldNames
                match fieldTypes.[offset] with
                | t when (isSubtypeOf node.Env t TUnit) ->
                    Asm() // Nothing to do
                | t when (isSubtypeOf node.Env t TFloat) ->
                    Asm(RV.FLW_S(FPReg.r(env.FPTarget), Imm12(offset * 4),
                                 Reg.r(env.Target)),
                        $"Retrieve value of struct field '%s{field}'")
                | _ ->
                    Asm(RV.LW(Reg.r(env.Target), Imm12(offset * 4),
                              Reg.r(env.Target)),
                        $"Retrieve value of struct field '%s{field}'")
            | t ->
                failwith $"BUG: FieldSelect codegen on invalid target type: %O{t}"

        // Put everything together: compile the target, access the field
        selTargetCode ++ fieldAccessCode

    | Pointer(_) ->
        failwith "BUG: pointers cannot be compiled (by design!)"
    | ArrayCons(size, init) ->
        /// Compile size first to have it available and keep it in r(Target)
        let compiledSize = doCodegen env size
        
        /// Allocate heap space for the array: size+1 elements (first for length)
        let sizeAllocCode =
            (beforeSysCall [Reg.a0] [])
                .AddText([
                    RV.ADDI(Reg.a0, Reg.r(env.Target), Imm12(1)), "a0 = size + 1"
                    RV.SLLI(Reg.a0, Reg.a0, Shamt(2u)), "a0 = (size + 1) * 4 bytes"
                    RV.LI(Reg.a7, 9), "RARS syscall: Sbrk"
                    RV.ECALL, ""
                    RV.MV(Reg.r(env.Target + 1u), Reg.a0),
                    "Move syscall result (array mem address) to target+1"
                ])
                ++ afterSysCall [Reg.a0] []
        
        /// Store the size at offset 0
        let storeSizeCode =
            Asm(RV.SW(Reg.r(env.Target), Imm12(0), Reg.r(env.Target + 1u)),
                "Store array size at offset 0")
        
        /// Compile init to target+2u (so it won't overwrite size in r(Target))
        let initCode =
            doCodegen {env with Target = env.Target + 2u} init
        
        /// Create a loop to initialize all elements starting at offset 4
        let loopLabel = Util.genSymbol "array_init_loop"
        let loopEndLabel = Util.genSymbol "array_init_end"
        let initLoopCode =
            Asm(RV.LI(Reg.r(env.Target + 3u), 0), "Initialize loop counter to 0")
                .AddText(RV.LABEL(loopLabel), "Array initialization loop")
                .AddText(RV.BEQ(Reg.r(env.Target + 3u), Reg.r(env.Target), loopEndLabel),
                         "Exit loop when counter == size")
                .AddText([
                    RV.ADDI(Reg.r(env.Target + 4u), Reg.r(env.Target + 3u), Imm12(1)), "offset = counter + 1"
                    RV.SLLI(Reg.r(env.Target + 4u), Reg.r(env.Target + 4u), Shamt(2u)), "offset = offset * 4"
                    RV.ADD(Reg.r(env.Target + 4u), Reg.r(env.Target + 1u), Reg.r(env.Target + 4u)), "address = base + offset"
                ])
                .AddText([
                    match init.Type with
                    | t when isSubtypeOf init.Env t TUnit ->
                        RV.NOP, ""
                    | t when isSubtypeOf init.Env t TFloat ->
                        RV.FSW_S(FPReg.r env.FPTarget, Imm12 0, Reg.r(env.Target + 4u)),
                        "Store init value (float)"
                    | _ ->
                        RV.SW(Reg.r(env.Target + 2u), Imm12 0, Reg.r(env.Target + 4u)),
                        "Store init value"
                ])
                .AddText([
                    RV.ADDI(Reg.r(env.Target + 3u), Reg.r(env.Target + 3u), Imm12(1)), "counter++"
                    RV.LA(Reg.r(env.Target + 4u), loopLabel), "Load loop start address"
                    RV.JR(Reg.r(env.Target + 4u)), "Jump to loop start"
                ])
                .AddText(RV.LABEL loopEndLabel, "End of array initialization")
        
        compiledSize ++ sizeAllocCode ++ storeSizeCode ++ initCode ++ initLoopCode
            .AddText(RV.MV(Reg.r env.Target, Reg.r(env.Target + 1u)),
                     "Move array pointer result to target register")

    | ArrayElem(array, index) ->
        /// Compile array expression to get pointer in target
        let arrayCode = doCodegen env array
        /// Compile index to target+1
        let indexCode =
            (doCodegen {env with Target = env.Target + 1u} index)
                .AddText(RV.MV(Reg.r(env.Target + 2u), Reg.r(env.Target + 1u)),
                         "Save index to a temporary register")
        
        /// Calculate address: base + 4 + index*4 = base + 4*(1+index)
        let addrCalcCode =
            Asm([
                (RV.ADDI(Reg.r(env.Target + 2u), Reg.r(env.Target + 2u), Imm12(1)), "offset_index = 1 + index")
                (RV.SLLI(Reg.r(env.Target + 2u), Reg.r(env.Target + 2u), Shamt(2u)), "offset_index = offset_index * 4")
                (RV.ADD(Reg.r(env.Target + 2u), Reg.r(env.Target), Reg.r(env.Target + 2u)), "element_addr = base + offset")
            ])
        
        /// Load the element from memory at the computed address
        let loadElemCode =
            match node.Type with
            | t when (isSubtypeOf node.Env t TUnit) ->
                Asm()
            | t when (isSubtypeOf node.Env t TFloat) ->
                Asm(RV.FLW_S(FPReg.r(env.FPTarget), Imm12(0), Reg.r(env.Target + 2u)),
                    "Load array element (float)")
            | _ ->
                Asm(RV.LW(Reg.r(env.Target), Imm12(0), Reg.r(env.Target + 2u)),
                    "Load array element")
        
        arrayCode ++ indexCode ++ addrCalcCode ++ loadElemCode

    | ArrayLength(array) ->
        /// Compile array expression to get pointer in target
        let arrayCode = doCodegen env array
        /// Load length from offset 0
        let lengthCode =
            Asm(RV.LW(Reg.r(env.Target), Imm12(0), Reg.r(env.Target)),
                "Load array length from offset 0")
        
        arrayCode ++ lengthCode

    | Copy(target) -> 
        let targetCode = doCodegen env target
        match (expandType node.Env target.Type) with
        | TStruct(fields) ->

            let structAllocCode =
                Asm(RV.MV(Reg.r(env.Target + 1u), Reg.r(env.Target)),
                    "Save source struct address for copy")
                ++ (beforeSysCall [Reg.r(env.Target + 1u)] [])
                    .AddText([
                        (RV.LI(Reg.a0, fields.Length * 4),
                         "Amount of memory to allocate for a copied struct (in bytes)")
                        (RV.LI(Reg.a7, 9), "RARS syscall: Sbrk")
                        (RV.ECALL, "")
                        (RV.MV(Reg.r(env.Target), Reg.a0),
                         "Move syscall result (copied struct mem address) to target")
                    ])
                    ++ (afterSysCall [Reg.r(env.Target + 1u)] [])

            // lw env.Target + 2u, offset(env.Target + 1u)  
            // sw env.Target + 2u, offset(env.Target)
            let copyField (acc: Asm) (fieldOffset: int, _) =
                acc.AddText([
                    (RV.LW(Reg.r(env.Target + 2u), Imm12(fieldOffset * 4),
                           Reg.r(env.Target + 1u)),
                     $"Load copied struct field at offset %d{fieldOffset}")
                    (RV.SW(Reg.r(env.Target + 2u), Imm12(fieldOffset * 4),
                           Reg.r(env.Target)),
                     $"Store copied struct field at offset %d{fieldOffset}")
                ])
            let fieldsCopyCode =
                List.fold copyField (Asm()) (List.indexed fields)

            targetCode ++ structAllocCode ++ fieldsCopyCode
        | (t: Type) ->
            failwith $"BUG: copy codegen on invalid target type: %O{t}"

    | DeepCopy(target) ->
        match (expandType node.Env target.Type) with
        | TStruct(fields) ->
            doCodegen env target
            let tmpName = Util.genSymbol "__deepcopy_target"
            let tmpVar = { target with Expr = Var(tmpName) }

            let mkFieldNode (fieldName, fieldType) =
                let fieldSelect: TypedAST =
                    { Pos = node.Pos
                      Env = node.Env
                      Type = fieldType
                      Expr = FieldSelect(tmpVar, fieldName) }
                
                let fieldInit =
                    match (expandType node.Env fieldType) with
                    | TStruct(_) -> 
                        let structExpr = DeepCopy(fieldSelect)
                        ({ Pos = node.Pos
                           Env = node.Env
                           Type = fieldType
                           Expr = structExpr
                        }: TypedAST)
                    | _ -> fieldSelect
                
                (fieldName, fieldInit)

            let newFields = List.map mkFieldNode fields
            let copiedStruct: TypedAST =
                { Pos = node.Pos
                  Env = node.Env
                  Type = target.Type
                  Expr = StructCons(newFields)
                }

            let lowered: TypedAST =
                { Pos = node.Pos
                  Env = node.Env
                  Type = target.Type
                  Expr = Let(tmpName, target, copiedStruct) }

            doCodegen env lowered
        | (t: Type) ->
            failwith $"BUG: deepcopy codegen on invalid target type: %O{t}"    
    | UnionCons(label, expr) -> failwith "Not Implemented"
    | Match(expr, cases) -> failwith "Not Implemented"

/// Escape a string so it can be shown inside the compile-time rendering of a
/// failed assertion expression.
and internal escapeAssertionString (s: string): string =
    s.Replace("\\", "\\\\")
     .Replace("\n", "\\n")
     .Replace("\r", "\\r")
     .Replace("\t", "\\t")
     .Replace("\"", "\\\"")

/// Return a compact, source-like rendering of an expression for assertion
/// diagnostics.  The original source text is not stored in the AST, so this is
/// intentionally a readable reconstruction from the typed AST.
and internal formatAssertionExpr (node: TypedAST): string =
    let par (n: TypedAST) = $"(%s{formatAssertionExpr n})"
    match node.Expr with
    | UnitVal -> "()"
    | BoolVal(v) -> if v then "true" else "false"
    | IntVal(v) -> string v
    | FloatVal(v) -> string v
    | StringVal(v) -> $"\"%s{escapeAssertionString v}\""
    | Var(name) -> name
    | BinNumOp(op, lhs, rhs) ->
        let opStr =
            match op with
            | NumericalOp.Add -> "+"
            | NumericalOp.Sub -> "-"
            | NumericalOp.Mult -> "*"
            | NumericalOp.Div -> "/"
            | NumericalOp.Mod -> "%"
        $"%s{par lhs} %s{opStr} %s{par rhs}"
    | BinLogicOp(op, lhs, rhs) ->
        let opStr =
            match op with
            | LogicOp.And -> "&"
            | LogicOp.Or -> "|"
            | LogicOp.Xor -> "^"
            | LogicOp.AndS -> "&&"
            | LogicOp.OrS -> "||"
        $"%s{par lhs} %s{opStr} %s{par rhs}"
    | Not(arg) -> $"not %s{par arg}"
    | BinRelOp(op, lhs, rhs) ->
        let opStr =
            match op with
            | RelationalOp.Eq -> "="
            | RelationalOp.Less -> "<"
            | RelationalOp.LessEq -> "<="
            | RelationalOp.Greater -> ">"
        $"%s{par lhs} %s{opStr} %s{par rhs}"
    | ReadInt -> "readInt()"
    | ReadFloat -> "readFloat()"
    | Print(arg) -> $"print(%s{formatAssertionExpr arg})"
    | PrintLn(arg) -> $"println(%s{formatAssertionExpr arg})"
    | If(cond, ifTrue, ifFalse) ->
        $"if %s{formatAssertionExpr cond} then %s{formatAssertionExpr ifTrue} else %s{formatAssertionExpr ifFalse}"
    | Seq(nodes) ->
        nodes |> List.map formatAssertionExpr |> String.concat "; " |> sprintf "{%s}"
    | Type(name, _, scope) -> $"type %s{name}; %s{formatAssertionExpr scope}"
    | Ascription(_, expr) -> formatAssertionExpr expr
    | Assertion(arg) -> $"assert(%s{formatAssertionExpr arg})"
    | Let(name, init, scope)
    | LetT(name, _, init, scope) ->
        $"let %s{name} = %s{formatAssertionExpr init}; %s{formatAssertionExpr scope}"
    | LetMut(name, init, scope) ->
        $"let mutable %s{name} = %s{formatAssertionExpr init}; %s{formatAssertionExpr scope}"
    | Assign(lhs, rhs) -> $"%s{formatAssertionExpr lhs} <- %s{formatAssertionExpr rhs}"
    | While(cond, body) -> $"while %s{formatAssertionExpr cond} do %s{formatAssertionExpr body}"
    | DoWhile(body, cond) -> $"do %s{formatAssertionExpr body} while %s{formatAssertionExpr cond}"
    | For(name, init, cond, step, body) ->
        $"for %s{name} = %s{formatAssertionExpr init}; %s{formatAssertionExpr cond}; %s{formatAssertionExpr step} do %s{formatAssertionExpr body}"
    | Lambda(args, body) ->
        let argNames = args |> List.map fst |> String.concat ", "
        $"fun (%s{argNames}) -> %s{formatAssertionExpr body}"
    | Application(expr, args) ->
        let argsStr = args |> List.map formatAssertionExpr |> String.concat ", "
        $"%s{formatAssertionExpr expr}(%s{argsStr})"
    | StructCons(fields) ->
        fields
        |> List.map (fun (field, expr) -> $"%s{field} = %s{formatAssertionExpr expr}")
        |> String.concat "; "
        |> sprintf "struct {%s}"
    | FieldSelect(target, field) -> $"%s{formatAssertionExpr target}.%s{field}"
    | Sqrt(arg) ->
        $"sqrt(%s{formatAssertionExpr arg})"
    | ArrayCons(size, init) ->
        $"array(%s{formatAssertionExpr size}, %s{formatAssertionExpr init})"
    | ArrayElem(array, index) ->
        $"%s{formatAssertionExpr array}[%s{formatAssertionExpr index}]"
    | ArrayLength(array) ->
        $"%s{formatAssertionExpr array}.length"
    | Copy(target) ->
        $"copy(%s{formatAssertionExpr target})"
    | DeepCopy(target) ->
        $"deepcopy(%s{formatAssertionExpr target})"
    | Pointer(addr) -> $"<pointer 0x%x{addr}>"
    | UnionCons(label, expr) -> $"%s{label}(%s{formatAssertionExpr expr})"
    | Match(expr, _) -> $"match %s{formatAssertionExpr expr} with ..."    
    | IncDec(op, name) -> $"{op}({name})"

/// Generate code that prints a fixed string through the RARS PrintString
/// syscall.  The string is allocated in the data segment.
and internal printStringLiteral (s: string): Asm =
    let label = Util.genSymbol "assert_diag_str"
    Asm().AddData(label, Alloc.String(escapeAssertionString s))
    ++ (beforeSysCall [Reg.a0] [])
        .AddText([
            (RV.LA(Reg.a0, label), "Load assertion diagnostic string")
            (RV.LI(Reg.a7, 4), "RARS syscall: PrintString")
            (RV.ECALL, "")
        ])
        ++ (afterSysCall [Reg.a0] [])

/// Generate code that prints a boolean value held in the given register.
and internal printBoolReg (reg: Reg): Asm =
    let trueLabel = Util.genSymbol "assert_bool_true"
    let endLabel = Util.genSymbol "assert_bool_end"
    let trueStr = Util.genSymbol "assert_true_str"
    let falseStr = Util.genSymbol "assert_false_str"
    Asm().AddData(trueStr, Alloc.String("true"))
         .AddData(falseStr, Alloc.String("false"))
    ++ (beforeSysCall [Reg.a0] [])
        .AddText([
            (RV.BNEZ(reg, trueLabel), "Assertion diagnostic: boolean is true")
            (RV.LA(Reg.a0, falseStr), "String to print via syscall")
            (RV.J(endLabel), "")
            (RV.LABEL(trueLabel), "")
            (RV.LA(Reg.a0, trueStr), "String to print via syscall")
            (RV.LABEL(endLabel), "")
            (RV.LI(Reg.a7, 4), "RARS syscall: PrintString")
            (RV.ECALL, "")
        ])
        ++ (afterSysCall [Reg.a0] [])

/// Generate code that prints an integer-like value held in a register according
/// to the given Hygge type.  For structure types, the register is interpreted as
/// a heap pointer to the structure.
and internal printValueReg (env: TypingEnv) (reg: Reg) (tpe: Type) (depth: int): Asm =
    match expandType env tpe with
    | t when (isSubtypeOf env t TUnit) -> printStringLiteral "()"
    | t when (isSubtypeOf env t TBool) -> printBoolReg reg
    | t when (isSubtypeOf env t TInt) ->
        (beforeSysCall [Reg.a0] [])
            .AddText([
                (RV.MV(Reg.a0, reg), "Copy assertion diagnostic int to a0")
                (RV.LI(Reg.a7, 1), "RARS syscall: PrintInt")
                (RV.ECALL, "")
            ])
            ++ (afterSysCall [Reg.a0] [])
    | t when (isSubtypeOf env t TString) ->
        printStringLiteral "\""
        ++ (beforeSysCall [Reg.a0] [])
            .AddText([
                (RV.MV(Reg.a0, reg), "Copy assertion diagnostic string pointer to a0")
                (RV.LI(Reg.a7, 4), "RARS syscall: PrintString")
                (RV.ECALL, "")
            ])
            ++ (afterSysCall [Reg.a0] [])
        ++ (printStringLiteral "\"")
    | TFun(_, _) -> printStringLiteral "<function>"
    | TStruct(fields) -> printStructReg env reg fields depth
    | TUnion(_) -> printStringLiteral "<union>"
    | TVar(name) -> printStringLiteral $"<value of unresolved type %s{name}>"
    | TFloat -> failwith "BUG: float values must be printed through printFloatReg"
    | TArray(_) -> printStringLiteral "<array>"

/// Generate code that prints a floating-point value held in the given register.
and internal printFloatReg (fpreg: FPReg): Asm =
    (beforeSysCall [] [FPReg.fa0])
        .AddText([
            (RV.FMV_S(FPReg.fa0, fpreg), "Copy assertion diagnostic float to fa0")
            (RV.LI(Reg.a7, 2), "RARS syscall: PrintFloat")
            (RV.ECALL, "")
        ])
        ++ (afterSysCall [] [FPReg.fa0])

/// Generate code that prints a structure value.  The given register must hold
/// the heap address of the first field of the structure.
and internal printStructReg (env: TypingEnv) (baseReg: Reg) (fields: List<string * Type>) (depth: int): Asm =
    if depth <= 0 then
        printStringLiteral "{...}"
    else
        let valueReg = if baseReg = Reg.t(6u) then Reg.t(5u) else Reg.t(6u)
        let printField (acc: Asm) (i: int, (fieldName: string, fieldType: Type)) =
            let separator = if i = 0 then "" else "; "
            let prefix = $"%s{separator}%s{fieldName} = "
            let fieldAsm =
                match expandType env fieldType with
                | t when (isSubtypeOf env t TUnit) ->
                    printStringLiteral "()"
                | t when (isSubtypeOf env t TFloat) ->
                    (beforeSysCall [Reg.a0] [FPReg.fa0])
                        .AddText([
                            (RV.FLW_S(FPReg.fa0, Imm12(i * 4), baseReg),
                             $"Load float field '%s{fieldName}' for assertion diagnostic")
                            (RV.LI(Reg.a7, 2), "RARS syscall: PrintFloat")
                            (RV.ECALL, "")
                        ])
                        ++ (afterSysCall [Reg.a0] [FPReg.fa0])
                | t ->
                    Asm(RV.LW(valueReg, Imm12(i * 4), baseReg),
                        $"Load field '%s{fieldName}' for assertion diagnostic")
                    ++ (saveRegisters [baseReg] [])
                    ++ (printValueReg env valueReg t (depth - 1))
                    ++ (restoreRegisters [baseReg] [])
            acc ++ (printStringLiteral prefix) ++ fieldAsm

        printStringLiteral "{"
        ++ (List.fold printField (Asm()) (List.indexed fields))
        ++ (printStringLiteral "}")

/// Generate code that prints the current runtime value of a variable involved
/// in a failed assertion.
and internal codegenAssertionValue (env: CodegenEnv) (typeEnv: TypingEnv) (name: string): Asm =
    match typeEnv.Vars.TryFind name with
    | None -> printStringLiteral $"%s{name} = <not in typing environment>\n"
    | Some(tpe) ->
        let header = printStringLiteral $"%s{name} = "
        let valueCode =
            match expandType typeEnv tpe with
            | t when (isSubtypeOf typeEnv t TUnit) -> printStringLiteral "()"
            | t when (isSubtypeOf typeEnv t TFloat) ->
                match env.VarStorage.TryFind name with
                | Some(Storage.FPReg(fpreg)) -> printFloatReg fpreg
                | Some(Storage.Label(lab)) ->
                    (beforeSysCall [Reg.a0] [FPReg.fa0])
                        .AddText([
                            (RV.LA(Reg.a0, lab), $"Load address of variable '%s{name}'")
                            (RV.FLW_S(FPReg.fa0, Imm12(0), Reg.a0),
                             $"Load float value of variable '%s{name}'")
                            (RV.LI(Reg.a7, 2), "RARS syscall: PrintFloat")
                            (RV.ECALL, "")
                        ])
                        ++ (afterSysCall [Reg.a0] [FPReg.fa0])
                | Some(Storage.Reg(_)) as st ->
                    failwith $"BUG: float variable %s{name} has unexpected storage %O{st}"
                | None -> printStringLiteral "<not stored>"                
                | Some(value) -> failwith "Not Implemented"
            | t ->
                match env.VarStorage.TryFind name with
                | Some(Storage.Reg(reg)) -> printValueReg typeEnv reg t assertStructPrintDepth
                | Some(Storage.Label(lab)) ->
                    match t with
                    | TFun(_, _) -> printStringLiteral "<function>"
                    | _ ->
                        let scratch = Reg.t(5u)
                        Asm([
                            (RV.LA(scratch, lab), $"Load address of variable '%s{name}'")
                            (RV.LW(scratch, Imm12(0), scratch),
                             $"Load value of variable '%s{name}'")
                        ])
                        ++ (printValueReg typeEnv scratch t assertStructPrintDepth)
                | Some(Storage.FPReg(_)) as st ->
                    failwith $"BUG: non-float variable %s{name} has unexpected storage %O{st}"
                | None -> printStringLiteral "<not stored>"                
                | Some(value) -> failwith "Not Implemented"
        header
        ++ (saveRegisters [Reg.t(5u); Reg.t(6u)] [])
        ++ valueCode
        ++ (restoreRegisters [Reg.t(5u); Reg.t(6u)] [])
        ++ (printStringLiteral "\n")

/// Generate code that prints all assertion-value diagnostics.
and internal codegenAssertionValues (env: CodegenEnv) (assertExpr: TypedAST) (names: List<string>): Asm =
    match names with
    | [] -> printStringLiteral "values: none\n"
    | _ ->
        printStringLiteral "values:\n"
        ++ (List.fold (fun acc name ->
                acc ++ (printStringLiteral "  ")
                    ++ (codegenAssertionValue env assertExpr.Env name))
                (Asm()) names)

/// Generate code to save the given registers on the stack, before a RARS system
/// call. Register a7 (which holds the system call number) is backed-up by
/// default, so it does not need to be specified when calling this function.
and internal beforeSysCall (regs: List<Reg>) (fpregs: List<FPReg>): Asm =
    Asm(RV.COMMENT("Before system call: save registers"))
        ++ (saveRegisters (Reg.a7 :: regs) fpregs)

/// Generate code to restore the given registers from the stack, after a RARS
/// system call. Register a7 (which holds the system call number) is restored
/// by default, so it does not need to be specified when calling this function.
and internal afterSysCall (regs: List<Reg>) (fpregs: List<FPReg>): Asm =
    Asm(RV.COMMENT("After system call: restore registers"))
        ++ (restoreRegisters (Reg.a7 :: regs) fpregs)

/// Generate code to save the given lists of registers by using increasing
/// offsets from the stack pointer register (sp).
and internal saveRegisters (rs: List<Reg>) (fprs: List<FPReg>): Asm =
    /// Generate code to save standard registers by folding over indexed 'rs'
    let regSave (asm: Asm) (i, r) = asm.AddText(RV.SW(r, Imm12(i * 4), Reg.sp))
    /// Code to save standard registers
    let rsSaveAsm = List.fold regSave (Asm()) (List.indexed rs)

    /// Generate code to save floating point registers by folding over indexed
    /// 'fprs', and accumulating code on top of 'rsSaveAsm' above. Notice that
    /// we use the length of 'rs' as offset for saving on the stack, since those
    /// stack locations are already used to save 'rs' above.
    let fpRegSave (asm: Asm) (i, r) =
        asm.AddText(RV.FSW_S(r, Imm12((i + rs.Length) * 4), Reg.sp))
    /// Code to save both standard and floating point registers
    let regSaveCode = List.fold fpRegSave rsSaveAsm (List.indexed fprs)

    // Put everything together: update the stack pointer and save the registers
    Asm(RV.ADDI(Reg.sp, Reg.sp, Imm12(-4 * (rs.Length + fprs.Length))),
        "Update stack pointer to make room for saved registers")
      ++ regSaveCode

/// Generate code to restore the given lists of registers, that are assumed to
/// be saved with increasing offsets from the stack pointer register (sp)
and internal restoreRegisters (rs: List<Reg>) (fprs: List<FPReg>): Asm =
    /// Generate code to restore standard registers by folding over indexed 'rs'
    let regLoad (asm: Asm) (i, r) = asm.AddText(RV.LW(r, Imm12(i * 4), Reg.sp))
    /// Code to restore standard registers
    let rsLoadAsm = List.fold regLoad (Asm()) (List.indexed rs)

    /// Generate code to restore floating point registers by folding over
    /// indexed 'fprs', and accumulating code on top of 'rsLoadAsm' above.
    /// Notice that we use the length of 'rs' as offset for saving on the stack,
    /// since those stack locations are already used to save 'rs' above.
    let fpRegLoad (asm: Asm) (i, r) =
        asm.AddText(RV.FLW_S(r, Imm12((i + rs.Length) * 4), Reg.sp))
    /// Code to restore both standard and floating point registers
    let regRestoreCode = List.fold fpRegLoad rsLoadAsm (List.indexed fprs)

    // Put everything together: restore the registers and then the stack pointer
    regRestoreCode
        .AddText(RV.ADDI(Reg.sp, Reg.sp, Imm12(4 * (rs.Length + fprs.Length))),
                 "Restore stack pointer after register restoration")

/// Compile a function instance with the given (optional) name, arguments, and
/// body, and using the given environment.  This function places all the
/// assembly code it generates in the Text segment (hence, this code may need
/// to be moved afterwards).
and internal compileFunction (args: List<string * Type>)
                             (body: TypedAST)
                             (env: CodegenEnv): Asm =
    /// List of indexed arguments: we use the index as the number of the 'a'
    /// register that holds the argument
    let indexedArgs = List.indexed args
    /// Folder function that assigns storage information to function arguments.
    /// The first 8 integer-like arguments are stored in RISC-V argument
    /// registers a0-a7. Any further integer-like arguments are stored on the
    /// caller's stack frame and accessed through offsets from fp.
    let folder ((acc, intArgCount, floatArgCount, stackArgCount): Map<string, Storage> * int * int * int)
           (var, tpe) =

        if isSubtypeOf body.Env tpe TFloat then
            if floatArgCount  < 8 then
                let storage = Storage.FPReg(FPReg.fa(uint floatArgCount))
                (acc.Add(var, storage), intArgCount, floatArgCount + 1, stackArgCount)
            else
                let offset = stackArgCount * 4
                let storage = Storage.Frame(offset)
                (acc.Add(var, storage), intArgCount, floatArgCount + 1, stackArgCount + 1)
        else
            if intArgCount < 8 then
                let storage = Storage.Reg(Reg.a(uint intArgCount))
                (acc.Add(var, storage), intArgCount + 1, floatArgCount, stackArgCount)
            else
                let offset = stackArgCount * 4
                let storage = Storage.Frame(offset)
                (acc.Add(var, storage), intArgCount + 1, floatArgCount, stackArgCount + 1)

    /// Updated storage information including function arguments, where arguments
    /// above the 8th integer-like argument are mapped to stack frame locations.
    let (varStorage2, _, _, _) =
        List.fold folder (env.VarStorage, 0, 0, 0) args

    /// Code for the body of the function, using the newly-created
    /// variable storage mapping 'varStorage2'.  NOTE: the function body
    /// compilation restarts the target register numbers from 0.  Consequently,
    /// the function body result (i.e. the function return value) will be stored
    /// in Reg.r(0) or FPReg.r(0) (depending on its type); when the function
    /// ends, we need to move that result into the function return value
    /// register 'a0' or 'fa0'.
    let bodyCode =
        let env = {Target = 0u; FPTarget = 0u; VarStorage = varStorage2}
        doCodegen env body
    /// Code to move the body result into the function return value register
    let returnCode =
        match body.Type with
        | t when isSubtypeOf body.Env t TFloat ->
            Asm(RV.FMV_S(FPReg.fa0, FPReg.r(0u)),
                "Move float result of function into return value register")
        | t when isSubtypeOf body.Env t TUnit ->
            Asm()
        | _ ->
            Asm(RV.MV(Reg.a0, Reg.r(0u)),
                "Move result of function into return value register")

    /// Integer registers to save before executing the function body.
    /// Note: the definition of 'saveRegs' uses list comprehension:
    /// https://en.wikibooks.org/wiki/F_Sharp_Programming/Lists#Using_List_Comprehensions
    let saveRegs = [for i in 0u..11u do yield Reg.s(i)]

    // Finally, we put together the full code for the function
    Asm(RV.COMMENT("Funtion prologue begins here"))
            .AddText(RV.COMMENT("Save callee-saved registers"))
        ++ (saveRegisters saveRegs [])
            .AddText(RV.ADDI(Reg.fp, Reg.sp, Imm12(saveRegs.Length * 4)),
                     "Update frame pointer for the current function")
            .AddText(RV.COMMENT("End of function prologue.  Function body begins"))
        ++ bodyCode
            .AddText(RV.COMMENT("End of function body.  Function epilogue begins"))
        ++ returnCode
            .AddText(RV.COMMENT("Restore callee-saved registers"))
            ++ (restoreRegisters saveRegs [])
                .AddText(RV.JR(Reg.ra), "End of function, return to caller")


/// Generate RISC-V assembly for the given AST.
let codegen (node: TypedAST): RISCV.Asm =
    /// Initial codegen environment, targeting generic registers 0 and without
    /// any variable in the storage map
    let env = {Target = 0u; FPTarget = 0u; VarStorage =  Map[]}
    Asm(RV.MV(Reg.fp, Reg.sp), "Initialize frame pointer")
    ++ (doCodegen env node)
        .AddText([
            (RV.LI(Reg.a7, 10), "RARS syscall: Exit")
            (RV.ECALL, "Successful exit with code 0")
        ])
