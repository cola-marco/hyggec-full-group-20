module ClosureConversion

open AST
open Type
open Typechecker

/// We ensure that the argument and field names added during closure conversion do not clash with other arguments and variable names that appear in the input program
type UniqueNameGenerator() = 
    let mutable counter = 0

    member _.Generate(prefix: string) = 
        counter <- counter + 1
        $"$%s{prefix}_%d{counter}"

/// Create a PretypeNode at the given source-code position.
/// This is used when closure conversion generates new type annotations,
/// for example for the hidden closure argument `$clos_1`.
let mkPretype  (pos: AST.Position) (pretype: AST.Pretype) : AST.PretypeNode = 
    {
        Pos = pos
        Pretype = pretype
    }

/// Convert a checked Hygge type back into a syntactic pretype.
/// Closure conversion starts from the typed AST, but it generates a new
/// untyped AST that will be type checked again. Therefore, generated
/// lambdas need PretypeNode annotations instead of Type.Type values.
let rec typeToPretype pos typ = 
    match typ with
    | TUnit ->
        mkPretype pos (TId "unit")

    | TBool ->
        mkPretype pos (TId "bool")
    
    | TInt ->
        mkPretype pos (TId "int")

    | TFloat ->
        mkPretype pos (TId "float")
    
    | TString ->
        mkPretype pos (TId "string")
    
    | TVar name ->
        mkPretype pos (TId name)
    
    | TFun(argTypes, returnType) ->
        mkPretype pos
            (
                Pretype.TFun(
                    argTypes |> List.map (typeToPretype pos),
                    typeToPretype pos returnType
                )
            )
    
    | TStruct fields ->
        mkPretype pos
            (
                Pretype.TStruct(
                    fields
                    |> List.map (fun (fieldName, fieldType) ->
                        fieldName, typeToPretype pos fieldType)
                )
            )

    | TUnion cases ->
        mkPretype pos
            (
                Pretype.TUnion(
                    cases
                    |> List.map (fun (caseName, caseType) ->
                        caseName, typeToPretype pos caseType)
                )
            )

    | TArray elemType ->
        mkPretype pos
            (Pretype.TArray(typeToPretype pos elemType))

/// Create an untyped AST node at the given source-code position.
let mkNode (pos:  AST.Position)(expr: AST.UntypedExpr): AST.UntypedAST =
    {
        Expr = expr
        Pos = pos
        Env = ()
        Type = ()
    }

/// Create an untyped AST node using the source-code position of an existing
/// typed AST node. 
let mkLike (node: Typechecker.TypedAST) (expr: AST.UntypedExpr) : AST.UntypedAST =
    mkNode node.Pos expr

/// Erase type-checking annotations while preserving the original expression
/// structure. This gives closure conversion a recursive traversal skeleton:
/// most expressions are copied unchanged, while lambdas and applications are
/// rewritten by the closure-conversion cases.
let rec convert (node: Typechecker.TypedAST) : AST.UntypedAST =
    match node.Expr with
    | UnitVal ->
        mkLike node UnitVal

    | BoolVal value ->
        mkLike node (BoolVal value)

    | IntVal value ->
        mkLike node (IntVal value)

    | FloatVal value ->
        mkLike node (FloatVal value)

    | StringVal value ->
        mkLike node (StringVal value)

    | Var name ->
        mkLike node (Var name)

    | BinNumOp(op, lhs, rhs) ->
        mkLike node 
            (
                BinNumOp(
                    op, convert lhs, convert rhs
                )
            )

    | BinLogicOp(op, lhs, rhs) ->
        mkLike node 
            (
                BinLogicOp(
                    op, convert lhs, convert rhs
                )
            )

    | Not arg ->
        mkLike node (Not(convert arg))

    | Sqrt arg ->
        mkLike node (Sqrt(convert arg))

    | BinRelOp(op, lhs, rhs) ->
        mkLike node 
            (
                BinRelOp(
                    op, convert lhs, convert rhs
                )
            )

    | ReadInt ->
        mkLike node ReadInt

    | ReadFloat ->
        mkLike node ReadFloat

    | Print arg ->
        mkLike node (Print(convert arg))

    | PrintLn arg ->
        mkLike node (PrintLn(convert arg))

    | If(condition, ifTrue, ifFalse) ->
        mkLike node 
            (
                If(
                    convert condition,
                    convert ifTrue,
                    convert ifFalse
                )
            )

    | Seq nodes ->
        mkLike node 
            (
                Seq(nodes |> List.map convert)
            )

    | Type(name, def, scope) ->
        mkLike node 
            (
                Type(
                    name, 
                    def, 
                    convert scope
                )
            )

    | Ascription(tpe, inner) ->
        mkLike node 
            (
                Ascription(
                    tpe, 
                    convert inner
                )
            )

    | Assertion arg ->
        mkLike node 
            (
                Assertion(convert arg)
            )

    | Let(name, init, scope) ->
        mkLike node 
            (
                Let(
                    name, 
                    convert init, 
                    convert scope
                )
            )

    | LetT(name, tpe, init, scope) ->
        mkLike node 
            (
                LetT(
                    name, 
                    tpe, 
                    convert init, 
                    convert scope
                )
            )

    | LetMut(name, init, scope) ->
        mkLike node 
            (
                LetMut(
                    name, 
                    convert init, 
                    convert scope
                )
            )

    | Assign(target, expr) ->
        mkLike node 
            (
                Assign(
                    convert target, 
                    convert expr
                )
            )

    | While(cond, body) ->
        mkLike node 
            (
                While(
                    convert cond, 
                    convert body
                )
            )

    | DoWhile(body, cond) ->
        mkLike node 
            (
                DoWhile(
                    convert body, 
                    convert cond
                )
            )

    | For(name, init, cond, step, body) ->
        mkLike node 
            (
                For(
                    name,
                    convert init,
                    convert cond,
                    convert step,
                    convert body
                )
            )

    | Lambda(args, body) ->
        mkLike node 
            (
                Lambda(
                    args, 
                    convert body
                )
            )

    | Application(fn, args) ->
        mkLike node 
            (
                Application(
                    convert fn,
                    args |> List.map convert
                )
            )

    | StructCons fields ->
        mkLike node 
            (
                StructCons(
                    fields |> List.map (fun (fieldName, value) ->
                        fieldName, convert value)
                )
            )

    | FieldSelect(target, field) ->
        mkLike node 
            (
                FieldSelect(
                    convert target, 
                    field
                )
            )

    | Pointer addr ->
        mkLike node 
            (
                Pointer addr
            )

    | Copy arg ->
        mkLike node 
            (
                Copy(convert arg)
            )

    | DeepCopy arg ->
        mkLike node 
            (
                DeepCopy(convert arg)
            )

    | UnionCons(label, expr) ->
        mkLike node 
            (
                UnionCons(label, convert expr)
            )

    | Match(expr, cases) ->
        mkLike node 
            (
                Match(
                    convert expr,
                    cases |> List.map (fun (label, varName, caseBody) ->
                        label, varName, convert caseBody)
                )
            )

    | ArrayCons(size, init) ->
        mkLike node 
            (
                ArrayCons(
                    convert size, 
                    convert init
                )
            )

    | ArrayElem(name, index) ->
        mkLike node 
            (
                ArrayElem(
                    convert name, 
                    convert index
                )
            )

    | ArrayLength name ->
        mkLike node 
            (
                ArrayLength(convert name)
            )

/// Entry point for the closure-conversion phase.

let closureConvert (node: Typechecker.TypedAST) : AST.UntypedAST =
    convert node

