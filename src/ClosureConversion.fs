module ClosureConversion

open AST
open Type
open Typechecker

/// Generates unique internal names that cannot clash with source-level names.
type UniqueNameGenerator() = 
    let mutable counter = 0

    member _.Generate(prefix: string) = 
        counter <- counter + 1
        $"$%s{prefix}_%d{counter}"

let private nameGenerator = UniqueNameGenerator()

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

/// Create an untyped node using the position of another untyped node.
let mkLikeUntyped (node: AST.UntypedAST) (expr: AST.UntypedExpr) : AST.UntypedAST =
    mkNode node.Pos expr

/// Look up the type of a variable in the typing environment of a typed AST node.
let private lookupVarType (node: Typechecker.TypedAST) (name: string) : Type.Type =
    match Map.tryFind name node.Env.Vars with
    | Some(tpe) -> tpe
    | None -> failwith $"Closure conversion error: cannot find type of variable '%s{name}'"

/// Represents a closure type generated during closure conversion.
type GeneratedTypeDef =
 {
    Name: string
    Def: AST.PretypeNode
 }

/// Result of converting an expression.
/// Besides the converted expression, we also keep generated closure types
/// and the expression's new type after closure conversion.
type ConversionResult = 
 {
    Expr: AST.UntypedAST
    TypeDefs: List<GeneratedTypeDef>
    ConvertedType: Type.Type
 }

// Wrap an expression with generated type definitions so they are in scope.
let wrapTypeDefs (pos: AST.Position) (defs: List<GeneratedTypeDef>) (body: AST.UntypedAST) : AST.UntypedAST =
    List.foldBack
        (fun def acc ->
            mkNode pos (Type(def.Name, def.Def, acc)))
        defs
        body

// Replace captured variables in an already converted untyped AST.
// For example, x becomes $clos_1.x inside the generated plain function body.
let rec replaceCapturedVars (closureArgName: string) (captured: Set<string>) (node: AST.UntypedAST) : AST.UntypedAST =
    match node.Expr with
    | Var name when Set.contains name captured ->
        let closureVar =
            mkNode node.Pos (Var closureArgName)

        mkLikeUntyped node 
            (
                FieldSelect(
                    closureVar, 
                    name
                )
            )

    | Var name ->
        mkLikeUntyped node (Var name)

    | UnitVal ->
        mkLikeUntyped node UnitVal

    | BoolVal value ->
        mkLikeUntyped node (BoolVal value)

    | IntVal value ->
        mkLikeUntyped node (IntVal value)

    | FloatVal value ->
        mkLikeUntyped node (FloatVal value)

    | StringVal value ->
        mkLikeUntyped node (StringVal value)

    | BinNumOp(op, lhs, rhs) ->
        mkLikeUntyped node 
            (
                BinNumOp(
                    op,
                    replaceCapturedVars closureArgName captured lhs,
                    replaceCapturedVars closureArgName captured rhs
                )
            )

    | BinLogicOp(op, lhs, rhs) ->
        mkLikeUntyped node 
            (
                BinLogicOp(
                    op,
                    replaceCapturedVars closureArgName captured lhs,
                    replaceCapturedVars closureArgName captured rhs
                )
            )

    | BinRelOp(op, lhs, rhs) ->
        mkLikeUntyped node 
            (
                BinRelOp(
                    op,
                    replaceCapturedVars closureArgName captured lhs,
                    replaceCapturedVars closureArgName captured rhs
                )
            )

    | Not arg ->
        mkLikeUntyped node 
            (
                Not(
                    replaceCapturedVars closureArgName captured arg
                )
            )

    | Sqrt arg ->
        mkLikeUntyped node 
            (
                Sqrt(
                    replaceCapturedVars closureArgName captured arg
                )
            )

    | If(condition, ifTrue, ifFalse) ->
        mkLikeUntyped node 
            (
                If(
                    replaceCapturedVars closureArgName captured condition,
                    replaceCapturedVars closureArgName captured ifTrue,
                    replaceCapturedVars closureArgName captured ifFalse
                )
            )

    | Let(name, init, scope) ->
        mkLikeUntyped node 
            (
                Let(
                    name,
                    replaceCapturedVars closureArgName captured init,
                    replaceCapturedVars closureArgName (Set.remove name captured) scope
                )
            )

    | LetT(name, tpe, init, scope) ->
        mkLikeUntyped node 
            (
                LetT(
                    name,
                    tpe,
                    replaceCapturedVars closureArgName captured init,
                    replaceCapturedVars closureArgName (Set.remove name captured) scope
                )
            )

    | LetMut(name, init, scope) ->
        mkLikeUntyped node 
            (
                LetMut(
                    name,
                    replaceCapturedVars closureArgName captured init,
                    replaceCapturedVars closureArgName (Set.remove name captured) scope
                )
            )

    | Lambda(args, body) ->
        let argNames =
            args 
            |> List.map fst 
            |> Set.ofList

        let capturedForBody =
            Set.difference captured argNames

        mkLikeUntyped node 
            (
                Lambda(
                    args,
                    replaceCapturedVars closureArgName capturedForBody body
                )
            )

    | Application(fn, args) ->
        mkLikeUntyped node 
            (
                Application(
                    replaceCapturedVars closureArgName captured fn,
                    args |> List.map (replaceCapturedVars closureArgName captured)
                )
            )

    | StructCons fields ->
        mkLikeUntyped node 
            (
                StructCons(
                    fields
                    |> List.map 
                        (
                            fun (fieldName, value) ->
                                fieldName, replaceCapturedVars closureArgName captured value
                        )
                )
            )

    | FieldSelect(target, field) ->
        mkLikeUntyped node 
            (
                FieldSelect(
                    replaceCapturedVars closureArgName captured target,
                    field
                )
            )

    | Type(name, def, scope) ->
        mkLikeUntyped node 
            (
                Type(
                    name,
                    def,
                    replaceCapturedVars closureArgName captured scope
                )
            )

    | Ascription(tpe, inner) ->
        mkLikeUntyped node 
            (
                Ascription(
                    tpe,
                    replaceCapturedVars closureArgName captured inner
                )
            )

    | Assertion arg ->
        mkLikeUntyped node 
            (
                Assertion(
                    replaceCapturedVars closureArgName captured arg
                )
            )

    | Seq nodes ->
        mkLikeUntyped node 
            (
                Seq(
                    nodes |> List.map (replaceCapturedVars closureArgName captured)
                )
            )

    | other ->
        mkLikeUntyped node other
    
// Convert a lambda expression into a closure struct.
// This is used both for let-bound lambdas and nested lambdas.
and convertLambdaToClosure (lambdaNode: Typechecker.TypedAST) (args: List<string * AST.PretypeNode>) (body: Typechecker.TypedAST) : ConversionResult =
    let closureTypeName =
        nameGenerator.Generate "Closure"

    let closureArgName =
        nameGenerator.Generate "clos"

    let captured =
        ASTUtil.freeVars lambdaNode

    let mutableCaptured =
        captured
        |> Set.filter (fun varName -> lambdaNode.Env.Mutables.Contains varName)

    if not (Set.isEmpty mutableCaptured) then
        failwith $"Closure conversion only supports immutable captured variables: %A{mutableCaptured}"

    let closureTypePretype =
        mkPretype lambdaNode.Pos (TId closureTypeName)

    let originalArgTypes, _ =
        match lambdaNode.Type with
        | TFun(argTypes, ret) -> 
            argTypes, ret

        | other ->
            failwith $"Closure conversion expected lambda to have function type, got %A{other}"

    let bodyResult =
        convertExpr body

    let convertedReturnType =
        bodyResult.ConvertedType

    let plainFunctionType =
        mkPretype lambdaNode.Pos 
            (
                Pretype.TFun(
                    closureTypePretype :: (originalArgTypes |> List.map (typeToPretype lambdaNode.Pos)),
                    typeToPretype lambdaNode.Pos convertedReturnType
                )
            )

    let capturedFields =
        captured
        |> Set.toList
        |> List.map 
            (
                fun varName ->
                    varName, typeToPretype lambdaNode.Pos (lookupVarType lambdaNode varName)
            )

    let closureStructType =
        mkPretype lambdaNode.Pos 
            (
                Pretype.TStruct(
                    ("$f", plainFunctionType) :: capturedFields
                )
            )

    let convertedBodyWithCapturedVars =
        replaceCapturedVars closureArgName captured bodyResult.Expr

    let plainFunction =
        mkNode lambdaNode.Pos 
            (
                Lambda(
                    (closureArgName, closureTypePretype) :: args,
                    convertedBodyWithCapturedVars
                )
            )

    let closureFields =
        let functionField =
            "$f", plainFunction

        let capturedValueFields =
            captured
            |> Set.toList
            |> List.map 
                (
                    fun varName ->
                        varName, mkNode lambdaNode.Pos (Var varName)
                )

        functionField :: capturedValueFields

    let rawClosureStruct =
        mkNode lambdaNode.Pos 
            (
                StructCons closureFields
            )

    let closureStruct =
        mkNode lambdaNode.Pos 
            (
                Ascription(
                    closureTypePretype,
                    rawClosureStruct
                )
            )

    let generatedType =
        {
            Name = closureTypeName
            Def = closureStructType
        }

    {
        Expr = closureStruct
        TypeDefs = bodyResult.TypeDefs @ [generatedType]
        ConvertedType = TVar closureTypeName
    }

/// Convert a typed expression as part of closure conversion.
/// Most expressions keep the same structure, but the result also carries
/// generated closure type definitions and the expression's type after conversion.
/// Lambda and application cases are rewritten into explicit closure operations.
and convertExpr (node: Typechecker.TypedAST) : ConversionResult =
    match node.Expr with
    | UnitVal ->
        {
            Expr = mkLike node UnitVal
            TypeDefs = []
            ConvertedType = node.Type
        }

    | BoolVal value ->
        {
            Expr = mkLike node (BoolVal value)
            TypeDefs = []
            ConvertedType = node.Type
        }

    | IntVal value ->
        {
            Expr = mkLike node (IntVal value)
            TypeDefs = []
            ConvertedType = node.Type
        }

    | FloatVal value ->
        {
            Expr = mkLike node (FloatVal value)
            TypeDefs = []
            ConvertedType = node.Type
        }

    | StringVal value ->
        {
            Expr = mkLike node (StringVal value)
            TypeDefs = []
            ConvertedType = node.Type
        }

    | Var name ->
        {
            Expr = mkLike node (Var name)
            TypeDefs = []
            ConvertedType = node.Type
        }

    | BinNumOp(op, lhs, rhs) ->
        let lhsResult = convertExpr lhs
        let rhsResult = convertExpr rhs
        {
            Expr = mkLike node 
                (
                    BinNumOp(
                        op, lhsResult.Expr, rhsResult.Expr
                    )
                )
            TypeDefs = lhsResult.TypeDefs @ rhsResult.TypeDefs
            ConvertedType = node.Type
        }

    | BinLogicOp(op, lhs, rhs) ->
        let lhsResult = convertExpr lhs
        let rhsResult = convertExpr rhs
        {
            Expr = mkLike node 
                (
                    BinLogicOp(
                        op, lhsResult.Expr, rhsResult.Expr
                    )
                )
            TypeDefs = lhsResult.TypeDefs @ rhsResult.TypeDefs
            ConvertedType = node.Type
        }

    | Not arg ->
        let argResult = convertExpr arg
        {
            Expr = mkLike node (Not(argResult.Expr))
            TypeDefs = argResult.TypeDefs
            ConvertedType = node.Type
        }

    | Sqrt arg ->
        let argResult = convertExpr arg
        {
            Expr = mkLike node (Sqrt(argResult.Expr))
            TypeDefs = argResult.TypeDefs
            ConvertedType = node.Type
        }

    | BinRelOp(op, lhs, rhs) ->
        let lhsResult = convertExpr lhs
        let rhsResult = convertExpr rhs
        {
            Expr = mkLike node 
                (
                    BinRelOp(
                        op, lhsResult.Expr, rhsResult.Expr
                    )
                )
            TypeDefs = lhsResult.TypeDefs @ rhsResult.TypeDefs
            ConvertedType = node.Type
        }

    | ReadInt ->
        {
            Expr = mkLike node ReadInt
            TypeDefs = []
            ConvertedType = node.Type
        }

    | ReadFloat ->
        {
            Expr = mkLike node ReadFloat
            TypeDefs = []
            ConvertedType = node.Type
        }

    | Print arg ->
        let argResult = convertExpr arg
        {
            Expr = mkLike node (Print(argResult.Expr))
            TypeDefs = argResult.TypeDefs
            ConvertedType = node.Type
        }

    | PrintLn arg ->
        let argResult = convertExpr arg
        {
            Expr = mkLike node (PrintLn(argResult.Expr))
            TypeDefs = argResult.TypeDefs
            ConvertedType = node.Type
        }

    | If(condition, ifTrue, ifFalse) ->
        let condResult = convertExpr condition
        let trueResult = convertExpr ifTrue
        let falseResult = convertExpr ifFalse
        {
            Expr = mkLike node 
                (
                    If(
                        condResult.Expr,
                        trueResult.Expr,
                        falseResult.Expr
                    )
                )
            TypeDefs = condResult.TypeDefs @ trueResult.TypeDefs @ falseResult.TypeDefs
            ConvertedType = node.Type
        }

    | Seq nodes ->
        let nodeResults = nodes |> List.map convertExpr
        {
            Expr = mkLike node 
                (
                    Seq(nodeResults |> List.map (fun r -> r.Expr))
                )
            TypeDefs = List.concat (nodeResults |> List.map (fun r -> r.TypeDefs))
            ConvertedType = node.Type
        }

    | Type(name, def, scope) ->
        let scopeResult = convertExpr scope
        {
            Expr = mkLike node 
                (
                    Type(
                        name, 
                        def, 
                        scopeResult.Expr
                    )
                )
            TypeDefs = scopeResult.TypeDefs
            ConvertedType = node.Type
        }

    | Ascription(tpe, inner) ->
        let innerResult = convertExpr inner
        {
            Expr = mkLike node 
                (
                    Ascription(
                        tpe, 
                        innerResult.Expr
                    )
                )
            TypeDefs = innerResult.TypeDefs
            ConvertedType = node.Type
        }

    | Assertion arg ->
        let argResult = convertExpr arg
        {
            Expr = mkLike node 
                (
                    Assertion(argResult.Expr)
                )
            TypeDefs = argResult.TypeDefs
            ConvertedType = node.Type
        }

    | Let(name, ({ Expr = Lambda(args, body) } as init), scope) ->
        let initResult =
            convertLambdaToClosure init args body

        let scopeResult =
            convertExpr scope

        {
            Expr = mkLike node 
                (
                    Let(
                        name,
                        initResult.Expr,
                        scopeResult.Expr
                    )
                )

            TypeDefs =
                initResult.TypeDefs @ scopeResult.TypeDefs

            ConvertedType =
                node.Type
        }

    | Let(name, init, scope) ->
        let initResult = convertExpr init
        let scopeResult = convertExpr scope
        {
            Expr = mkLike node 
                (
                    Let(
                        name, 
                        initResult.Expr,
                        scopeResult.Expr
                    )
                )
            TypeDefs = initResult.TypeDefs @ scopeResult.TypeDefs
            ConvertedType = node.Type
        }

    | LetT(name, tpe, init, scope) ->
        let initResult = convertExpr init
        let scopeResult = convertExpr scope
        {
            Expr = mkLike node 
                (
                    LetT(
                        name, 
                        tpe, 
                        initResult.Expr,
                        scopeResult.Expr
                    )
                )
            TypeDefs = initResult.TypeDefs @ scopeResult.TypeDefs
            ConvertedType = node.Type
        }

    | LetMut(name, init, scope) ->
        let initResult = convertExpr init
        let scopeResult = convertExpr scope
        {
            Expr = mkLike node 
                (
                    LetMut(
                        name, 
                        initResult.Expr,
                        scopeResult.Expr
                    )
                )
            TypeDefs = initResult.TypeDefs @ scopeResult.TypeDefs
            ConvertedType = node.Type
        }

    | Assign(target, expr) ->
        let targetResult = convertExpr target
        let exprResult = convertExpr expr
        {
            Expr = mkLike node 
                (
                    Assign(
                        targetResult.Expr, 
                        exprResult.Expr
                    )
                )
            TypeDefs = targetResult.TypeDefs @ exprResult.TypeDefs
            ConvertedType = node.Type
        }

    | While(cond, body) ->
        let condResult = convertExpr cond
        let bodyResult = convertExpr body
        {
            Expr = mkLike node 
                (
                    While(
                        condResult.Expr, 
                        bodyResult.Expr
                    )
                )
            TypeDefs = condResult.TypeDefs @ bodyResult.TypeDefs
            ConvertedType = node.Type
        }

    | DoWhile(body, cond) ->
        let bodyResult = convertExpr body
        let condResult = convertExpr cond
        {
            Expr = mkLike node 
                (
                    DoWhile(
                        bodyResult.Expr, 
                        condResult.Expr
                    )
                )
            TypeDefs = bodyResult.TypeDefs @ condResult.TypeDefs
            ConvertedType = node.Type
        }

    | For(name, init, cond, step, body) ->
        let initResult = convertExpr init
        let condResult = convertExpr cond
        let stepResult = convertExpr step
        let bodyResult = convertExpr body
        {
            Expr = mkLike node 
                (
                    For(
                        name,
                        initResult.Expr,
                        condResult.Expr,
                        stepResult.Expr,
                        bodyResult.Expr
                    )
                )
            TypeDefs = initResult.TypeDefs @ condResult.TypeDefs @ stepResult.TypeDefs @ bodyResult.TypeDefs
            ConvertedType = node.Type
        }

    | Lambda(args, body) ->
        convertLambdaToClosure node args body

    // Apply a closure by calling its $f field and passing the closure
    // itself as the hidden first argument.
    | Application(fn, args) ->
        let tmpName = nameGenerator.Generate "tmp"

        let fnResult = convertExpr fn
        let argResults = args |> List.map convertExpr

        let tmpVar =
            mkNode node.Pos (Var tmpName)

        let functionField =
            mkNode node.Pos (FieldSelect(tmpVar, "$f"))

        let call =
            mkNode node.Pos (
                Application(
                    functionField,
                    tmpVar :: (argResults |> List.map (fun r -> r.Expr))
                )
            )

        {
            Expr =
                mkLike node (
                    Let(
                        tmpName,
                        fnResult.Expr,
                        call
                    )
                )

            TypeDefs =
                fnResult.TypeDefs @ (argResults |> List.collect (fun r -> r.TypeDefs))

            ConvertedType =
                node.Type
        }

    | StructCons fields ->
        let fieldResults = fields |> List.map (fun (name, expr) -> name, convertExpr expr)
        {
            Expr = mkLike node 
                (
                    StructCons(
                        fieldResults |> List.map (fun (name, result) ->
                            name, result.Expr)
                    )
                )
            TypeDefs = List.concat (fieldResults |> List.map (fun (_, result) -> result.TypeDefs))
            ConvertedType = node.Type
        }

    | FieldSelect(target, field) ->
        let targetResult = convertExpr target
        {
            Expr = mkLike node 
                (
                    FieldSelect(
                        targetResult.Expr, 
                        field
                    )
                )
            TypeDefs = targetResult.TypeDefs
            ConvertedType = node.Type
        }

    | Pointer addr ->
        {
            Expr = mkLike node 
                (
                    Pointer addr
                )
            TypeDefs = []
            ConvertedType = node.Type
        }

    | Copy arg ->
        let argResult = convertExpr arg
        {
            Expr = mkLike node 
                (
                    Copy(argResult.Expr)
                )
            TypeDefs = argResult.TypeDefs
            ConvertedType = node.Type
        }

    | DeepCopy arg ->
        let argResult = convertExpr arg
        {
            Expr = mkLike node 
                (
                    DeepCopy(argResult.Expr)
                )
            TypeDefs = argResult.TypeDefs
            ConvertedType = node.Type
        }

    | UnionCons(label, expr) ->
        let exprResult = convertExpr expr
        {
            Expr = mkLike node 
                (
                    UnionCons(label, exprResult.Expr)
                )
            TypeDefs = exprResult.TypeDefs
            ConvertedType = node.Type
        }

    | Match(expr, cases) ->
        let exprResult = convertExpr expr
        let caseResults = cases |> List.map (fun (label, varName, body) -> label, varName, convertExpr body)
        {
            Expr = mkLike node 
                (
                    Match(
                        exprResult.Expr,
                        caseResults |> List.map (fun (label, varName, result) ->
                            label, varName, result.Expr)
                    )
                )
            TypeDefs = exprResult.TypeDefs @ (List.concat (caseResults |> List.map (fun (_, _, result) -> result.TypeDefs)))
            ConvertedType = node.Type
        }

    | ArrayCons(size, init) ->
        let sizeResult = convertExpr size
        let initResult = convertExpr init
        {
            Expr = mkLike node 
                (
                    ArrayCons(
                        sizeResult.Expr, 
                        initResult.Expr
                    )
                )
            TypeDefs = sizeResult.TypeDefs @ initResult.TypeDefs
            ConvertedType = node.Type
        }

    | ArrayElem(name, index) ->
        let nameResult = convertExpr name
        let indexResult = convertExpr index
        {
            Expr = mkLike node 
                (
                    ArrayElem(
                        nameResult.Expr, 
                        indexResult.Expr
                    )
                )
            TypeDefs = nameResult.TypeDefs @ indexResult.TypeDefs
            ConvertedType = node.Type
        }

    | ArrayLength name ->
        let nameResult = convertExpr name
        {
            Expr = mkLike node 
                (
                    ArrayLength(nameResult.Expr)
                )
            TypeDefs = nameResult.TypeDefs
            ConvertedType = node.Type
        }

/// Entry helper for closure conversion.
/// Converts a typed AST into an untyped closure-converted AST and wraps the
/// result with any generated closure type definitions.
and convert (node: Typechecker.TypedAST) : AST.UntypedAST =
    let result = convertExpr node
    wrapTypeDefs node.Pos result.TypeDefs result.Expr

/// Entry point for the closure-conversion phase.
let closureConvert (node: Typechecker.TypedAST) : AST.UntypedAST =
    convert node

