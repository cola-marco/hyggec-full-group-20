// hyggec - The didactic compiler for the Hygge programming language.
// Copyright (C) 2026 Technical University of Denmark
// Author: Alceste Scalas <alcsc@dtu.dk>
// Released under the MIT license (see LICENSE.md for details)

/// Parser for the Hygge programming language, implemented using parser combinators.
module Parser

open Lexer
open ParserUtils
open AST


/// Parse pretype. This is a forward reference to pPretype'.
let pPretype, pPretypeRef = pForwardRef()
/// Parse a Hygge expression. This is a forward reference to pExpr'.
let pExpr, pExprRef = pForwardRef()
/// Parse a sequence of expressions. This is a forward reference to pSequenceExpr'.
let pSequenceExpr, pSequenceExprRef = pForwardRef()
/// Parse a simple expression. This is a forward reference to pSimpleExpr'.
let pSimpleExpr, pSimpleExprRef = pForwardRef()
/// Parse an unary expression. This is a forward reference to pUnaryExpr'.
let pUnaryExpr, pUnaryExprRef = pForwardRef()


/// Parse an integer value, producing an AST node with an IntVal expression.
let inline pIntVal (stream: TokenStream) =
    let tok = stream.Current()
    match tok.Token with
        | LIT_INT v ->
            stream.Advance()
            Ok (mkNode (AST.Expr.IntVal v) tok.Begin tok.Begin tok.End)
        | _ -> Error "LIT_INT"


/// Parse a float value, producing an AST node with a FloatVal expression.
let inline pFloatVal (stream: TokenStream) =
    let tok = stream.Current()
    match tok.Token with
        | LIT_FLOAT v ->
            stream.Advance()
            Ok (mkNode (AST.Expr.FloatVal v) tok.Begin tok.Begin tok.End)
        | _ -> Error "LIT_FLOAT"


/// Parse a boolean value, producing an AST node with a BoolVal expression.
let inline pBoolVal (stream: TokenStream) =
    let tok = stream.Current()
    match tok.Token with
        | LIT_BOOL v ->
            stream.Advance()
            Ok (mkNode (AST.Expr.BoolVal v) tok.Begin tok.Begin tok.End)
        | _ -> Error "LIT_BOOL"


/// Parse a string value, producing an AST node with a StringVal expression.
let inline pStringVal (stream: TokenStream) =
    let tok = stream.Current()
    match tok.Token with
        | LIT_STRING v ->
            stream.Advance()
            Ok (mkNode (AST.Expr.StringVal v) tok.Begin tok.Begin tok.End)
        | _ -> Error "LIT_STRING"


/// Parse a unit value, producing an AST node with a UnitVal expression.
let inline pUnitVal (stream: TokenStream) =
    let tok = stream.Current()
    match tok.Token with
        | LIT_UNIT ->
            stream.Advance()
            Ok (mkNode AST.Expr.UnitVal tok.Begin tok.Begin tok.End)
        | _ -> Error "LIT_STRING"


/// Parse an identifier, returning its token with position and name.
let inline pIdent (stream: TokenStream) =
    let tok = stream.Current()
    match tok.Token with
        | IDENT name ->
            stream.Advance()
            Ok (tok, name)
        | _ -> Error "IDENT"


/// Parse a literal value.
let pValue = choice [
    pIntVal
    pStringVal
    pFloatVal
    pUnitVal
    pBoolVal
]


/// Parse a possibly empty sequence of comma-separated (pre)types.
let pPretypesCommaSeq =
    /// Parse a (pre)type and wrap the result in a single-element list (this is
    /// handy for accumulation using chainl below).
    let pPretypeLst = pPretype |>> fun ptNode -> [ptNode]

    chainl pPretypeLst
        (pToken COMMA
             |>> fun _ ->
                fun acc ptNode ->
                    // ptNode is produced by pIdentType above and contains a
                    // pretype AST node; we accumulate it with acc
                    List.append acc ptNode)
        [] // Default result for chainl: empty list


/// Parse a possibly empty sequence of comma-separated (pre)types, between
/// parentheses.
let pParenPretypesCommaSeq = choice [
    pToken LIT_UNIT >>- preturn []
    pToken LPAREN >>- pPretypesCommaSeq ->> pToken RPAREN
] 


/// Parse a non-empty sequence of identifiers with type ascriptions, separated
/// by semicolons.
let pIdentPretypesSemiSeq =
    /// Parse an identifier with a (pre)type ascription. Wrap the result in a
    /// single-element list (this is handy for accumulation using chainl below).
    let pIdentType = pIdent ->>- (pToken COLON >>- pPretype)
                        |>> fun ((_, name), preType) -> [(name, preType)]

    chainl1 pIdentType
        (pToken SEMI
            |>> fun _ ->
                fun acc idType ->
                     // idType (produced by pIdentType above) contains a pair with
                     // an identifier name and (pre)type; we accumulate it with acc
                     List.append acc idType)


/// Parse a pretype, producing a PretypeNode.
let pPretype' = choice [
    // Array type
    pToken ARRAY ->>- (pToken LCURLY >>- pPretype) ->>- pToken RCURLY
        |>> fun ((tok1, tpe), tok2) ->
            mkPretypeNode (AST.Pretype.TArray tpe) tok1.Begin tok1.Begin tok2.End
    pIdent
        |>> fun (tok, name) ->
            mkPretypeNode (AST.Pretype.TId name) tok.Begin tok.Begin tok.End
    // Function type
    pParenPretypesCommaSeq ->>- pToken RARROW ->>- pPretype
        |>> fun ((targs, tok), tret) ->
            mkPretypeNode (AST.Pretype.TFun (targs, tret)) tok.Begin tok.Begin tret.Pos.End
    // Struct type
    pToken STRUCT ->>- (pToken LCURLY >>- pIdentPretypesSemiSeq) ->>- pToken RCURLY
        |>> fun ((tok1, fields), tok2) ->
            mkPretypeNode (AST.Pretype.TStruct fields) tok1.Begin tok1.Begin tok2.End
    // Union type
    pToken UNION ->>- (pToken LCURLY >>- pIdentPretypesSemiSeq) ->>- pToken RCURLY
        |>> fun ((tok1, cases), tok2) ->
            mkPretypeNode (AST.Pretype.TUnion cases) tok1.Begin tok1.Begin tok2.End
    
]


/// Parse a possibly empty sequence of comma-separated identifiers with type
/// ascriptions.
let pIdentTypesCommaSeq =
    /// Parse an identifier with a (pre)type ascription. Wrap the result in a
    /// single-element list (this is handy for accumulation using chainl below).
    let pIdentType = pIdent ->>- (pToken COLON >>- pPretype)
                        |>> fun ((_, name), preType) -> [(name, preType)]

    chainl pIdentType
        (pToken COMMA
            |>> fun _ ->
                fun acc idType ->
                    // idType is produced by pIdentType above and contains a
                    // pair with an identifier name and (pre)type; we
                    // accumulate it with acc
                    List.append acc idType)
        [] // Default result for chainl: empty list


/// Parse a possibly empty sequence of comma-separated identifiers with type
/// ascriptions, between parentheses.
let pParenIdentTypesCommaSeq =
    choice [
        pToken LIT_UNIT >>- preturn [] // Matches (), i.e. two parentheses without spaces in between
        pToken LPAREN >>- pIdentTypesCommaSeq ->> pToken RPAREN
    ]


/// Parse a possibly empty sequence of comma-separated simple expressions.
let pSimpleExprCommaSeq =
    /// Parse a simple expression and wrap the result in a single-element list
    /// (this is handy for accumulation using chainl below).
    let pSimpleExprList = pSimpleExpr |>> fun node -> [node]

    chainl pSimpleExprList
           (pToken COMMA
                |>> fun _ ->
                    fun acc expr ->
                        // expr is produced by pSimpleExprList above and
                        // contains an AST node wrapped in a list; we
                        // accumulate it with acc
                        List.append acc expr)
           [] // Default result for chainl: empty list


/// Parse a possibly empty sequence of comma-separated simple expressions,
/// between parentheses. Return a pair with the list of parsed AST nodes and the
/// rightmost token,
let pParenSimpleExprCommaSeq =
    choice [
        pToken LIT_UNIT // Matches (), i.e. two parentheses without spaces in between
            |>> fun tok -> ([], tok)
        pToken LPAREN >>- pSimpleExprCommaSeq ->>- pToken RPAREN
    ]


/// Parse empty parentheses, like (), ( ), (  )... They could be tokenized as
/// either a LIT_UNIT or as an LPAREN followed by an RPAREN. Return the
/// rightmost token.
let pEmptyParen = choice [
    pToken LIT_UNIT
    pToken LPAREN >>- pToken RPAREN
]


/// Parse a readInt() expression.
let pReadInt =
    pToken READ_INT ->>- pEmptyParen
        |>> fun (tok1, tok2) ->
            mkNode AST.Expr.ReadInt tok1.Begin tok1.Begin tok2.End


/// Parse a readFloat() expression.
let pReadFloat =
    pToken READ_FLOAT ->>- pEmptyParen
        |>> fun (tok1, tok2) ->
            mkNode AST.Expr.ReadFloat tok1.Begin tok1.Begin tok2.End


/// Parse a print(...) expression.
let pPrint =
    pToken PRINT ->>- (pToken LPAREN >>- pSimpleExpr) ->>- pToken RPAREN
        |>> fun ((tok1, expr), tok2) ->
            mkNode (AST.Expr.Print expr) tok1.Begin tok1.Begin tok2.End


/// Parse a printLn(...) expression.
let pPrintLn =
    pToken PRINTLN ->>- (pToken LPAREN >>- pSimpleExpr) ->>- pToken RPAREN
        |>> fun ((tok1, expr), tok2) ->
            mkNode (AST.Expr.PrintLn expr) tok1.Begin tok1.Begin tok2.End

/// Parse a sqrt(...) expression, with optional type ascription.
let pSqrt =
    pToken SQRT ->>- (pToken LPAREN >>- pSimpleExpr) ->>- pToken RPAREN
    >>= fun ((tokSqrt, expr), tokR) ->
        // Create the basic Sqrt node
        let node = mkNode (AST.Expr.Sqrt expr) tokSqrt.Begin tokSqrt.Begin tokR.End
        // Optionally parse ": type" immediately after
        choice [
            pToken COLON ->>- pPretype
                |>> fun (tokColon, tpe) ->
                    mkNode (AST.Expr.Ascription(tpe, node))
                           tokColon.Begin node.Pos.Begin tpe.Pos.End
            preturn node
        ]

/// Parse an assert(...) expression.
let pAssert =
    pToken ASSERT ->>- (pToken LPAREN >>- pSimpleExpr) ->>- pToken RPAREN
        |>> fun ((tok1, expr), tok2) ->
            mkNode (AST.Expr.Assertion expr) tok1.Begin tok1.Begin tok2.End


/// Parse an expression between curly brackets.
let pCurlyExpr =
    pToken LCURLY >>- pExpr ->> pToken RCURLY


/// Parse a type declaration.
let pType =
    pToken TYPE ->>- pIdent ->>-
        (pToken EQ >>- pPretype) ->>-
        (pToken SEMI >>- pExpr)
            |>> fun (((tok, (_, name)), tpe), scope) ->
                mkNode (AST.Expr.Type (name, tpe, scope))
                       tok.Begin tok.Begin scope.Pos.End


/// Parse a union value constructor.
let pUnionCons =
    pIdent ->>- (pToken LCURLY >>- pSimpleExpr) ->>- pToken RCURLY
        |>> fun (((tok1, label), expr), tok2) ->
            mkNode (AST.Expr.UnionCons (label, expr)) tok1.Begin tok1.Begin tok2.End


/// Parse a variable, producing an AST node with a Var expression.
let pVariable =
    pIdent
        |>> fun (tok, name) ->
            mkNode (AST.Expr.Var name) tok.Begin tok.Begin tok.End


/// Parse a non-empty sequence of identifiers (representing struct fields) with
/// initialized with simple expressions, separated by semicolons.
let pFieldInitSeq =
    /// Parse an identifier followed by an equal and a simple expression. Wrap
    /// the result in a single-element list (handy for accumulation using
    /// chainl1 below).
    let pFieldInit = pIdent ->>- (pToken EQ >>- pSimpleExpr)
                        |>> fun ((_, name), expr) -> [(name, expr)]

    chainl1 pFieldInit
        (pToken SEMI
            |>> fun _ ->
                fun acc fInit ->
                    // fInit (produced by pFieldInit above) contains a pair with
                    // an field name and simple expression; accumulate it with acc
                    List.append acc fInit)


/// Parse a struct value construction.
let pStructCons =
    pToken STRUCT ->>- (pToken LCURLY >>- pFieldInitSeq) ->>- pToken RCURLY
        |>> fun ((tok1, fields), tok2) ->
            mkNode (AST.Expr.StructCons fields) tok1.Begin tok1.Begin tok2.End

let pCopy = 
    pToken COPY ->>- (pToken LPAREN >>- pSimpleExpr) ->>- pToken RPAREN
    |>> fun ((tok1, expr), tok2) ->
            mkNode (AST.Expr.Copy expr) tok1.Begin tok1.Begin tok2.End

let pDeepCopy = 
    pToken DEEPCOPY ->>- (pToken LPAREN >>- pSimpleExpr) ->>- pToken RPAREN
    |>> fun ((tok1, expr), tok2) ->
            mkNode (AST.Expr.DeepCopy expr) tok1.Begin tok1.Begin tok2.End

/// Parse a sequence of one or more dot-separated identifiers (representing
/// field names in a sequence of fields selections, e.g. 'field1.field2.field3').
let pFieldDotSeq =
    /// Parse a field name (as an identifier) and wrap it in a list (handy for
    /// accumulation using chainl1 below).
    let pField = pIdent
                    |>> fun x -> [x]

    chainl1 pField
        (pToken DOT
            |>> fun _ ->
                fun acc field ->
                    acc @ field)

/// Parse a array value construction.
let pArrayCons =
    pToken ARRAY ->>- (pToken LPAREN >>- pSimpleExpr) ->>- (pToken COMMA >>- pSimpleExpr ->>- pToken RPAREN)
        |>> fun ((tok1, numberOfElements), (initialValue, tok2)) ->
            mkNode (AST.Expr.ArrayCons (numberOfElements, initialValue)) tok1.Begin tok1.Begin tok2.End


/// Parse a array value construction.
let pArrayElem =
    pToken ARRAYELEM ->>- (pToken LPAREN >>- pVariable) ->>- (pToken COMMA >>- pSimpleExpr ->>- pToken RPAREN)
        |>> fun ((tok1, name), (index, tok2)) ->
            mkNode (AST.Expr.ArrayElem (name, index)) tok1.Begin tok1.Begin tok2.End

let pArrayLength =
    pToken ARRAYLENGTH ->>- (pToken LPAREN >>- pVariable) ->>- pToken RPAREN
        |>> fun ((tok1, name), tok2) ->
            mkNode (AST.Expr.ArrayLength name) tok1.Begin tok1.Begin tok2.End

let pSlice =
    pToken SLICE ->>- (pToken LPAREN >>- pSimpleExpr) ->>- (pToken COMMA >>- pSimpleExpr) ->>- (pToken COMMA >>- pSimpleExpr ->>- pToken RPAREN)
        |>> fun (((tokSlice, arrayExpr), loExpr), (hiExpr, tokR)) ->
            let loopVarName = "__slice_i"

            let sizeWithoutOffset =
                mkNode (AST.Expr.BinNumOp (AST.NumericalOp.Sub, hiExpr, loExpr))
                       loExpr.Pos.Begin loExpr.Pos.Begin hiExpr.Pos.End

            let sizeExpr =
                mkNode (AST.Expr.BinNumOp (AST.NumericalOp.Add,
                                            sizeWithoutOffset,
                                            mkNode (AST.Expr.IntVal 1) loExpr.Pos.Begin loExpr.Pos.Begin loExpr.Pos.Begin))
                       tokSlice.Begin sizeWithoutOffset.Pos.Begin tokR.End

            let arrayInit =
                mkNode (AST.Expr.ArrayElem (arrayExpr, loExpr))
                       tokSlice.Begin arrayExpr.Pos.Begin loExpr.Pos.End

            let arrayCons =
                mkNode (AST.Expr.ArrayCons (sizeExpr, arrayInit))
                       tokSlice.Begin tokSlice.Begin tokR.End

            let resultArrayVarName = "__slice_array"
            let resultArrayVar =
                mkNode (AST.Expr.Var resultArrayVarName)
                       tokSlice.Begin tokSlice.Begin tokR.End

            let loopIndexVar =
                mkNode (AST.Expr.Var loopVarName)
                       tokSlice.Begin tokSlice.Begin tokR.End

            let stepExpr =
                let increment =
                    mkNode (AST.Expr.BinNumOp (AST.NumericalOp.Add,
                                                loopIndexVar,
                                                mkNode (AST.Expr.IntVal 1) tokSlice.Begin tokSlice.Begin tokSlice.Begin))
                           tokSlice.Begin loopIndexVar.Pos.Begin tokR.End
                mkNode (AST.Expr.Assign (loopIndexVar, increment))
                       tokSlice.Begin loopIndexVar.Pos.Begin increment.Pos.End

            let condExpr =
                mkNode (AST.Expr.BinRelOp (AST.RelationalOp.Less, loopIndexVar, sizeExpr))
                       tokSlice.Begin loopIndexVar.Pos.Begin sizeExpr.Pos.End

            let srcIndex =
                mkNode (AST.Expr.BinNumOp (AST.NumericalOp.Add,
                                            loExpr,
                                            loopIndexVar))
                       loExpr.Pos.Begin loExpr.Pos.Begin tokR.End

            let readElem =
                mkNode (AST.Expr.ArrayElem (arrayExpr, srcIndex))
                       tokSlice.Begin arrayExpr.Pos.Begin srcIndex.Pos.End

            let writeElemIndex =
                mkNode (AST.Expr.Var loopVarName)
                       tokSlice.Begin tokSlice.Begin tokR.End

            let writeElem =
                mkNode (AST.Expr.ArrayElem (resultArrayVar, writeElemIndex))
                       tokSlice.Begin resultArrayVar.Pos.Begin writeElemIndex.Pos.End

            let bodyExpr =
                mkNode (AST.Expr.Assign (writeElem, readElem))
                       tokSlice.Begin writeElem.Pos.Begin readElem.Pos.End

            let forExpr =
                mkNode (AST.Expr.For (loopVarName,
                                      mkNode (AST.Expr.IntVal 0) tokSlice.Begin tokSlice.Begin tokSlice.Begin,
                                      condExpr,
                                      stepExpr,
                                      bodyExpr))
                       tokSlice.Begin tokSlice.Begin tokR.End

            let seqExpr =
                mkNode (AST.Expr.Seq [forExpr; resultArrayVar])
                       tokSlice.Begin tokSlice.Begin tokR.End

            mkNode (AST.Expr.Let (resultArrayVarName, arrayCons, seqExpr))
                   tokSlice.Begin tokSlice.Begin tokR.End


/// Parse a primary expression.
let pPrimary = choice [
                    pToken LPAREN >>- pSimpleExpr ->> pToken RPAREN
                    pValue
                    pUnionCons // IMPORTANT: try parsing this before 'pVariable'
                    pVariable
                    pStructCons
                    pCopy
                    pDeepCopy
                    pArrayCons
                    pSlice
                    pArrayElem
                    pArrayLength
               ] >>= fun node ->
                    // If the expression is followed by a dot, then it is a
                    // field selection. If so, parse and accumulate as many
                    // nested field selections as possible (e.g.
                    // 'expr.field1.field2.field3') and create corresponding
                    // nested AST FieldSelect nodes. Otherwise, return the
                    // AST node as it is.
                    choice [
                        pToken DOT >>-
                             pFieldDotSeq
                                |>> fun fields ->
                                    // Fold over all parsed fields to create
                                    // nested AST FieldSelect nodes.
                                    List.fold
                                        (fun acc (tok, field) ->
                                            mkNode (AST.Expr.FieldSelect (acc, field))
                                                   tok.Begin acc.Pos.Begin tok.End)
                                        node fields
                        preturn node
                    ] >>= fun node ->
                        // Check if the expression is followed by a left
                        // parenthesis: if so, it is a function application
                        // (a.k.a. function call). Otherwise, return the
                        // AST node as it is.
                        choice [
                            pParenSimpleExprCommaSeq
                                |>> fun (args, tok) ->
                                    mkNode (AST.Expr.Application (node, args))
                                           node.Pos.Begin node.Pos.Begin tok.End
                            preturn node
                        ]


/// Parse an ascription: a primary expression with (optional) type annotation.
let pAscriptionExpr =
    pPrimary >>= fun node ->
        // Check whether there is a colon and a pretype after the primary
        // expression: if so, create an AST node for a type ascription.
        // Otherwise, return the previously-parsed AST node as it is.
        choice [
            pToken COLON ->>- pPretype
                |>> fun (tok, tpe) ->
                    mkNode (AST.Expr.Ascription (tpe, node))
                           tok.Begin node.Pos.Begin tpe.Pos.End
            preturn node
        ]


/// Parse a unary expression.
let pUnaryExpr' = choice [
    pToken NOT ->>- pUnaryExpr
        |>> fun (tok, arg) ->
            mkNode (AST.Expr.Not arg) tok.Begin tok.Begin arg.Pos.End
    pReadInt
    pReadFloat
    pPrint
    pSqrt
    pPrintLn
    pAssert
    pAscriptionExpr
]


/// Parse a multiplicative expression.
let pMultExpr =
    chainl1 pUnaryExpr
        (choice [
            pToken TIMES
                |>> fun tok ->
                    fun acc rhs ->
                        mkNode (AST.Expr.BinNumOp (AST.NumericalOp.Mult, acc, rhs))
                               tok.Begin acc.Pos.Begin rhs.Pos.End
            pToken DIVIDED
                |>> fun tok ->
                    fun acc rhs ->
                        mkNode (AST.Expr.BinNumOp (AST.NumericalOp.Div, acc, rhs))
                                tok.Begin acc.Pos.Begin rhs.Pos.Begin
            pToken MODULO
                |>> fun tok ->
                    fun acc rhs ->
                        mkNode (AST.Expr.BinNumOp (AST.NumericalOp.Mod, acc, rhs))
                                tok.Begin acc.Pos.Begin rhs.Pos.Begin
        ])


/// Parse an additive expression.
let pAddExpr =
    chainl1 pMultExpr
        (choice [
            pToken PLUS
                |>> fun tok ->
                    fun acc rhs ->
                        mkNode (AST.Expr.BinNumOp (AST.NumericalOp.Add, acc, rhs))
                               tok.Begin acc.Pos.Begin rhs.Pos.End
                               
            pToken MINUS
                |>> fun tok ->
                    fun acc rhs ->
                        mkNode (AST.Expr.BinNumOp (AST.NumericalOp.Sub, acc, rhs))
                               tok.Begin acc.Pos.Begin rhs.Pos.End
        ])

/// Parse a relational expression.
let pRelExpr =
    pAddExpr >>= fun lhs ->
        choice [
            pToken EQ ->>- pAddExpr
                |>> fun (tok, rhs) ->
                    mkNode (AST.Expr.BinRelOp (AST.RelationalOp.Eq, lhs, rhs))
                           tok.Begin lhs.Pos.Begin rhs.Pos.End
            pToken LT ->>- pAddExpr
                |>> fun (tok, rhs) ->
                    mkNode (AST.Expr.BinRelOp (AST.RelationalOp.Less, lhs, rhs))
                           tok.Begin lhs.Pos.Begin rhs.Pos.End
            pToken LTEQ ->>- pAddExpr
                |>> fun (tok, rhs) ->
                    mkNode (AST.Expr.BinRelOp (AST.RelationalOp.LessEq, lhs, rhs))
                           tok.Begin lhs.Pos.Begin rhs.Pos.End
            pToken GT ->>- pAddExpr
                |>> fun (tok, rhs) ->
                    mkNode (AST.Expr.BinRelOp (AST.RelationalOp.Greater, lhs, rhs))
                           tok.Begin lhs.Pos.Begin rhs.Pos.End
            preturn lhs // Default case if no operator above matches
        ]


/// Parse a logical 'and' expression.
let pAndExpr =
    chainl1 pRelExpr
        (choice [
            (pToken AND
                |>> fun tok ->
                    fun acc rhs ->
                        mkNode (AST.Expr.BinLogicOp (AST.LogicOp.And, acc, rhs))
                            tok.Begin acc.Pos.Begin rhs.Pos.End)

            (pToken ANDS
                |>> fun tok ->
                    fun acc rhs ->
                        mkNode (AST.Expr.BinLogicOp (AST.LogicOp.AndS, acc, rhs))
                            tok.Begin acc.Pos.Begin rhs.Pos.End)
        ])


/// Parse a logical 'or' expression.
let pOrExpr =
    chainl1 pAndExpr
        (choice [
            (pToken OR
                |>> fun tok ->
                    fun acc rhs ->
                        mkNode (AST.Expr.BinLogicOp (AST.LogicOp.Or, acc, rhs))
                               tok.Begin acc.Pos.Begin rhs.Pos.End)
            (pToken XOR
                |>> fun tok ->
                    fun acc rhs ->
                        mkNode (AST.Expr.BinLogicOp (AST.LogicOp.Xor, acc, rhs))
                               tok.Begin acc.Pos.Begin rhs.Pos.End)
            (pToken ORS
                |>> fun tok ->
                    fun acc rhs ->
                        mkNode (AST.Expr.BinLogicOp (AST.LogicOp.OrS, acc, rhs))
                               tok.Begin acc.Pos.Begin rhs.Pos.End)
        ])
        
/// Parse an 'if-then-else' expression.
let pIfExpr = choice [
    pToken IF ->>- pSimpleExpr ->>-
        (pToken THEN >>- pSimpleExpr) ->>-
        (pToken ELSE >>- pSimpleExpr)
            |>> fun (((tok, condN), thenN), elseN) ->
                    mkNode (AST.Expr.If (condN, thenN, elseN))
                           tok.Begin tok.Begin elseN.Pos.End
]


/// Parse a non-empty sequence of pattern matching cases separated by semicolons.
let pMatchCases =
    /// Parse a single pattern matching case and wrap the result in a
    /// single-element list (handy for accumulation using chainl1 below).
    let pMatchCase = pIdent ->>- (pToken LCURLY >>- pIdent) ->>- pToken RCURLY ->>-
                        (pToken RARROW >>- pSimpleExpr)
                            |>> fun ((((_, label), (_, variable)), _), expr) ->
                                [(label, variable, expr)]

    chainl1 pMatchCase
        (pToken SEMI
            |>> fun _ ->
                fun acc matchCase ->
                    // matchCase (produced by pMatchCase above) contains a triple
                    // with label, variable, and expression; accumulate it with acc
                    List.append acc matchCase)

/// Xifeng's original for implementation with scoped variable
let pForScopedExpr =
    pToken LET >>- pToken MUTABLE >>- pIdent ->>-   // let mutable x
        (pToken EQ >>- pSimpleExpr) ->>-                // =
        (pToken SEMI >>- pSimpleExpr) ->>-              // ; ec
        (pToken SEMI >>- pSimpleExpr)              // ; eu
    |>> fun ((((tok, name), ei), ec), eu) ->
        (((((tok, name), ei), ec), eu), None)

/// for each loop syntax sugar
let pForInExpr =
    pIdent ->>- (pToken IN >>- pSimpleExpr)
    |>> fun ((tok, varName), arrayExpr) ->
        let loopVarName = "__i"
        let initExpr = mkNode (AST.Expr.IntVal 0) tok.Begin tok.Begin tok.End
        let condExpr = 
            mkNode (AST.Expr.BinRelOp(AST.RelationalOp.Less,
                                      mkNode (AST.Expr.Var loopVarName) tok.Begin tok.Begin tok.End,
                                      mkNode (AST.Expr.ArrayLength arrayExpr) tok.Begin tok.Begin arrayExpr.Pos.End))
                   tok.Begin tok.Begin arrayExpr.Pos.End
        let addOneExpr = mkNode (AST.Expr.BinNumOp(AST.NumericalOp.Add,
                                                    mkNode (AST.Expr.Var loopVarName) tok.Begin tok.Begin tok.End,
                                                    mkNode (AST.Expr.IntVal 1) tok.Begin tok.Begin tok.End))
                                tok.Begin tok.Begin tok.End
        let stepExpr = 
            mkNode (AST.Expr.Assign(mkNode (AST.Expr.Var loopVarName) tok.Begin tok.Begin tok.End,
                                    addOneExpr))
                   tok.Begin tok.Begin tok.End
        (((((tok, loopVarName), initExpr), condExpr), stepExpr), Some(varName, arrayExpr))

/// Parse a "simple" expression, which (unlike the more general 'pExpr') cannot
/// result in a 'Seq'uence of sub-expressions, unless they are explicitly
/// enclosed in curly brackets.
let pSimpleExpr' = choice [
    pPrimary ->>- pToken LARROW ->>- pSimpleExpr
        |>> fun ((lhs, tok), rhs) ->
            mkNode (AST.Expr.Assign (lhs, rhs)) tok.Begin lhs.Pos.Begin rhs.Pos.End
    pIfExpr
    pOrExpr
    pCurlyExpr
    pToken WHILE ->>- pSimpleExpr ->>- (pToken DO >>- pSimpleExpr)
        |>> fun ((tok, cond), body) ->
            mkNode (AST.Expr.While (cond, body)) tok.Begin tok.Begin body.Pos.End

    pToken DO ->>- pSimpleExpr ->>- (pToken WHILE >>- pSimpleExpr)
        |>> fun ((tok, body), cond) ->
            mkNode (AST.Expr.DoWhile (body, cond)) tok.Begin tok.Begin cond.Pos.End
    
    pToken FOR ->>-
        (pToken LPAREN >>-                              // (
        choice [
            pForInExpr
            pForScopedExpr
        ] ->>-
        (pToken RPAREN >>- pSimpleExpr))                //) eb
            |>> fun(tokFor,((((((_,name),ei),ec),eu),subst),eb)) ->
                let finalBody = 
                    match subst with
                    | None -> eb
                    | Some(varName, arrayExpr) ->
                        let indexVar = mkNode (AST.Expr.Var "__i") tokFor.Begin tokFor.Begin tokFor.End
                        let arrayElemExpr = mkNode (AST.Expr.ArrayElem(arrayExpr, indexVar)) tokFor.Begin tokFor.Begin tokFor.End
                        ASTUtil.subst eb varName arrayElemExpr
                mkNode (AST.Expr.For (name, ei, ec, eu, finalBody))
                       tokFor.Begin tokFor.Begin eb.Pos.End

    // Lambda expression: fun (args) -> body
    pToken FUN ->>-
        pParenIdentTypesCommaSeq ->>- (pToken RARROW >>- pSimpleExpr)
            |>> fun ((tok, args), body) ->
                mkNode (AST.Expr.Lambda (args, body)) tok.Begin tok.Begin body.Pos.End
    // Match expression: match expr with { cases }
    pToken MATCH ->>- pSimpleExpr ->>-
        (pToken WITH >>- pToken LCURLY >>- pMatchCases) ->>- pToken RCURLY
            |>> fun (((tok, expr), cases), tok2) ->
                mkNode (AST.Expr.Match (expr, cases)) tok.Begin tok.Begin tok2.End

]


/// Parse a sequence of expressions.
let pSequenceExpr' = choice [
    pCurlyExpr >>= fun node ->
        // We do not require a semicolon between an expression in curly brackets
        // and the next expression. Check whether there is an optional semicolon
        // and another expression after the closing bracket: if so, 'node' is
        // part of a sequence. Otherwise, return 'node' as it is.
        choice [
            choice [
              pToken SEMI >>- pExpr
              pExpr
            ] |>> fun node2 ->
                    match node2.Expr with
                    | AST.Expr.Seq nodes ->
                        // Flatten the sequence (not necessary but keeps AST flat)
                        mkNode (AST.Expr.Seq (node :: nodes))
                               node.Pos.End node.Pos.Begin node2.Pos.End
                    | _ ->
                        mkNode (AST.Expr.Seq [node; node2])
                               node.Pos.End node.Pos.Begin node2.Pos.End
            preturn node
        ]
    pSimpleExpr >>= fun node ->
        // Check whether there is a semicolon and an expression after the simple
        // expression: if so, 'node' is part of a sequence. Otherwise, return
        // 'node' as it is.
        choice [
            pToken SEMI ->>- pExpr
                |>> fun (tok, node2) ->
                    match node2.Expr with
                    | AST.Expr.Seq nodes ->
                        // Flatten the sequence (not necessary but keeps AST flat)
                        mkNode (AST.Expr.Seq (node :: nodes))
                               tok.Begin node.Pos.Begin node2.Pos.End
                    | _ ->
                        mkNode (AST.Expr.Seq [node; node2])
                               tok.Begin node.Pos.Begin node2.Pos.End
            preturn node
        ]
]


/// Parse a 'let' binding without type annotation.
let pLet =
    pToken LET ->>- pIdent ->>-
        (pToken EQ >>- pSimpleExpr) ->>-
        (pToken SEMI >>- pExpr)
            |>> fun (((tok, (_, name)), init), scope) ->
                mkNode (AST.Expr.Let (name, init, scope))
                       tok.Begin tok.Begin scope.Pos.End


/// Parse a 'let' binding with a type annotation.
let pLetT =
    pToken LET ->>- pIdent ->>-
        (pToken COLON >>- pPretype) ->>-
        (pToken EQ >>- pSimpleExpr) ->>-
        (pToken SEMI >>- pExpr)
            |>> fun ((((tok, (_, name)), tpe), init), scope) ->
                mkNode (AST.Expr.LetT (name, tpe, init, scope))
                       tok.Begin tok.Begin scope.Pos.End


/// Parse a mutable 'let' binding.
let pLetMut =
    pToken LET ->>- pToken MUTABLE ->>- pIdent ->>-
        (pToken EQ >>- pSimpleExpr) ->>-
        (pToken SEMI >>- pExpr)
            |>> fun ((((tok, _), (_, name)), init), scope) ->
                mkNode (AST.Expr.LetMut (name, init, scope))
                       tok.Begin tok.Begin scope.Pos.End


/// Parse any Hygge expression.
let pExpr' = choice [
    pType
    // Function declaration. We rewrite it into a let-expression that declares a
    // variable and initializes it with a lambda term.
    pToken FUN ->>- pIdent ->>-
        pParenIdentTypesCommaSeq ->>-
        (pToken COLON >>- pPretype) ->>-
        (pToken EQ >>- pSimpleExpr) ->>-
        (pToken SEMI >>- pExpr)
            |>> fun (((((tok, (_, name)), args), retType), body), scope) ->
                let argTypes = List.map snd args
                let funPretype = AST.Pretype.TFun (argTypes, retType)
                let funPretypeNode = mkPretypeNode funPretype
                                                   tok.Begin tok.Begin retType.Pos.End
                let lambda = mkNode (AST.Expr.Lambda (args, body))
                                    tok.Begin tok.Begin body.Pos.End
                mkNode (AST.Expr.LetT (name, funPretypeNode, lambda, scope))
                       tok.Begin tok.Begin scope.Pos.End
    pLetMut
    pLetT
    pLet
    pSequenceExpr
]


// Initialize the forward references defined at the beginning of this file.
pPretypeRef.Value <- pPretype'
pExprRef.Value <- pExpr'
pSequenceExprRef.Value <- pSequenceExpr'
pSimpleExprRef.Value <- pSimpleExpr'
pUnaryExprRef.Value <- pUnaryExpr'


/// Parse a whole Hygge program (i.e., an expression followed by EOF); if the
/// parsing fails, report a summary of all errors.
let pProgram: TokenStream -> Result<AST.UntypedAST, Lexer.Position * string> =
    pExpr ->> pToken EOF  |>  summarizeErrors


let isCV (name, scope) = Set.contains name (ASTUtil.capturedVars(scope))


let rec fixLetMut (node: Node<'a,'b>): Node<'a,'b> =
    match node.Expr with
    | LetMut(name, init, scope) when isCV(name, scope) ->
        let init' = fixLetMut init
        let structNode = {node with Expr = StructCons([("value", init')])}
        let scopeSubst = ASTUtil.subst scope name {node with Expr = FieldSelect({node with Expr = Var(name)}, "value")}
        {node with Expr = Let(name, structNode, fixLetMut scopeSubst)}
    | LetMut(name, init, scope) ->
        {node with Expr = LetMut(name, fixLetMut init, fixLetMut scope)}
    | Let(name, init, scope) ->
        {node with Expr = Let(name, fixLetMut init, fixLetMut scope)}
    | LetT(name, tpe, init, scope) ->
        {node with Expr = LetT(name, tpe, fixLetMut init, fixLetMut scope)}
    | Lambda(args, body) ->
        {node with Expr = Lambda(args, fixLetMut body)}
    | Seq(nodes) ->
        {node with Expr = Seq(List.map fixLetMut nodes)}
    | BinNumOp(op, lhs, rhs) ->
        {node with Expr = BinNumOp(op, fixLetMut lhs, fixLetMut rhs)}
    | BinLogicOp(op, lhs, rhs) ->
        {node with Expr = BinLogicOp(op, fixLetMut lhs, fixLetMut rhs)}
    | BinRelOp(op, lhs, rhs) ->
        {node with Expr = BinRelOp(op, fixLetMut lhs, fixLetMut rhs)}
    | Sqrt(arg) -> {node with Expr = Sqrt(fixLetMut arg)}
    | Not(arg) -> {node with Expr = Not(fixLetMut arg)}
    | Print(arg) -> {node with Expr = Print(fixLetMut arg)}
    | PrintLn(arg) -> {node with Expr = PrintLn(fixLetMut arg)}
    | Assertion(arg) -> {node with Expr = Assertion(fixLetMut arg)}
    | Ascription(tpe, arg) -> {node with Expr = Ascription(tpe, fixLetMut arg)}
    | UnionCons(label, arg) -> {node with Expr = UnionCons(label, fixLetMut arg)}
    | ArrayLength(arg) -> {node with Expr = ArrayLength(fixLetMut arg)}
    | Copy(arg) -> {node with Expr = Copy(fixLetMut arg)}
    | DeepCopy(arg) -> {node with Expr = DeepCopy(fixLetMut arg)}
    | If(cond, ifTrue, ifFalse) ->
        {node with Expr = If(fixLetMut cond, fixLetMut ifTrue, fixLetMut ifFalse)}
    | Type(name, tpe, scope) ->
        {node with Expr = Type(name, tpe, fixLetMut scope)}
    | While(cond, body) ->
        {node with Expr = While(fixLetMut cond, fixLetMut body)}
    | DoWhile(body, cond) ->
        {node with Expr = DoWhile(fixLetMut body, fixLetMut cond)}
    | For(name, init, cond, step, body) ->
        {node with Expr = For(name, fixLetMut init, fixLetMut cond, fixLetMut step, fixLetMut body)}
    | Application(expr, args) ->
        {node with Expr = Application(fixLetMut expr, List.map fixLetMut args)}
    | StructCons(fields) ->
        {node with Expr = StructCons(List.map (fun (n, e) -> (n, fixLetMut e)) fields)}
    | FieldSelect(target, field) ->
        {node with Expr = FieldSelect(fixLetMut target, field)}
    | Assign(target, expr) ->
        {node with Expr = Assign(fixLetMut target, fixLetMut expr)}
    | Match(expr, cases) ->
        {node with Expr = Match(fixLetMut expr, List.map (fun (l, v, cont) -> (l, v, fixLetMut cont)) cases)}
    | ArrayCons(size, init) ->
        {node with Expr = ArrayCons(fixLetMut size, fixLetMut init)}
    | ArrayElem(name, index) ->
        {node with Expr = ArrayElem(fixLetMut name, fixLetMut index)}
    | UnitVal | BoolVal(_) | IntVal(_) | FloatVal(_) | StringVal(_)
    | Pointer(_) | Var(_) | ReadInt | ReadFloat -> node

/// Parse the given array of 'tokens' with positions and return either Ok
/// UntypedAST, or an Error with a position and a message.
let parse (tokens: array<TokenWithPos>): Result<AST.UntypedAST, Lexer.Position * string> =
    let stream = {
        // TODO: use immarray when available. See:
        // https://github.com/fsharp/fslang-design/blob/main/RFCs/FS-1094-immarray.md
        Tokens = tokens
        Index = 0
        Expected = ResizeArray 512
    }
    
    match pProgram stream with
    | Ok(ast) -> Ok(fixLetMut ast)
    | Error(e) -> Error(e)

