// hyggec - The didactic compiler for the Hygge programming language.
// Copyright (C) 2026 Technical University of Denmark
// Author: Alceste Scalas <alcsc@dtu.dk>
// Released under the MIT license (see LICENSE.md for details)

/// Tokenizer for the Hygge programming language.
module Lexer

open System.Text.RegularExpressions


// fsharplint:disable enumCaseNames
/// A token, possibly carrying a value.
type Token =
    /// Left parenthesis.
    | LPAREN
    /// Right parenthesis.
    | RPAREN
    /// Left curly bracket.
    | LCURLY
    /// Right curly bracket.
    | RCURLY
    /// Plus sign.
    | PLUS
    /// Minus sign
    | MINUS
    /// Multiplication sign.
    | TIMES
    /// Division sign
    | DIVIDED
    /// Modulo sign
    | MODULO
    /// Logical 'and'.
    | AND
    /// Logical 'or'.
    | OR
    /// Logical 'xor'.
    | XOR
    /// Short-circuit logical 'ands'
    | ANDS
    /// Short-circuit logical "ors"
    | ORS
    /// Logical 'not'.
    | NOT
    /// Square root function
    | SQRT
    /// Equality symbol.
    | EQ
    /// Less-than symbol.
    | LT
    /// Less-than-or-equal-to symbol.
    | LTEQ
    /// Greater-than symbol.
    | GT
    /// Left arrow (assignment operator).
    | LARROW
    /// Right arrow (function type operator).
    | RARROW
    /// Semicolon.
    | SEMI
    /// Comma.
    | COMMA
    /// Colon, used e.g. in type ascriptions.
    | COLON
    /// Keyword 'if'.
    | IF
    /// Keyword 'then'.
    | THEN
    /// Keyword 'else'.
    | ELSE
    /// Keyword 'let'.
    | LET
    /// Keyword 'readInt'.
    | READ_INT
    /// Keyword 'readFloat'.
    | READ_FLOAT
    /// Keyword 'print'.
    | PRINT
    /// Keyword 'println'.
    | PRINTLN
    /// Keyword 'assert'.
    | ASSERT
    /// Keyword 'type'.
    | TYPE
    /// Keyword 'mutable'.
    | MUTABLE
    /// Keyword 'while'.
    | WHILE
    /// Keyword 'do'.
    | DO
    /// Keyword 'for'
    | FOR
    /// Keyword 'fun'.
    | FUN
    /// Keyword 'struct'.
    | STRUCT
    /// Keyword 'union'.
    | UNION
    /// Keyword 'match'.
    | MATCH
    /// Keyword 'with'.
    | WITH
    /// Dot, used for field selection.
    | DOT
    /// Integer literal.
    | LIT_INT of value: int
    /// Floating-point literal.
    | LIT_FLOAT of value: single
    /// Boolean literal.
    | LIT_BOOL of value: bool
    /// String literal.
    | LIT_STRING of value: string
    /// Unit literal.
    | LIT_UNIT
    /// Generic identifier (might result in a variable, pretype, etc.).
    | IDENT of value: string
    /// End of file.
    | EOF
    /// keyword `array`
    | ARRAY
    /// Keyword `arrayElem`
    | ARRAYELEM
    /// Keyword `arrayLength`
    | ARRAYLENGTH
    /// Keyword `in`
    | IN
    /// Keyword `slice`
    | SLICE


/// Position in a file.
type Position =
    { /// Name of the file this position refers to.
      Filename: string
      /// Offset (in number of characters) from the beginning of the file.
      Offset: int
      /// Line number in the file.
      Line: int
      /// Column number in the file.
      Column: int
    }


/// A token with begin and end positions in the originating source file.
type TokenWithPos =
    { /// The token, possibly carrying a value.
      Token: Token
      /// Position where the token begins.
      Begin: Position
      /// Position where the token ends.
      End: Position
    } with override this.ToString() =
                let lineRowSpan = $"{this.Begin.Line}:{this.Begin.Column}-{this.End.Line}:{this.End.Column}"
                let offsetSpan = $"{this.Begin.Offset}-{this.End.Offset}"
                $"%O{this.Token} ({lineRowSpan}, offset {offsetSpan})"


/// Recursively tokenize the given 'input' string, using 'pos' as the current
/// position, and accumulating the accepted tokens with positions in 'acc'.
/// Return either Ok (), or Error with an error message.
[<TailCall>]
let rec internal tokenizeRec (input: string) (pos: Position)
                             (acc: ResizeArray<TokenWithPos>): Result<unit,string> =
    match input[pos.Offset..] with
    | "" -> // We reached the end of the input string: add EOF and return Ok
        acc.Add { Token = EOF; Begin = pos; End = pos }
        Ok ()

    | Whitespace pos pos'
    | Comment    pos pos'
    | Newline    pos pos' ->
        // Just keep tokenizing the rest of the input at position pos'
        tokenizeRec input pos' acc

    // IMPORTANT: longer symbols must be matched first, otherwise they may be
    // tokenized as multiple shorter symbols. E.g., if the rule for token
    // LIT_UNIT is moved after LPAREN and RPAREN, then LPAREN and RPAREN will be
    // matched first and LIT_UNIT will never be produced.
    | Symbol "()" LIT_UNIT pos (accepted, pos')
    | Symbol "<-" LARROW   pos (accepted, pos')
    | Symbol "->" RARROW   pos (accepted, pos')
    | Symbol "("  LPAREN   pos (accepted, pos')
    | Symbol ")"  RPAREN   pos (accepted, pos')
    | Symbol "{"  LCURLY   pos (accepted, pos')
    | Symbol "}"  RCURLY   pos (accepted, pos')
    | Symbol "+"  PLUS     pos (accepted, pos')
    | Symbol "-"  MINUS    pos (accepted, pos')
    | Symbol "*"  TIMES    pos (accepted, pos')
    | Symbol "/"  DIVIDED  pos (accepted, pos')
    | Symbol "%"  MODULO   pos (accepted, pos')
    | Symbol "<="  LTEQ    pos (accepted, pos')
    | Symbol "="  EQ       pos (accepted, pos')
    | Symbol "<"  LT       pos (accepted, pos')
    | Symbol ">"  GT       pos (accepted, pos')
    | Symbol ","  COMMA    pos (accepted, pos')
    | Symbol ";"  SEMI     pos (accepted, pos')
    | Symbol ":"  COLON    pos (accepted, pos')
    | Symbol "&&" ANDS     pos (accepted, pos')
    | Symbol "||" ORS      pos (accepted, pos')
    | Regex @"(\d+\.?\d*|\.\d+)([eE][+-]?\d+)?f" mkFloatLit       pos (accepted, pos')
    | Regex @"\d+"                               mkIntegerLit     pos (accepted, pos')
    | Regex "\"(\\\\\"|[^\"])*\""                mkStringLit      pos (accepted, pos')
    | Regex @"[a-zA-Z_][a-zA-Z0-9_]*"            mkKeywordOrIdent pos (accepted, pos')
    // We tokenize the dot here to give precedence to floating-point numbers
    | Symbol "."  DOT      pos (accepted, pos') ->
        // Add the accepted token to acc (in reverse order for performance) and
        // keep tokenizing the rest of the input at position pos'
        acc.Add accepted
        tokenizeRec input pos' acc

    | other -> // There are more input characters but they do not match any rule
        /// The first 8 (at most) characters of the remaining input
        let len = min (other.Length-1) 7
        Error $"{pos.Filename}:{pos.Line}:{pos.Column}: unrecognized input: {other[..len]}"

/// Convert a string into a keyword token or an identifier
and internal mkKeywordOrIdent (s: string) =
    match s with
    | "and" -> AND
    | "or" -> OR
    | "xor" -> XOR
    | "not" -> NOT
    | "sqrt" -> SQRT
    | "if" -> IF
    | "then" -> THEN
    | "else" -> ELSE
    | "let" -> LET
    | "readInt" -> READ_INT
    | "readFloat" -> READ_FLOAT
    | "println" -> PRINTLN
    | "print" -> PRINT
    | "assert" -> ASSERT
    | "type" -> TYPE
    | "mutable" -> MUTABLE
    | "while" -> WHILE
    | "do" -> DO
    | "for" -> FOR
    | "fun" -> FUN
    | "struct" -> STRUCT
    | "union" -> UNION
    | "match" -> MATCH
    | "with" -> WITH
    | "true" -> LIT_BOOL true
    | "false" -> LIT_BOOL false
    | "array" -> ARRAY
    | "arrayElem" -> ARRAYELEM
    | "arrayLength" -> ARRAYLENGTH
    | "in" -> IN
    | "slice" -> SLICE
    | other -> IDENT other

/// Convert a string into a FloatLit token, after stripping the final 'f'.
and internal mkFloatLit (s: string) = LIT_FLOAT (single s[0..s.Length-2])

/// Convert a string into an IntegerLit.
and internal mkIntegerLit (s: string) = LIT_INT (int s)

/// Convert a string into a BoolLit.
and internal mkBoolLit (s: string) = LIT_BOOL (s = "true")

/// Convert a string into a StringLit token, after stripping the initial and
/// final '"' and unescaping internal quotes.
and internal mkStringLit (s: string) =
    let str = s[1..s.Length-2].Replace("\\\"", "\"")
    LIT_STRING str

/// Active pattern (used by tokenizeRec) to match 'symbol' at the beginning of
/// 'input' and create 'token' at 'pos'ition. A successful match produces the
/// new token with position and an updated position.
and internal (|Symbol|_|) (symbol: string) (token: Token) (pos: Position) (input: string) =
    assert (symbol.Length >= 1)
    if input.StartsWith symbol then
        let accepted = { Token = token
                         Begin = pos
                         End = { pos with Offset = pos.Offset + symbol.Length - 1
                                          Column = pos.Column + symbol.Length - 1 } }
        let pos' = { pos with Offset = pos.Offset + symbol.Length
                              Column = pos.Column + symbol.Length }
        Some (accepted, pos')
    else None

/// Active pattern (used by tokenizeRec) to match 'regex' at the beginning of
/// 'input'. This active pattern creates a token at 'pos'ition by applying
/// 'toToken' to the string matched by 'regex'. A successful match produces the
/// new token with position and the updated tokenization position.
and internal (|Regex|_|) (regex: string) (toToken: string -> Token) (pos: Position) (input: string) =
    let m = Regex.Match(input, $@"^{regex}")
    if m.Success then
        if m.Length < 1 then
            failwith $"BUG: '{regex}' successfully matches 0 characters at {pos.Filename}:{pos.Line}:{pos.Column}"
        let accepted = { Token = toToken m.Value
                         Begin = pos
                         End = { pos with Offset = pos.Offset + m.Length - 1
                                          Column = pos.Column + m.Length - 1} }
        let pos' = { pos with Offset = pos.Offset + m.Length
                              Column = pos.Column + m.Length }
        Some (accepted, pos')
    else None

/// Active pattern (used by tokenizeRec) matching a whitespace at the beginning
/// of 'input' at 'pos'ition. A successful match produces an the updated
/// tokenization position.
and internal (|Whitespace|_|) (pos: Position) (input: string) =
    let m = Regex.Match(input, @"^[ \t]+")
    if m.Success then
        let pos' = { pos with Offset = pos.Offset + m.Length
                              Column = pos.Column + m.Length }
        Some pos'
    else None

/// Active pattern (used by tokenizeRec) matching a newline at the beginning of
/// 'input' at 'pos'ition. A successful match produces the updated tokenization
/// position.
and internal (|Newline|_|) (pos: Position) (input: string) =
    if input[0] = '\n' || (input[0] = '\r' && input.Length > 1 && input[1] = '\n') then
        let len = if (input.StartsWith '\n') then 1 else 2
        let pos' = { pos with Offset = pos.Offset + len
                              Line = pos.Line + 1
                              Column = 1 }
        Some pos'
    else None

/// Active pattern (used by tokenizeRec) matching a comment at the beginning of
/// 'input' at 'pos'ition. A successful match produces the updated tokenization
/// position.
and internal (|Comment|_|) (pos: Position) (input: string) =
    let m = Regex.Match(input, @"^//[^\n\r]*")
    if m.Success then
        let pos' = { pos with Offset = pos.Offset + m.Length }
        Some pos'
    else None


/// Tokenize the contents of 'filename'. Return either Ok with an array of
/// tokens with positions, or Error with a message.
let tokenize (filename: string): Result<array<TokenWithPos>,string> =
    Log.debug (lazy $"Regex cache size: {Regex.CacheSize}")
    // See https://learn.microsoft.com/en-us/dotnet/api/system.text.regularexpressions.regex.cachesize
    Regex.CacheSize <- max Regex.CacheSize 255
    Log.debug (lazy $"Regex cache size is now: {Regex.CacheSize}")

    /// Result of the file reading operation
    let fileReadRes = try
                          Ok (System.IO.File.ReadAllText filename)
                      with
                          | e -> Error e.Message

    match fileReadRes with
    | Ok content ->
        /// Initial position in the input file
        let initialPos = { Filename = filename; Offset = 0; Line = 1; Column = 1 }
        /// Collection of accepted tokens
        let tokens = ResizeArray 512
        match tokenizeRec content initialPos tokens with
        | Ok () -> Ok (tokens.ToArray())
        | Error s -> Error s
    | Error e -> Error e
