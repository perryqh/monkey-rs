use anyhow::{bail, Result};
use lexer::{
    lexer::Lexer,
    token::{Token, TokenKind},
};

use crate::ast::{
    ArrayLiteral, BlockStatement, CallExpression, Expression, FunctionLiteral, HashLiteral,
    Identifier, IfExpression, IndexExpression, InfixExpression, LetDereferenceStatement,
    LetStatement, PrefixExpression, Program, ReturnStatement, SetLiteral, Statement,
};

#[derive(Debug)]
pub struct Parser {
    peekable_tokens: std::iter::Peekable<std::vec::IntoIter<Token>>,
    current_token: Option<Token>,
}

/// Denotes the precedence of various operators.
#[derive(Debug, PartialEq, PartialOrd, Clone, Copy)]
pub enum Precedence {
    Lowest,
    Equals,
    LessGreater,
    Sum,
    Product,
    Prefix,
    Call,
    Index,
}

fn precedence_from_token(tok: &Token) -> Precedence {
    match &tok.kind {
        TokenKind::Equal => Precedence::Equals,
        TokenKind::NotEqual => Precedence::Equals,
        TokenKind::LT => Precedence::LessGreater,
        TokenKind::GT => Precedence::LessGreater,
        TokenKind::Plus => Precedence::Sum,
        TokenKind::Minus => Precedence::Sum,
        TokenKind::Slash => Precedence::Product,
        TokenKind::Asterisk => Precedence::Product,
        TokenKind::Percent => Precedence::Product,
        TokenKind::LeftParen => Precedence::Call,
        TokenKind::LeftBracket => Precedence::Index,

        _ => Precedence::Lowest,
    }
}

impl Parser {
    pub fn new(lexer: Lexer) -> Self {
        let peekable_tokens = lexer.collect::<Vec<Token>>().into_iter().peekable();
        Self {
            peekable_tokens,
            current_token: None,
        }
    }

    pub fn parse(&mut self) -> Result<Program> {
        let mut prog = Program::new();
        self.next_token()?;

        while self.current_token_is_not(&TokenKind::EOF) {
            let stmt = self.parse_statement()?;
            prog.statements.push(stmt);
            self.next_token()?;
        }

        Ok(prog)
    }

    fn parse_statement(&mut self) -> Result<Statement> {
        match self.current_token_kind()? {
            TokenKind::Let => self.parse_let_statement(),
            TokenKind::Return => self.parse_return_statement(),
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_expression_statement(&mut self) -> Result<Statement> {
        let expression = self.parse_expression(Precedence::Lowest)?;
        if self.peek_token_is(&TokenKind::Semicolon) {
            self.next_token()?;
        }
        Ok(Statement::Expression(expression))
    }

    fn parse_return_statement(&mut self) -> Result<Statement> {
        self.expect_current_token()?;
        self.next_token()?;
        let value = self.parse_expression(Precedence::Lowest)?;
        self.expect_peek_advance(&TokenKind::Semicolon)?;
        Ok(Statement::Return(ReturnStatement {
            return_value: value,
        }))
    }

    fn parse_let_statement(&mut self) -> Result<Statement> {
        self.next_token()?;

        let is_pointer = self.current_token_is(&TokenKind::Asterisk);
        if is_pointer {
            self.next_token()?;
        }
        let name = self.parse_identifier()?;
        self.expect_peek_advance(&TokenKind::Assign)?;
        self.next_token()?;

        let value = self.parse_expression(Precedence::Lowest)?;
        self.expect_peek_advance(&TokenKind::Semicolon)?;

        if is_pointer {
            Ok(Statement::LetDereference(LetDereferenceStatement {
                name,
                value,
            }))
        } else {
            Ok(Statement::Let(LetStatement { name, value }))
        }
    }

    fn infix_parse(&mut self, left: &Expression) -> Option<Result<Expression>> {
        let peek_token = self.peek_token()?;
        match peek_token.kind {
            TokenKind::Plus
            | TokenKind::Minus
            | TokenKind::Asterisk
            | TokenKind::Slash
            | TokenKind::Percent
            | TokenKind::Equal
            | TokenKind::NotEqual
            | TokenKind::LT
            | TokenKind::GT => Some(self.parse_infix_expression(left)),
            TokenKind::LeftParen => Some(self.parse_call_expression(left)),
            TokenKind::LeftBracket => Some(self.parse_index_expression(left)),

            _ => None,
        }
    }

    fn parse_index_expression(&mut self, left: &Expression) -> Result<Expression> {
        self.next_token()?;
        self.next_token()?;

        let idx = Expression::Index(IndexExpression {
            left: Box::new(left.clone()),
            index: Box::new(self.parse_expression(Precedence::Lowest)?),
        });

        self.expect_peek_advance(&TokenKind::RightBracket)?;

        Ok(idx)
    }

    fn parse_block_statement(&mut self) -> Result<Statement> {
        let mut statements = vec![];

        self.next_token()?;
        while self.current_token_is_not(&TokenKind::RightBrace)
            && self.current_token_is_not(&TokenKind::EOF)
        {
            let stmt = self.parse_statement()?;
            statements.push(stmt);
            self.next_token()?;
        }

        Ok(Statement::Block(BlockStatement { statements }))
    }

    fn parse_call_expression(&mut self, left: &Expression) -> Result<Expression> {
        self.next_token()?;

        if self.peek_token_is(&TokenKind::RightParen) {
            self.next_token()?;
            return Ok(Expression::Call(CallExpression {
                function: Box::new(left.clone()),
                arguments: vec![],
            }));
        }

        let arguments = self.parse_expression_list(&TokenKind::RightParen)?;

        Ok(Expression::Call(CallExpression {
            function: Box::new(left.clone()),
            arguments,
        }))
    }

    fn parse_expression_list(&mut self, end: &TokenKind) -> Result<Vec<Expression>> {
        if self.peek_token_is(end) {
            self.next_token()?;
            return Ok(vec![]);
        }

        let mut expressions = vec![];

        self.next_token()?;
        expressions.push(self.parse_expression(Precedence::Lowest)?);

        while self.peek_token_is(&TokenKind::Comma) {
            self.next_token()?;
            self.next_token()?;

            expressions.push(self.parse_expression(Precedence::Lowest)?);
        }

        self.expect_peek_advance(end)?;

        Ok(expressions)
    }

    fn precedence_less_than_peek(&mut self, precedence: &Precedence) -> Result<bool> {
        let peek_token = self.expect_peek_token()?;
        let less_than = (*precedence as u32) < (precedence_from_token(peek_token) as u32);
        Ok(less_than)
    }

    fn parse_expression(&mut self, precedence: Precedence) -> Result<Expression> {
        let mut left = self.prefix_parse()?;

        while self.peek_token_is_not(&TokenKind::Semicolon)
            && self.precedence_less_than_peek(&precedence)?
        {
            match self.infix_parse(&left) {
                Some(infix) => left = infix?,
                None => {
                    return Ok(left);
                }
            }
        }

        Ok(left)
    }

    fn prefix_parse(&mut self) -> Result<Expression> {
        match self.current_token_kind()? {
            TokenKind::Identifier(_) => Ok(Expression::Identifier(self.parse_identifier()?)),
            TokenKind::Integer(i) => Ok(Expression::Integer(*i)),
            TokenKind::Float(f) => Ok(Expression::Float(*f)),
            TokenKind::String(s) => Ok(Expression::String(s.to_string())),
            b @ TokenKind::True | b @ TokenKind::False => {
                Ok(Expression::Boolean(*b == TokenKind::True))
            }
            TokenKind::Bang | TokenKind::Minus | TokenKind::Ampersand | TokenKind::Asterisk => {
                self.parse_prefix_expression()
            }
            TokenKind::LeftParen => self.parse_grouped_expression(),
            TokenKind::LeftBracket => {
                let elements = self.parse_expression_list(&TokenKind::RightBracket)?;
                Ok(Expression::Array(ArrayLiteral { elements }))
            }
            TokenKind::LeftBrace => self.parse_hash_literal(),
            TokenKind::If => self.parse_if_expression(),
            TokenKind::Function => self.parse_function_literal(),
            TokenKind::Set => self.parse_set_literal(),
            _ => bail!(
                "want: {}, got: {:?}",
                "matching prefix parse function",
                self.current_token.as_ref()
            ),
        }
    }

    fn parse_set_literal(&mut self) -> Result<Expression> {
        let mut set = vec![];
        self.expect_peek_advance(&TokenKind::LeftBrace)?;

        while self.peek_token_is_not(&TokenKind::RightBrace) {
            self.next_token()?;

            set.push(self.parse_expression(Precedence::Lowest)?);

            if self.peek_token_is_not(&TokenKind::RightBrace) {
                self.expect_peek_advance(&TokenKind::Comma)?;
            }
        }

        self.expect_peek_advance(&TokenKind::RightBrace)?;
        Ok(Expression::Set(SetLiteral { set }))
    }

    fn parse_function_literal(&mut self) -> Result<Expression> {
        self.expect_peek_advance(&TokenKind::LeftParen)?;

        let parameters = self.parse_function_parameters()?;

        self.expect_peek_advance(&TokenKind::LeftBrace)?;

        let body = if let Statement::Block(block) = self.parse_block_statement()? {
            block
        } else {
            bail!(
                "expected function body block statement got {:?}",
                &self.current_token_kind()?
            );
        };
        Ok(Expression::Function(FunctionLiteral { parameters, body }))
    }

    fn parse_function_parameters(&mut self) -> Result<Vec<Identifier>> {
        let mut params = vec![];

        if self.peek_token_is(&TokenKind::RightParen) {
            self.next_token()?;
            return Ok(params);
        }

        self.next_token()?;
        params.push(self.parse_identifier()?);

        while self.peek_token_is(&TokenKind::Comma) {
            self.next_token()?;
            self.next_token()?;

            params.push(self.parse_identifier()?);
        }

        self.expect_peek_advance(&TokenKind::RightParen)?;

        Ok(params)
    }

    fn parse_if_expression(&mut self) -> Result<Expression> {
        self.expect_peek_advance(&TokenKind::LeftParen)?;
        self.next_token()?;

        let condition = Box::new(self.parse_expression(Precedence::Lowest)?);

        self.expect_peek_advance(&TokenKind::RightParen)?;
        self.expect_peek_advance(&TokenKind::LeftBrace)?;

        let consequence = if let Statement::Block(block) = self.parse_block_statement()? {
            block
        } else {
            bail!(
                "expected if block statement got {:?}",
                &self.current_token_kind()?
            );
        };

        if self.peek_token_is_not(&TokenKind::Else) {
            return Ok(Expression::If(IfExpression {
                condition,
                consequence,
                alternative: None,
            }));
        }

        self.next_token()?;
        self.expect_peek_advance(&TokenKind::LeftBrace)?;

        let alternative = if let Statement::Block(block) = self.parse_block_statement()? {
            Some(block)
        } else {
            bail!(
                "expected else block statement got {:?}",
                &self.current_token_kind()?
            );
        };

        Ok(Expression::If(IfExpression {
            condition,
            consequence,
            alternative,
        }))
    }

    fn parse_prefix_expression(&mut self) -> anyhow::Result<Expression> {
        let operator_kind = self.current_token_kind()?.clone();
        self.next_token()?;

        let right = Box::new(self.parse_expression(Precedence::Prefix)?);

        Ok(Expression::Prefix(PrefixExpression {
            operator: operator_kind.clone(),
            right,
        }))
    }

    fn parse_grouped_expression(&mut self) -> Result<Expression> {
        self.next_token()?;

        let expr = self.parse_expression(Precedence::Lowest)?;

        self.expect_peek_advance(&TokenKind::RightParen)?;

        Ok(expr)
    }

    fn parse_hash_literal(&mut self) -> Result<Expression> {
        let mut pairs = vec![];
        while self.peek_token_is_not(&TokenKind::RightBrace) {
            self.next_token()?;

            let key = self.parse_expression(Precedence::Lowest)?;
            self.expect_peek_advance(&TokenKind::Colon)?;
            self.next_token()?;

            let value = self.parse_expression(Precedence::Lowest)?;

            pairs.push((key, value));

            if self.peek_token_is_not(&TokenKind::RightBrace) {
                self.expect_peek_advance(&TokenKind::Comma)?;
            }
        }

        self.expect_peek_advance(&TokenKind::RightBrace)?;

        Ok(Expression::Hash(HashLiteral { pairs }))
    }

    fn parse_infix_expression(&mut self, left: &Expression) -> Result<Expression> {
        self.next_token()?;

        let operator_kind = self.current_token_kind()?.clone();
        let prec = precedence_from_token(&self.current_token.as_ref().unwrap());
        self.next_token()?;

        let right = Box::new(self.parse_expression(prec)?);

        Ok(Expression::Infix(InfixExpression {
            left: Box::new(left.clone()),
            operator: operator_kind,
            right,
        }))
    }

    fn parse_identifier(&self) -> Result<Identifier> {
        match self.current_token_kind()? {
            TokenKind::Identifier(name) => Ok(Identifier {
                value: name.clone(),
            }),
            _ => bail!("expected Identifier token"),
        }
    }

    fn next_token(&mut self) -> Result<()> {
        self.current_token = self.peekable_tokens.next();
        Ok(())
    }

    fn peek_token(&mut self) -> Option<&Token> {
        self.peekable_tokens.peek()
    }

    fn current_token_is(&self, kind: &TokenKind) -> bool {
        self.current_token
            .as_ref()
            .map_or(false, |t| t.kind == *kind)
    }

    fn peek_token_is(&mut self, kind: &TokenKind) -> bool {
        self.peekable_tokens
            .peek()
            .map_or(false, |t| t.kind == *kind)
    }

    fn peek_token_is_not(&mut self, kind: &TokenKind) -> bool {
        !self.peek_token_is(kind)
    }

    fn expect_peek_advance(&mut self, kind: &TokenKind) -> Result<()> {
        if self.peek_token_is(kind) {
            self.next_token()?;
            Ok(())
        } else {
            bail!("expected token {:?}, got {:?}", kind, self.peek_token());
        }
    }

    fn current_token_is_not(&self, kind: &TokenKind) -> bool {
        self.current_token
            .as_ref()
            .map_or(true, |t| t.kind != *kind)
    }

    fn current_token_kind(&self) -> Result<&TokenKind> {
        self.current_token
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("expected token"))
            .map(|t| &t.kind)
    }

    fn expect_current_token(&self) -> Result<&Token> {
        self.current_token
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("expected token"))
    }

    fn expect_peek_token(&mut self) -> Result<&Token> {
        self.peek_token()
            .ok_or_else(|| anyhow::anyhow!("expected token"))
    }
}

#[cfg(test)]
mod tests {
    use lexer::token::{Integer, Radix};

    use crate::ast::Statement;

    use super::*;

    #[test]
    fn test_with_empty_input() {
        let input = "";
        let program = parse(input);
        assert_eq!(program.statements.len(), 0);
    }

    #[test]
    fn test_with_invalid_input() {
        let input = "let x 5;";
        let lexer = Lexer::new(input);
        let mut program = Parser::new(lexer);
        let result = program.parse();

        assert!(result.is_err());
    }

    #[test]
    fn test_let_statements() {
        let input = r#"
            let x = 5;
            let y = 10;
            let foobar = 838383;
        "#;
        let program = parse(input);

        assert_eq!(program.statements.len(), 3);
        let expected_identifiers = vec!["x", "y", "foobar"];
        for (i, expected_identifier) in expected_identifiers.iter().enumerate() {
            let stmt = &program.statements[i];
            assert!(format!("{}", stmt).contains("let"));
            let let_stmt = if let Statement::Let(let_stmt) = stmt {
                let_stmt
            } else {
                assert!(false, "expected Let statement");
                continue; // This continue is technically unreachable, but included for clarity
            };
            assert_eq!(let_stmt.name.value, *expected_identifier);
            assert_eq!(format!("{}", let_stmt.name), *expected_identifier);
        }
    }

    #[test]
    fn test_return_statements() {
        let input = vec!["return 5;", "return 10;", "return 993322;"];
        let input_str = input.join("\n");
        let program = parse(input_str.as_str());

        assert_eq!(program.statements.len(), 3);
        for (stmt, expected) in program.statements.iter().zip(input.iter()) {
            assert_eq!(format!("{}", stmt), expected.to_string());
        }
    }

    #[test]
    fn test_identifier_expression() {
        let input = "foobar;";
        let program = parse(input);

        assert_eq!(program.statements.len(), 1);
        let stmt = &program.statements[0];
        let expression = if let Statement::Expression(expression) = stmt {
            expression
        } else {
            assert!(false, "expected Expression statement");
            return; // This return is technically unreachable, but included for clarity
        };
        assert_eq!(format!("{}", expression), "foobar");
    }

    #[test]
    fn test_integer_literal_expression() {
        let input = "25;";
        let program = parse(input);

        assert_eq!(program.statements.len(), 1);
        let stmt = &program.statements[0];
        let expression = if let Statement::Expression(expression) = stmt {
            expression
        } else {
            assert!(false, "expected Expression statement");
            return; // This return is technically unreachable, but included for clarity
        };
        assert_eq!(format!("{}", expression), "25");
    }

    #[test]
    fn test_prefix_expression() {
        let input = vec!["!5;", "-15;", "*foobar;"];
        let expected = vec!["(!5)", "(-15)", "(*foobar)"];
        let input_str = input.join("\n");
        let program = parse(input_str.as_str());

        assert_eq!(program.statements.len(), input.len());
        for (stmt, expected) in program.statements.iter().zip(expected.iter()) {
            assert_eq!(format!("{}", stmt), expected.to_string());
        }
    }

    #[test]
    fn test_parse_string_expression() {
        let input = r#""hello world";"#;
        let program = parse(input);

        assert_eq!(program.statements.len(), 1);
        let stmt = &program.statements[0];
        let expression = if let Statement::Expression(expression) = stmt {
            expression
        } else {
            assert!(false, "expected Expression statement");
            return; // This return is technically unreachable, but included for clarity
        };
        assert_eq!(format!("{}", expression), "\"hello world\"");
    }

    #[test]
    fn parse_float_literal_expression() {
        let program = parse("3.4;");

        assert_eq!(program.statements.len(), 1);

        let expected = 3.4;

        if let Statement::Expression(Expression::Float(f)) = program.statements[0] {
            let float: f64 = f.into();
            assert!((expected - float).abs() < std::f64::EPSILON);
        } else {
            assert!(false, "expected Float expression");
        }
    }

    fn parse(input: &str) -> Program {
        let lexer = Lexer::new(input);

        let mut parser = Parser::new(lexer);

        parser.parse().expect("failed to parse program")
    }

    #[test]
    fn test_parse_array_literal() {
        let tests = vec![
            ("[1, 2 * 2, !true]", vec!["1", "(2 * 2)", "(!true)"]),
            ("[]", vec![]),
        ];

        for (input, want) in tests {
            let prog = parse(input);

            assert_eq!(prog.statements.len(), 1);

            let got = if let Statement::Expression(Expression::Array(a)) = &prog.statements[0] {
                a
            } else {
                assert!(false, "not an array literal expression");
                return;
            };

            assert_eq!(got.elements.len(), want.len());
            for e in want.iter().zip(got.elements.iter()) {
                assert_eq!(*e.0, format!("{}", e.1));
            }
        }
    }

    #[test]
    fn parse_prefix_integer_expressions() {
        let tests = vec![("!5;", TokenKind::Bang, 5), ("-15;", TokenKind::Minus, 15)];

        for test in tests {
            let (input, want_op, want_int) = test;
            let prog = parse(input);

            let got = if let Statement::Expression(Expression::Prefix(pre)) = &prog.statements[0] {
                pre
            } else {
                panic!("not a prefix expression");
            };

            let got_int = if let Expression::Integer(int) = &*got.right {
                int
            } else {
                panic!("not an integer expression");
            };

            assert_eq!(want_op, got.operator);
            assert_eq!(want_int, got_int.value)
        }
    }

    #[test]
    fn parse_prefix_boolean_expressions() {
        let tests = vec![
            ("!true;", TokenKind::Bang, true),
            ("!false;", TokenKind::Bang, false),
        ];

        for test in tests {
            let (input, want_op, want_bool) = test;
            let prog = parse(input);

            let got = if let Statement::Expression(Expression::Prefix(pre)) = &prog.statements[0] {
                pre
            } else {
                panic!("not a prefix expression");
            };

            let got_bool = if let Expression::Boolean(b) = &*got.right {
                b
            } else {
                panic!("not a boolean expression");
            };

            assert_eq!(want_op, got.operator);
            assert_eq!(want_bool, *got_bool);
        }
    }

    #[test]
    fn parse_infix_integer_expressions() {
        let int = Expression::Integer(Integer {
            radix: Radix::Decimal,
            value: 5,
        });

        let tests = vec![
            ("5 + 5;", TokenKind::Plus),
            ("5 - 5;", TokenKind::Minus),
            ("5 * 5;", TokenKind::Asterisk),
            ("5 / 5;", TokenKind::Slash),
            ("5 % 5;", TokenKind::Percent),
            ("5 > 5;", TokenKind::GT),
            ("5 < 5;", TokenKind::LT),
            ("5 == 5;", TokenKind::Equal),
            ("5 != 5;", TokenKind::NotEqual),
        ];

        for (input, want_op) in tests {
            let prog = parse(input);

            let got = if let Statement::Expression(Expression::Infix(inf)) = &prog.statements[0] {
                inf
            } else {
                panic!("not an infix expression");
            };

            assert_eq!(int, *got.left);
            assert_eq!(want_op, got.operator);
            assert_eq!(int, *got.right);
        }
    }

    #[test]
    fn parse_infix_boolean_expressions() {
        let etrue = Expression::Boolean(true);
        let efalse = Expression::Boolean(false);

        let tests = vec![
            ("true == true", &etrue, TokenKind::Equal, &etrue),
            ("true != false", &etrue, TokenKind::NotEqual, &efalse),
            ("false == false", &efalse, TokenKind::Equal, &efalse),
        ];

        for (input, want_left, want_op, want_right) in tests {
            let prog = parse(input);

            let got = if let Statement::Expression(Expression::Infix(inf)) = &prog.statements[0] {
                inf
            } else {
                panic!("not an infix expression");
            };

            assert_eq!(*want_left, *got.left);
            assert_eq!(want_op, got.operator);
            assert_eq!(*want_right, *got.right);
        }
    }

    #[test]
    fn parse_if_expressions() {
        let tests = vec!["if (x < y) { x }", "if (x > y) { x } else { y }"];

        for test in tests {
            let got = format!("{}", parse(test));

            assert_eq!(test, got);
        }
    }

    #[test]
    fn parse_function_literals() {
        let tests = vec![
            ("fn() {};", "fn() {  }"),
            ("fn(x) { };", "fn(x) {  }"),
            ("fn(x, y) { x + y; };", "fn(x, y) { (x + y) }"),
        ];

        for (input, want) in tests {
            let got = format!("{}", parse(input));

            assert_eq!(want, got);
        }
    }

    #[test]
    fn parse_call_expressions() {
        let tests = vec![
            ("add(1, 2 * 3, 4 + 5);", "add(1, (2 * 3), (4 + 5))"),
            ("a + add(b * c) + d", "((a + add((b * c))) + d)"),
            (
                "add(a, b, 1, 2 * 3, 4 + 5, add(6, 7 * 8))",
                "add(a, b, 1, (2 * 3), (4 + 5), add(6, (7 * 8)))",
            ),
        ];

        for (input, want) in tests {
            let got = format!("{}", parse(input));

            assert_eq!(want, got);
        }
    }

    #[test]
    fn parse_hash_expressions() {
        let tests = vec![
            (
                r#"{"one": 1, "two": 2, "three": 3}"#,
                r#"{"one": 1, "two": 2, "three": 3}"#,
            ),
            (
                r#"{"one": 0 + 1, "two": 10 - 8, "three": 15 / 5}"#,
                r#"{"one": (0 + 1), "two": (10 - 8), "three": (15 / 5)}"#,
            ),
            ("{}", "{}"),
            // Duplicate keys permitted by the parser.
            ("{1: 1, 1: 1}", "{1: 1, 1: 1}"),
        ];

        for (input, want) in tests {
            let got = format!("{}", parse(input));

            assert_eq!(want, got);
        }
    }

    #[test]
    fn parse_set_expressions() {
        let tests = vec![
            (r#"set{1, "foo", true}"#, r#"set{1, "foo", true}"#),
            ("set{1}", "set{1}"),
            // Duplicate elements permitted by the parser.
            ("set{1, 1, 1, 2}", "set{1, 1, 1, 2}"),
        ];

        for (input, want) in tests {
            let got = format!("{}", parse(input));

            assert_eq!(want, got);
        }
    }

    #[test]
    fn parse_pointer_expressions() {
        let tests = vec![("&1", "(&1)"), ("&&1", "(&(&1))"), ("*&1", "(*(&1))")];

        for (input, want) in tests {
            let got = format!("{}", parse(input));

            assert_eq!(want, got);
        }
    }

    #[test]
    fn parse_operator_precedence() {
        let tests = vec![
            ("-a * b", "((-a) * b)"),
            ("!-a", "(!(-a))"),
            ("a + b + c", "((a + b) + c)"),
            ("a + b - c", "((a + b) - c)"),
            ("a * b * c", "((a * b) * c)"),
            ("a * b / c", "((a * b) / c)"),
            ("a + b / c", "(a + (b / c))"),
            ("a + b * c + d / e - f", "(((a + (b * c)) + (d / e)) - f)"),
            ("3 + 4; -5 * 5", "(3 + 4)((-5) * 5)"),
            ("5 > 4 == 3 < 4", "((5 > 4) == (3 < 4))"),
            ("5 < 4 != 3 > 4", "((5 < 4) != (3 > 4))"),
            (
                "3 + 4 * 5 == 3 * 1 + 4 * 5",
                "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
            ),
            ("1 + 2 % 3", "(1 + (2 % 3))"),
            ("true", "true"),
            ("false", "false"),
            ("3 > 5 == false", "((3 > 5) == false)"),
            ("3 < 5 == true", "((3 < 5) == true)"),
            ("1 + (2 + 3) + 4", "((1 + (2 + 3)) + 4)"),
            ("(5 + 5) * 2", "((5 + 5) * 2)"),
            ("2 / (5 + 5)", "(2 / (5 + 5))"),
            ("-(5 + 5)", "(-(5 + 5))"),
            ("!(true == true)", "(!(true == true))"),
            (
                "a * [1, 2, 3, 4][b * c] * d",
                "((a * ([1, 2, 3, 4][(b * c)])) * d)",
            ),
            (
                "add(a * b[2], b[1], 2 * [1, 2][1])",
                "add((a * (b[2])), (b[1]), (2 * ([1, 2][1])))",
            ),
        ];

        for (input, want) in tests {
            let got = format!("{}", parse(input));

            assert_eq!(want, got);
        }
    }
}
