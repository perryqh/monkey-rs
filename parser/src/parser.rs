use anyhow::{bail, Result};
use lexer::{
    lexer::Lexer,
    token::{Token, TokenKind},
};

use crate::ast::{
    Expression, Identifier, IntegerLiteral, LetStatement, NodeTrait, Program, ReturnStatement,
    Statement,
};

#[derive(Debug)]
struct Parser {
    peekable_tokens: std::iter::Peekable<std::vec::IntoIter<Token>>,
    current_token: Option<Token>,
}

impl Parser {
    fn new(lexer: Lexer) -> Self {
        let peekable_tokens = lexer.collect::<Vec<Token>>().into_iter().peekable();
        Self {
            peekable_tokens,
            current_token: None,
        }
    }

    pub fn parse(&mut self) -> Result<Program> {
        let mut prog = Program::new();
        self.next_token()?;

        while !self.current_token_is_eof() {
            let stmt = self.parse_statement()?;
            prog.statements.push(stmt);
            self.next_token()?;
        }

        Ok(prog)
    }

    fn parse_statement(&mut self) -> Result<Statement> {
        match self.current_token.as_ref().map(|t| &t.kind) {
            Some(TokenKind::Let) => self.parse_let_statement(),
            Some(TokenKind::Return) => self.parse_return_statement(),
            _ => bail!("unrecognized token"),
        }
    }

    fn parse_return_statement(&mut self) -> Result<Statement> {
        self.expect_current_token()?;
        self.next_token()?;
        let value = self.parse_expression()?;
        self.expect_peek(&TokenKind::Semicolon)?;
        Ok(Statement::Return(ReturnStatement {
            return_value: value,
        }))
    }

    fn parse_let_statement(&mut self) -> Result<Statement> {
        self.expect_current_token()?;
        self.expect_identifier_peek()?;
        let name = self.parse_identifier()?;
        self.expect_peek(&TokenKind::Assign)?;
        self.next_token()?;
        let value = self.parse_expression()?;
        self.expect_peek(&TokenKind::Semicolon)?;
        Ok(Statement::Let(LetStatement { name, value }))
    }

    fn parse_expression(&self) -> Result<Expression> {
        Ok(Expression::IntegerLiteral(IntegerLiteral { value: 5 }))
    }

    fn parse_identifier(&self) -> Result<Identifier> {
        let token = self.expect_current_token()?;
        match &token.kind {
            TokenKind::Identifier { name } => Ok(Identifier {
                value: name.clone(),
            }),
            _ => bail!("expected Identifier token"),
        }
    }

    fn current_token_is_eof(&self) -> bool {
        self.current_token_is_not(&TokenKind::EOF)
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

    fn expect_identifier_peek(&mut self) -> Result<()> {
        let token = self
            .peek_token()
            .ok_or_else(|| anyhow::anyhow!("expected token"))?;
        match &token.kind {
            TokenKind::Identifier { name: _ } => {
                self.next_token()?;
                Ok(())
            }
            _ => bail!("expected Identifier token"),
        }
    }

    fn expect_peek(&mut self, kind: &TokenKind) -> Result<()> {
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
            .map_or(false, |t| t.kind == *kind)
    }

    fn expect_current_token(&self) -> Result<&Token> {
        self.current_token
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("expected token"))
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::Statement;

    use super::*;

    #[test]
    fn test_with_empty_input() {
        let input = "";
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse().unwrap();
        assert_eq!(program.statements.len(), 0);
    }

    #[test]
    fn test_with_invalid_input() {
        let input = "let x 5;";
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let result = parser.parse();
        assert!(result.is_err());
    }

    #[test]
    fn test_let_statements() {
        let input = r#"
            let x = 5;
            let y = 10;
            let foobar = 838383;
        "#;
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse().unwrap();

        assert_eq!(program.statements.len(), 3);
        let expected_identifiers = vec!["x", "y", "foobar"];
        for (i, expected_identifier) in expected_identifiers.iter().enumerate() {
            let stmt = &program.statements[i];
            assert_eq!(stmt.token_literal(), "let");
            let let_stmt = if let Statement::Let(let_stmt) = stmt {
                let_stmt
            } else {
                assert!(false, "expected Let statement");
                continue; // This continue is technically unreachable, but included for clarity
            };
            assert_eq!(let_stmt.name.value, *expected_identifier);
            assert_eq!(let_stmt.name.token_literal(), *expected_identifier);
        }
    }

    #[test]
    fn test_return_statements() {
        let input = r#"
            return 5;
            return 10;
            return 993322;
        "#;
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse().unwrap();

        assert_eq!(program.statements.len(), 3);
        for stmt in program.statements {
            assert_eq!(stmt.token_literal(), "return");
        }
    }
}
