use lexer::lexer::Lexer;

use crate::ast::{Program, NodeTrait};

#[derive(Debug)]
struct Parser<'a> {
    lexer: Lexer<'a>,
}

impl<'a> Parser<'a> {
    fn new(lexer: Lexer<'a>) -> Self {
        Self { lexer }
    }

    fn parse_program(&mut self) -> Program {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::Statement;

    use super::*;

    #[test]
    fn test_let_statements() {
        let input = r#"
            let x = 5;
            let y = 10;
            let foobar = 838383;
        "#;
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();
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
}