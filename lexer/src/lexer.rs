use anyhow::bail;
use std::{iter::Peekable, str::Chars};

use crate::token::{Float, Integer, Radix, Token, TokenKind};

#[derive(Debug)]
pub struct Lexer<'a> {
    chars: Peekable<Chars<'a>>,
    current_token: Option<Token>,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        let chars = input.chars().peekable();
        Self {
            chars,
            current_token: None,
        }
    }

    fn consume_while<F>(&mut self, mut condition: F) -> String
    where
        F: FnMut(char) -> bool,
    {
        let mut result = String::new();
        while let Some(&c) = self.chars.peek() {
            if condition(c) {
                result.push(c);
                self.chars.next();
            } else {
                break;
            }
        }
        result
    }

    fn skip_whitespace(&mut self) {
        self.consume_while(|c| c.is_whitespace());
    }

    fn read_identifier(&mut self, initial_char: char) -> Token {
        let mut literal = initial_char.to_string();
        literal.push_str(&self.consume_while(|c| c.is_alphanumeric() || c == '_'));

        match literal.as_str() {
            "let" => Token::new(TokenKind::Let),
            "fn" => Token::new(TokenKind::Function),
            "true" => Token::new(TokenKind::True),
            "false" => Token::new(TokenKind::False),
            "if" => Token::new(TokenKind::If),
            "else" => Token::new(TokenKind::Else),
            "return" => Token::new(TokenKind::Return),
            "set" => Token::new(TokenKind::Set),
            _ => Token::new(TokenKind::Identifier(literal)),
        }
    }

    fn read_string(&mut self) -> anyhow::Result<Token> {
        let literal = self.consume_while(|c| c != '"');
        if self.chars.next().is_none() {
            bail!("unterminated string");
        }
        Ok(Token::new(TokenKind::String(literal)))
    }

    fn read_number(&mut self, initial_char: char) -> Token {
        let mut literal = initial_char.to_string();
        literal.push_str(&self.consume_while(|c| c.is_numeric() || c == '.'));
        if literal.contains('.') {
            Token::new(TokenKind::Float(
                literal.parse().unwrap_or_else(|_| Float::from(0.0))))
        } else {
            Token::new(TokenKind::Integer(Integer {
                value: literal.parse().unwrap(),
                radix: Radix::Decimal,
            }))
        }
    }

    pub fn next_token(&mut self) -> Option<Token> {
        self.skip_whitespace();
        let next_char = self.chars.next()?;
        let token = match next_char {
            '=' => {
                if let Some(&'=') = self.chars.peek() {
                    self.chars.next();
                    Token::new(TokenKind::EQ)
                } else {
                    Token::new(TokenKind::Assign)
                }
            }
            ';' => Token::new(TokenKind::Semicolon),
            '(' => Token::new(TokenKind::LParen),
            ')' => Token::new(TokenKind::RParen),
            ',' => Token::new(TokenKind::Comma),
            '+' => Token::new(TokenKind::Plus),
            '{' => Token::new(TokenKind::LBrace),
            '}' => Token::new(TokenKind::RBrace),
            '[' => Token::new(TokenKind::LBracket),
            ']' => Token::new(TokenKind::RBracket),
            '!' => {
                if let Some(&'=') = self.chars.peek() {
                    self.chars.next();
                    Token::new(TokenKind::NotEq)
                } else {
                    Token::new(TokenKind::Bang)
                }
            }
            '-' => Token::new(TokenKind::Minus),
            '*' => Token::new(TokenKind::Asterisk),
            '/' => Token::new(TokenKind::Slash),
            '<' => Token::new(TokenKind::LT),
            '>' => Token::new(TokenKind::GT),
            '%' => Token::new(TokenKind::Percent),
            '&' => Token::new(TokenKind::Ampersand),
            ':' => Token::new(TokenKind::Colon),
            '"' => self.read_string().ok()?,
            _ if next_char.is_alphabetic() => self.read_identifier(next_char),
            _ if next_char.is_numeric() => self.read_number(next_char),
            _ => Token::new(TokenKind::Illegal),
        };
        Some(token)
    }
}

impl Iterator for Lexer<'_> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(current) = &self.current_token {
            if current.kind == TokenKind::EOF {
                return None;
            }
        }

        let mut token = self.next_token();
        if token.is_none() {
            self.current_token = Some(Token::new(TokenKind::EOF));
            token = self.current_token.clone();
        }
        token
    }
}

#[cfg(test)]
mod tests {
    use crate::token::{Float, Integer, Radix};

    use super::*;

    #[test]
    fn test_next_token() {
        let input = "=+(){},;![]";
        let expected_tokens = vec![
            TokenKind::Assign,
            TokenKind::Plus,
            TokenKind::LParen,
            TokenKind::RParen,
            TokenKind::LBrace,
            TokenKind::RBrace,
            TokenKind::Comma,
            TokenKind::Semicolon,
            TokenKind::Bang,
            TokenKind::LBracket,
            TokenKind::RBracket,
            TokenKind::EOF,
        ];
        let mut lexer = Lexer::new(input);
        for kind in expected_tokens {
            let token = lexer.next().unwrap();
            assert_eq!(token.kind, kind);
        }
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn test_skip_white_space() {
        let input = "  \t\n  =  \t\n  +  \t\n  5  \t\n  ;  \t\n  ";
        let expected_tokens = vec![
            TokenKind::Assign,
            TokenKind::Plus,
            TokenKind::Integer(Integer {
                value: 5,
                radix: Radix::Decimal,
            }),
            TokenKind::Semicolon,
            TokenKind::EOF,
        ];
        let mut lexer = Lexer::new(input);
        for kind in expected_tokens {
            let token = lexer.next().unwrap();
            assert_eq!(token.kind, kind);
        }
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn test_next_token_with_identifiers() {
        let input = "let five = 5; let ten = 10; let add = fn(x, y) { x + y; };";
        let expected_tokens = vec![
            TokenKind::Let,
            TokenKind::Identifier("five".to_string()),
            TokenKind::Assign,
            TokenKind::Integer(Integer {
                value: 5,
                radix: Radix::Decimal,
            }),
            TokenKind::Semicolon,
            TokenKind::Let,
            TokenKind::Identifier("ten".to_string()),
            TokenKind::Assign,
            TokenKind::Integer(Integer {
                value: 10,
                radix: Radix::Decimal,
            }),
            TokenKind::Semicolon,
            TokenKind::Let,
            TokenKind::Identifier("add".to_string()),
            TokenKind::Assign,
            TokenKind::Function,
            TokenKind::LParen,
            TokenKind::Identifier("x".to_string()),
            TokenKind::Comma,
            TokenKind::Identifier("y".to_string()),
            TokenKind::RParen,
            TokenKind::LBrace,
            TokenKind::Identifier("x".to_string()),
            TokenKind::Plus,
            TokenKind::Identifier("y".to_string()),
            TokenKind::Semicolon,
            TokenKind::RBrace,
            TokenKind::Semicolon,
            TokenKind::EOF,
        ];
        let mut lexer = Lexer::new(input);
        for kind in expected_tokens {
            let token = lexer.next().unwrap();
            assert_eq!(token.kind, kind);
        }
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn test_next_token_with_multi_char_operators() {
        let input = "if (5 != 10) { return true; } else if (3 == 3) { return false; }";
        let expected_tokens = vec![
            TokenKind::If,
            TokenKind::LParen,
            TokenKind::Integer(Integer {
                value: 5,
                radix: Radix::Decimal,
            }),
            TokenKind::NotEq,
            TokenKind::Integer(Integer {
                value: 10,
                radix: Radix::Decimal,
            }),
            TokenKind::RParen,
            TokenKind::LBrace,
            TokenKind::Return,
            TokenKind::True,
            TokenKind::Semicolon,
            TokenKind::RBrace,
            TokenKind::Else,
            TokenKind::If,
            TokenKind::LParen,
            TokenKind::Integer(Integer {
                value: 3,
                radix: Radix::Decimal,
            }),
            TokenKind::EQ,
            TokenKind::Integer(Integer {
                value: 3,
                radix: Radix::Decimal,
            }),
            TokenKind::RParen,
            TokenKind::LBrace,
            TokenKind::Return,
            TokenKind::False,
            TokenKind::Semicolon,
            TokenKind::RBrace,
            TokenKind::EOF,
        ];
        let mut lexer = Lexer::new(input);
        for kind in expected_tokens {
            let token = lexer.next().unwrap();
            assert_eq!(token.kind, kind);
        }
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn test_next_token_with_all_operators() {
        let input = "=+(){},;![]-*/<>==!=";
        let expected_tokens = vec![
            TokenKind::Assign,
            TokenKind::Plus,
            TokenKind::LParen,
            TokenKind::RParen,
            TokenKind::LBrace,
            TokenKind::RBrace,
            TokenKind::Comma,
            TokenKind::Semicolon,
            TokenKind::Bang,
            TokenKind::LBracket,
            TokenKind::RBracket,
            TokenKind::Minus,
            TokenKind::Asterisk,
            TokenKind::Slash,
            TokenKind::LT,
            TokenKind::GT,
            TokenKind::EQ,
            TokenKind::NotEq,
            TokenKind::EOF,
        ];
        let mut lexer = Lexer::new(input);
        for kind in expected_tokens {
            let token = lexer.next().unwrap();
            assert_eq!(token.kind, kind);
        }
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn lex_tokens() {
        let result = Lexer::new(
            r#"
let five = 5;
let ten = 10;

let add = fn(x, y) {
    x + y;
};

let result = add(five, ten);

!-/*5;
5 < 10 > 5;

if (5 < 10) {
    return true;
} else {
    return false;
}

10 == 10;
10 != 9;
1.01 2.
4 % 2
"foobar"
"foo bar"
[1, 2];
{"foo": "bar"}
&five
"#,
        );

        let expected = vec![
            //
            TokenKind::Let,
            TokenKind::Identifier("five".to_string()),
            TokenKind::Assign,
            TokenKind::Integer(Integer {
                radix: Radix::Decimal,
                value: 5,
            }),
            TokenKind::Semicolon,
            //
            TokenKind::Let,
            TokenKind::Identifier("ten".to_string()),
            TokenKind::Assign,
            TokenKind::Integer(Integer {
                radix: Radix::Decimal,
                value: 10,
            }),
            TokenKind::Semicolon,
            //
            TokenKind::Let,
            TokenKind::Identifier("add".to_string()),
            TokenKind::Assign,
            TokenKind::Function,
            TokenKind::LParen,
            TokenKind::Identifier("x".to_string()),
            TokenKind::Comma,
            TokenKind::Identifier("y".to_string()),
            TokenKind::RParen,
            TokenKind::LBrace,
            TokenKind::Identifier("x".to_string()),
            TokenKind::Plus,
            TokenKind::Identifier("y".to_string()),
            TokenKind::Semicolon,
            TokenKind::RBrace,
            TokenKind::Semicolon,
            //
            TokenKind::Let,
            TokenKind::Identifier("result".to_string()),
            TokenKind::Assign,
            TokenKind::Identifier("add".to_string()),
            TokenKind::LParen,
            TokenKind::Identifier("five".to_string()),
            TokenKind::Comma,
            TokenKind::Identifier("ten".to_string()),
            TokenKind::RParen,
            TokenKind::Semicolon,
            //
            TokenKind::Bang,
            TokenKind::Minus,
            TokenKind::Slash,
            TokenKind::Asterisk,
            TokenKind::Integer(Integer {
                radix: Radix::Decimal,
                value: 5,
            }),
            TokenKind::Semicolon,
            //
            TokenKind::Integer(Integer {
                radix: Radix::Decimal,
                value: 5,
            }),
            TokenKind::LT,
            TokenKind::Integer(Integer {
                radix: Radix::Decimal,
                value: 10,
            }),
            TokenKind::GT,
            TokenKind::Integer(Integer {
                radix: Radix::Decimal,
                value: 5,
            }),
            TokenKind::Semicolon,
            //
            TokenKind::If,
            TokenKind::LParen,
            TokenKind::Integer(Integer {
                radix: Radix::Decimal,
                value: 5,
            }),
            TokenKind::LT,
            TokenKind::Integer(Integer {
                radix: Radix::Decimal,
                value: 10,
            }),
            TokenKind::RParen,
            TokenKind::LBrace,
            TokenKind::Return,
            TokenKind::True,
            TokenKind::Semicolon,
            TokenKind::RBrace,
            TokenKind::Else,
            TokenKind::LBrace,
            TokenKind::Return,
            TokenKind::False,
            TokenKind::Semicolon,
            TokenKind::RBrace,
            //
            TokenKind::Integer(Integer {
                radix: Radix::Decimal,
                value: 10,
            }),
            TokenKind::EQ,
            TokenKind::Integer(Integer {
                radix: Radix::Decimal,
                value: 10,
            }),
            TokenKind::Semicolon,
            //
            TokenKind::Integer(Integer {
                radix: Radix::Decimal,
                value: 10,
            }),
            TokenKind::NotEq,
            TokenKind::Integer(Integer {
                radix: Radix::Decimal,
                value: 9,
            }),
            TokenKind::Semicolon,
            //
            TokenKind::Float(Float::from(1.01)),
            TokenKind::Float(Float::from(2.)),
            //
            TokenKind::Integer(Integer {
                radix: Radix::Decimal,
                value: 4,
            }),
            TokenKind::Percent,
            TokenKind::Integer(Integer {
                radix: Radix::Decimal,
                value: 2,
            }),
            //
            TokenKind::String("foobar".to_string()),
            TokenKind::String("foo bar".to_string()),
            //
            TokenKind::LBracket,
            TokenKind::Integer(Integer {
                radix: Radix::Decimal,
                value: 1,
            }),
            TokenKind::Comma,
            TokenKind::Integer(Integer {
                radix: Radix::Decimal,
                value: 2,
            }),
            TokenKind::RBracket,
            TokenKind::Semicolon,
            //
            TokenKind::LBrace,
            TokenKind::String("foo".to_string()),
            TokenKind::Colon,
            TokenKind::String("bar".to_string()),
            TokenKind::RBrace,
            //
            TokenKind::Ampersand,
            TokenKind::Identifier("five".to_string()),
            //
            TokenKind::EOF,
        ];
        for (got, expected) in result.zip(expected) {
            assert_eq!(got.kind, expected);
        }
    }
}
