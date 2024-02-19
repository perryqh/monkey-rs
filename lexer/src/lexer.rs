use std::{iter::Peekable, str::Chars};

use crate::token::{Token, TokenKind};

struct Lexer<'a> {
    chars: Peekable<Chars<'a>>,
    current_token: Option<Token>,
}

impl<'a> Lexer<'a> {
    fn new(input: &'a str) -> Self {
        let chars = input.chars().peekable();
        Self {
            chars,
            current_token: None,
        }
    }

    fn consume_while<F>(&mut self, mut condition: F) -> String where F: FnMut(char) -> bool {
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
            _ => Token::new(TokenKind::Identifier { name: literal }),
        }
    }

    fn read_number(&mut self, initial_char: char) -> Token {
        let mut literal = initial_char.to_string();
        literal.push_str(&self.consume_while(|c| c.is_numeric()));
        Token::new(TokenKind::INT(literal.parse().unwrap()))
    }

    fn next_token(&mut self) -> Option<Token> {
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
            _ if next_char.is_alphabetic() => self.read_identifier(next_char),
            _ if next_char.is_numeric() => self.read_number(next_char),
            _ => Token::new(TokenKind::Illegal),
        };
        Some(token)
    }
}

impl<'a> Iterator for Lexer<'_> {
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
            TokenKind::INT(5),
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
            TokenKind::Identifier {
                name: "five".to_string(),
            },
            TokenKind::Assign,
            TokenKind::INT(5),
            TokenKind::Semicolon,
            TokenKind::Let,
            TokenKind::Identifier {
                name: "ten".to_string(),
            },
            TokenKind::Assign,
            TokenKind::INT(10),
            TokenKind::Semicolon,
            TokenKind::Let,
            TokenKind::Identifier {
                name: "add".to_string(),
            },
            TokenKind::Assign,
            TokenKind::Function,
            TokenKind::LParen,
            TokenKind::Identifier {
                name: "x".to_string(),
            },
            TokenKind::Comma,
            TokenKind::Identifier {
                name: "y".to_string(),
            },
            TokenKind::RParen,
            TokenKind::LBrace,
            TokenKind::Identifier {
                name: "x".to_string(),
            },
            TokenKind::Plus,
            TokenKind::Identifier {
                name: "y".to_string(),
            },
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
            TokenKind::INT(5),
            TokenKind::NotEq,
            TokenKind::INT(10),
            TokenKind::RParen,
            TokenKind::LBrace,
            TokenKind::Return,
            TokenKind::True,
            TokenKind::Semicolon,
            TokenKind::RBrace,
            TokenKind::Else,
            TokenKind::If,
            TokenKind::LParen,
            TokenKind::INT(3),
            TokenKind::EQ,
            TokenKind::INT(3),
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
}
