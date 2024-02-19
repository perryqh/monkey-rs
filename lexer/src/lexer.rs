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

    fn skip_whitespace(&mut self) {
        while let Some(&c) = self.chars.peek() {
            if c.is_whitespace() {
                self.chars.next();
            } else {
                break;
            }
        }
    }

    fn read_identifier(&mut self, initial_char: char) -> Token {
        let mut literal = String::new();
        literal.push(initial_char);
        while let Some(&c) = self.chars.peek() {
            if c.is_alphanumeric() || c == '_' {
                literal.push(c);
                self.chars.next();
            } else {
                break;
            }
        }
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
        let mut literal = String::new();
        literal.push(initial_char);
        while let Some(&c) = self.chars.peek() {
            if c.is_numeric() {
                literal.push(c);
                self.chars.next();
            } else {
                break;
            }
        }
        Token::new(TokenKind::INT(literal.parse().unwrap()))
    }

    fn next_token(&mut self) -> Option<Token> {
        self.skip_whitespace();
        let next_char = self.chars.next()?;
        let token = match next_char {
            '=' => Token::new(TokenKind::Assign),
            ';' => Token::new(TokenKind::Semicolon),
            '(' => Token::new(TokenKind::LParen),
            ')' => Token::new(TokenKind::RParen),
            ',' => Token::new(TokenKind::Comma),
            '+' => Token::new(TokenKind::Plus),
            '{' => Token::new(TokenKind::LBrace),
            '}' => Token::new(TokenKind::RBrace),
            '[' => Token::new(TokenKind::LBracket),
            ']' => Token::new(TokenKind::RBracket),
            '!' => Token::new(TokenKind::Bang),
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
}
