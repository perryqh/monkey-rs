use std::{iter::Peekable, str::Chars};

use crate::token::{Token, TokenKind};

struct Lexer<'a> {
    input: &'a str,
    chars: Peekable<Chars<'a>>,
    current_token: Option<Token<'a>>,
}

impl<'a> Lexer<'a> {
    fn new(input: &'a str) -> Self {
        let chars = input.chars().peekable();
        Self {
            input,
            chars,
            current_token: None,
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(current) = &self.current_token {
            if current.kind == TokenKind::EOF {
                return None;
            }
        }
        let next_char = self.chars.next();
        if next_char.is_none() {
            self.current_token = Some(Token::new(TokenKind::EOF, ""));
            return self.current_token.clone();
        }
        self.current_token = match next_char.unwrap() {
            '=' => Some(Token::new(TokenKind::Assign, "=")),
            ';' => Some(Token::new(TokenKind::Semicolon, ";")),
            '(' => Some(Token::new(TokenKind::LParen, "(")),
            ')' => Some(Token::new(TokenKind::RParen, ")")),
            ',' => Some(Token::new(TokenKind::Comma, ",")),
            '+' => Some(Token::new(TokenKind::Plus, "+")),
            '{' => Some(Token::new(TokenKind::LBrace, "{")),
            '}' => Some(Token::new(TokenKind::RBrace, "}")),
            '!' => Some(Token::new(TokenKind::Bang, "!")),
            '[' => Some(Token::new(TokenKind::LBracket, "[")),
            ']' => Some(Token::new(TokenKind::RBracket, "]")),
            _ => panic!("unexpected character: {}", next_char.unwrap())
        };
        self.current_token.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_next_token() {
        let input = "=+(){},;![]";
        let expected_tokens = vec![
            (TokenKind::Assign, "="),
            (TokenKind::Plus, "+"),
            (TokenKind::LParen, "("),
            (TokenKind::RParen, ")"),
            (TokenKind::LBrace, "{"),
            (TokenKind::RBrace, "}"),
            (TokenKind::Comma, ","),
            (TokenKind::Semicolon, ";"),
            (TokenKind::Bang, "!"),
            (TokenKind::LBracket, "["),
            (TokenKind::RBracket, "]"),
            (TokenKind::EOF, ""),
        ];
        let mut lexer = Lexer::new(input);
        for (kind, literal) in expected_tokens {
            let token = lexer.next().unwrap();
            assert_eq!(token.kind, kind);
            assert_eq!(token.literal, literal);
        }
        assert_eq!(lexer.next(), None);
    }
}
