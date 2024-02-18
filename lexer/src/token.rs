use std::fmt::{self, Formatter};

use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Eq, Hash, Ord, Serialize, Deserialize, PartialOrd, PartialEq)]
pub struct Token<'a> {
    pub kind: TokenKind,
    pub literal: &'a str,
}

impl<'a> Token<'a> {
    pub fn new(kind: TokenKind, literal: &'a str) -> Self {
        Self { kind, literal }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, Serialize, Deserialize, PartialOrd, PartialEq)]
pub enum TokenKind {
    Illegal,
    EOF,

    // Identifiers + literals
    Identifier { name: String },
    INT(i64),
    STRING(String),

    // Operators
    Assign,
    Plus,
    Minus,
    Bang,
    Asterisk,
    Slash,

    LT,
    GT,

    EQ,
    NotEq,

    // Delimiters
    Comma,
    Semicolon,
    Colon,

    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,

    // Keywords
    Function,
    Let,
    True,
    False,
    If,
    Else,
    Return,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Identifier { name } => write!(f, "{}", name),
            TokenKind::INT(i) => write!(f, "{}", i),
            TokenKind::STRING(s) => write!(f, "{}", s),
            TokenKind::Assign => write!(f, "="),
            TokenKind::Plus => write!(f, "+"),
            TokenKind::Minus => write!(f, "-"),
            TokenKind::Bang => write!(f, "!"),
            TokenKind::Asterisk => write!(f, "*"),
            TokenKind::Slash => write!(f, "/"),
            TokenKind::LT => write!(f, "<"),
            TokenKind::GT => write!(f, ">"),
            TokenKind::EQ => write!(f, "=="),
            TokenKind::NotEq => write!(f, "!="),
            TokenKind::Comma => write!(f, ","),
            TokenKind::Semicolon => write!(f, ";"),
            TokenKind::LParen => write!(f, "("),
            TokenKind::RParen => write!(f, ")"),
            TokenKind::LBrace => write!(f, "{{"),
            TokenKind::RBrace => write!(f, "}}"),
            TokenKind::LBracket => write!(f, "["),
            TokenKind::RBracket => write!(f, "]"),
            TokenKind::Function => write!(f, "fn"),
            TokenKind::Let => write!(f, "let"),
            TokenKind::True => write!(f, "true"),
            TokenKind::False => write!(f, "false"),
            TokenKind::If => write!(f, "if"),
            TokenKind::Else => write!(f, "else"),
            TokenKind::Return => write!(f, "return"),
            TokenKind::Illegal => write!(f, "ILLEGAL"),
            TokenKind::EOF => write!(f, "EOF"),
            TokenKind::Colon => write!(f, ":"),
        }
    }
}
