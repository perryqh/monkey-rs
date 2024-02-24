use std::{
    fmt::{self, Formatter},
    str::FromStr,
};

#[derive(Clone, Debug, Eq, Hash, Ord, PartialOrd, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
}

impl Token {
    pub fn new(kind: TokenKind) -> Self {
        Self { kind }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialOrd, PartialEq)]
pub enum TokenKind {
    Illegal,
    EOF,

    // Identifiers + literals
    Identifier(String),
    Integer(Integer),
    Float(Float),
    String(String),

    // Operators
    Assign,
    Plus,
    Minus,
    Bang,
    Asterisk,
    Slash,
    Percent,
    Ampersand,

    LT,
    GT,

    Equal,
    NotEqual,

    // Delimiters
    Comma,
    Semicolon,
    Colon,

    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,

    // Keywords
    Function,
    Let,
    True,
    False,
    If,
    Else,
    Return,
    Set,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Identifier(name) => write!(f, "{}", name),
            TokenKind::Integer(i) => write!(f, "{}", i),
            TokenKind::Float(float) => write!(f, "{}", float),
            TokenKind::String(s) => write!(f, "{}", s),
            TokenKind::Assign => write!(f, "="),
            TokenKind::Plus => write!(f, "+"),
            TokenKind::Minus => write!(f, "-"),
            TokenKind::Bang => write!(f, "!"),
            TokenKind::Asterisk => write!(f, "*"),
            TokenKind::Slash => write!(f, "/"),
            TokenKind::LT => write!(f, "<"),
            TokenKind::GT => write!(f, ">"),
            TokenKind::Equal => write!(f, "=="),
            TokenKind::NotEqual => write!(f, "!="),
            TokenKind::Comma => write!(f, ","),
            TokenKind::Semicolon => write!(f, ";"),
            TokenKind::LeftParen => write!(f, "("),
            TokenKind::RightParen => write!(f, ")"),
            TokenKind::LeftBrace => write!(f, "{{"),
            TokenKind::RightBrace => write!(f, "}}"),
            TokenKind::LeftBracket => write!(f, "["),
            TokenKind::RightBracket => write!(f, "]"),
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
            TokenKind::Percent => write!(f, "%"),
            TokenKind::Ampersand => write!(f, "&"),
            TokenKind::Set => write!(f, "set"),
        }
    }
}

/// An integer value and its associated radix.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Integer {
    pub radix: Radix,
    pub value: i64,
}

/// The radix or base of an `Integer`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Radix {
    Binary,
    Decimal,
    Hexadecimal,
    Octal,
}

impl fmt::Display for Integer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.radix {
            Radix::Binary => write!(f, "0b{:b}", self.value),
            Radix::Decimal => write!(f, "{}", self.value),
            Radix::Hexadecimal => write!(f, "0x{:x}", self.value),
            Radix::Octal => write!(f, "0o{:o}", self.value),
        }
    }
}

/// A `f64` value stored as raw bits.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Float(pub u64);

impl fmt::Display for Float {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let float: f64 = (*self).into();
        write!(f, "{}", float)
    }
}

impl From<f64> for Float {
    fn from(f: f64) -> Self {
        Self(f64::to_bits(f))
    }
}

impl FromStr for Float {
    type Err = std::num::ParseFloatError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse::<f64>().map(Float::from)
    }
}

impl From<Float> for f64 {
    fn from(f: Float) -> Self {
        f64::from_bits(f.0)
    }
}
