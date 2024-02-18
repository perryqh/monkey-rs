enum TokenType {
    ILLEGAL,
    EOF,

    // Identifiers + literals
    IDENT,
    INT,

    // Operators
    ASSIGN,
    PLUS,
    MINUS,
    BANG,
    ASTERISK,
    SLASH,

    LT,
    GT,

    EQ,
    NOT_EQ,

    // Delimiters
    COMMA,
    SEMICOLON,

    LPAREN,
    RPAREN,
    LBRACE,
    RBRACE,

    // Keywords
    FUNCTION,
    LET,
    TRUE,
    FALSE,
    IF,
    ELSE,
    RETURN,
}
struct Token {
    ttype: TokenType,
    literal: String,
}

impl From<&str> for TokenType {
    fn from(val: &str) -> TokenType {
        match val {
            "ILLEGAL" => TokenType::ILLEGAL,
            "EOF" => TokenType::EOF,
            _ => panic!("illegal token!")
        }
    }
}
