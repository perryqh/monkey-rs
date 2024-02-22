#[derive(Debug, PartialEq)]
pub enum Node {
    Program(Program),
    Statement(Statement),
    Expression(Expression),
}

pub trait NodeTrait {
    fn token_literal(&self) -> String;
}

#[derive(Debug, PartialEq)]
pub enum Statement {
    Let(LetStatement),
}

impl NodeTrait for Statement {
    fn token_literal(&self) -> String {
        match self {
            Statement::Let(_) => "let".to_string(),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct LetStatement {
    pub name: Identifier,
    pub value: Expression,
}

impl NodeTrait for LetStatement {
    fn token_literal(&self) -> String {
        "let".to_string()
    }
}

#[derive(Debug, PartialEq)]
pub struct Identifier {
    pub value: String,
}

impl NodeTrait for Identifier {
    fn token_literal(&self) -> String {
        self.value.clone()
    }
}

#[derive(Debug, PartialEq)]
pub enum Expression {
    Identifier(Identifier),
    IntegerLiteral(IntegerLiteral),
}

#[derive(Debug, PartialEq)]
pub struct IntegerLiteral {
    pub value: i64,
}

#[derive(Debug, PartialEq)]
pub struct Program {
    pub statements: Vec<Statement>,
}

impl Program {
    pub fn new() -> Self {
        Self {
            statements: Vec::new(),
        }
    }
}
