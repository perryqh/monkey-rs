use std::fmt::{self, Display, Formatter};

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Object {
    Integer(i64),
    Boolean(bool),
    Null,
}

impl Display for Object {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Object::Integer(i) => write!(f, "{}", i),
            Object::Boolean(b) => write!(f, "{}", b),
            Object::Null => write!(f, "null"),
        }
    }
}