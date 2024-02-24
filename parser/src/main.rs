use lexer::lexer::Lexer;
use parser::parser::Parser;
use std::io::stdin;

// REPL
pub fn main() {
    println!("Welcome to monkey parser REPL! Press Ctrl+C to exit.");

    loop {
        let mut input = String::new();
        stdin().read_line(&mut input).unwrap();

        if input.trim_end().is_empty() {
            println!("bye!");
            std::process::exit(0)
        }

        let lexer = Lexer::new(&input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse();

        match program {
            Ok(program) => println!("{}", program),
            Err(e) => println!("Error: {}", e),
        }
    }
}
