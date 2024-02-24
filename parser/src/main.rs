use lexer::lexer::Lexer;
use parser::parser::Parser;
use std::io::{self, stdin, Write};

pub fn main() {
    println!("Welcome to monkey parser REPL! Press Ctrl+C to exit.");

    loop {
        print!("> ");
        io::stdout().flush().expect("Failed to flush stdout");

        let mut input = String::new();
        match stdin().read_line(&mut input) {
            Ok(_) => {
                let trimmed_input = input.trim();
                if trimmed_input.is_empty() {
                    println!("bye!");
                    break; // Exit the loop with a break statement
                }
                let lexer = Lexer::new(trimmed_input); // Lexer can be immutable
                let mut parser = Parser::new(lexer);
                let program = parser.parse();

                match program {
                    Ok(program) => println!("{}", program),
                    Err(e) => println!("Error: {}", e),
                }
            }
            Err(error) => println!("Error reading line: {}", error),
        }
    }
}
