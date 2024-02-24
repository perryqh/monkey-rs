use lexer::lexer::Lexer;
use std::io::stdin;

// REPL
pub fn main() {
    println!("Welcome to monkey lexer REPL! Press Ctrl+C to exit.");

    loop {
        let mut input = String::new();
        stdin().read_line(&mut input).unwrap();

        if input.trim_end().is_empty() {
            println!("bye!");
            std::process::exit(0)
        }

        let lexer = Lexer::new(&input);

        for token in lexer {
            println!("{:?}", token);
        }
    }
}
