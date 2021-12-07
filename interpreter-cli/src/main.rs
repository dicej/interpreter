use {
    anyhow::Result,
    rustyline::{error::ReadlineError, Editor},
    std::{fs::File, io::Read, path::PathBuf},
    structopt::StructOpt,
    syn::Stmt,
};

const HISTORY_FILE: &str = ".interpreter-cli-history.txt";

#[derive(StructOpt, Debug)]
#[structopt(name = "interpreter-cli", about = "CLI for interpreter library")]
struct Options {
    input_file: Option<PathBuf>,
}

fn main() -> Result<()> {
    pretty_env_logger::init_timed();

    let options = Options::from_args();

    if let Some(input_file) = options.input_file {
        let mut content = String::new();

        File::open(&input_file)?.read_to_string(&mut content)?;

        println!("{:#?}", syn::parse_file(&content)?);
    } else {
        let mut rl = Editor::<()>::new();
        let _ = rl.load_history(HISTORY_FILE);

        loop {
            let readline = rl.readline(">> ");
            match readline {
                Ok(line) => {
                    rl.add_history_entry(line.as_str());

                    println!("{:#?}", syn::parse_str::<Stmt>(line.as_str()));

                    rl.save_history(HISTORY_FILE)?;
                }
                Err(ReadlineError::Interrupted | ReadlineError::Eof) => break,
                Err(err) => {
                    println!("Error: {:?}", err);
                    break;
                }
            }
        }
    }

    Ok(())
}
