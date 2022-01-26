use {
    anyhow::Result,
    interpreter::Env,
    rustyline::{error::ReadlineError, Editor},
    std::{fs::File, io::Read, path::PathBuf},
    structopt::StructOpt,
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

    let mut env = Env::new();

    if let Some(input_file) = options.input_file {
        let mut content = String::new();

        File::open(&input_file)?.read_to_string(&mut content)?;

        println!("{}", env.eval_file(&content)?);
    } else {
        let mut rl = Editor::<()>::new();
        let _ = rl.load_history(HISTORY_FILE);

        loop {
            match rl.readline(">> ") {
                Ok(line) => {
                    rl.add_history_entry(line.as_str());

                    println!("{}", env.eval_line(line.as_str())?);

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
