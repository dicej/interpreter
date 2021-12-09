use {
    anyhow::Result,
    std::fmt,
    syn::{Expr, Stmt},
};

pub struct Env {}

pub struct Eval {
    stmt: Stmt,
}

impl fmt::Display for Eval {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:#?}", self.stmt)
    }
}

impl Env {
    pub fn new() -> Env {
        Env {}
    }

    pub fn eval_line(&mut self, line: &str) -> Result<Eval> {
        let stmt = syn::parse_str::<Stmt>(line)
            .or_else(|_| syn::parse_str::<Expr>(line).map(Stmt::Expr))
            .or_else(|_| syn::parse_str::<Stmt>(&format!("{};", line)))?;

        Ok(Eval { stmt })
    }

    pub fn eval_file(&mut self, _file: &str) -> Result<Eval> {
        todo!()
    }
}
