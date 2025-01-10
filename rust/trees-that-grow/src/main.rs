use std::fmt::Debug;

trait ExprExt {
    type Var;
    type App;
    type Abs;
}

#[derive(Debug, Clone)]
enum Expr<X: ExprExt> {
    Var(X::Var, String),
    App(X::App, Box<Expr<X>>, Box<Expr<X>>),
    Abs(X::Abs, String, Box<Expr<X>>),
}

#[derive(Debug)]
enum Plain {}

impl ExprExt for Plain {
    type Var = ();
    type App = ();
    type Abs = ();
}

#[derive(Debug)]
enum Qualified {}

impl ExprExt for Qualified {
    type Var = String;
    type App = ();
    type Abs = ();
}

fn main() {
    use Expr::*;

    let expr: Expr<Plain> = Abs(
        (),
        "f".to_string(),
        Box::new(Abs(
            (),
            "x".to_string(),
            Box::new(App(
                (),
                Box::new(Var((), "f".to_string())),
                Box::new(Var((), "x".to_string())),
            )),
        )),
    );

    println!("{:?}", expr);

    let expr: Expr<Qualified> = Abs(
        (),
        "f".to_string(),
        Box::new(Abs(
            (),
            "x".to_string(),
            Box::new(App(
                (),
                Box::new(Var("NS1".to_string(), "f".to_string())),
                Box::new(Var("NS2".to_string(), "x".to_string())),
            )),
        )),
    );

    println!("{:?}", expr);
}
