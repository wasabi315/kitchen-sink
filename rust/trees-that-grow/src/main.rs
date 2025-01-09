use std::fmt::Debug;

trait ExprExt {
    type Var;
    type App;
    type Abs;
}

enum Expr<X: ExprExt> {
    Var(X::Var, String),
    App(X::App, Box<Expr<X>>, Box<Expr<X>>),
    Abs(X::Abs, String, Box<Expr<X>>),
}

trait ExprExtDebug: ExprExt<Var: Debug, App: Debug, Abs: Debug> {}

impl<X> ExprExtDebug for X where X: ExprExt<Var: Debug, App: Debug, Abs: Debug> {}

impl<X: ExprExtDebug> Debug for Expr<X> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Expr::*;

        match self {
            Var(x, s) => f.debug_tuple("Var").field(x).field(s).finish(),
            App(x, e1, e2) => f.debug_tuple("App").field(x).field(e1).field(e2).finish(),
            Abs(x, s, e) => f.debug_tuple("Abs").field(x).field(s).field(e).finish(),
        }
    }
}

enum Plain {}

impl ExprExt for Plain {
    type Var = ();
    type App = ();
    type Abs = ();
}

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
