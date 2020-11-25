const: (abs _ _), (app _ _), (const _), (var _)
const: Some, None
const: true, false
const: nil
const: (S _), O
def my_func := lam t.match t
| abs _ _ => true
| _ => match (is_const_hd_val t)
       | Some _ => true
       | _ => false
def y_comb := λf.(λx.(f (x x)) λx.(f (x x)))
def run := (y_comb gen_run)
rec my_prec := λn.
    match n
    | S x => x
    | O => O
def test_func := (my_prec (S (S (S O))))