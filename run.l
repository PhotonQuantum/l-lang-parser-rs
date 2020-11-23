const: abs, app, const, var
const: Some, None
const: nil
def my_func := lam t.match t
| abs _ _ => true
| _ => match (is_const_hd_val t)
       | Some _ => true
       | _ => false
def y_comb := λf.(λx.(f (x x)) λx.(f (x x)))
def run := (y_comb gen_run)