const: (S _), O
const: true, false
def z_comb_ := λf.(λx.(f λv.(x x v)) λx.(f λv.(x x v)))
def gen_evenb := λf.λn.
    match n
    | S x => match x
            | S y => (f y)
            | O => false
    | O => true
def my_evenb := (z_comb_ gen_evenb)
def test_func := (my_evenb (S (S (S O))))
def test_func2 := (my_evenb (S (S (S (S O)))))
