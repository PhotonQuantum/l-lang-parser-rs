const: (S _), O
const: true, false
def z_comb_ := λf.(λx.(f λv.(x x v)) λx.(f λv.(x x v)))
def gen_evenb := λf.λn.
    match n
    | S x => match x
            | S x => (f x)
            | O => false
            end
    | O => true
    end
def my_evenb := (z_comb_ gen_evenb)
rec rec_evenb := λn.
    match n
    | S x => match x
            | S x => x
            | O => false
            end
    | O => true
    end
def test_func := (my_evenb (S (S (S O))))
def test_func2 := (rec_evenb (S (S (S (S O)))))
