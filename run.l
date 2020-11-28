const: (S _), O
const: true, false
fix my_evenb := λn.
    match n
    | S x => match x
            | S x => (my_evenb x)
            | O => false
            end
    | O => true
    end

def main := (my_evenb (S (S (S (S O)))))
