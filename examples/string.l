const: (Ascii _ _ _ _ _ _ _ _)
const: (String _), EmptyString
const: true, false

fix bool_eqb := lam a.lam b.
    match a
    | true => 
        match b
        | true => true
        | false => false
        end
    | false =>
        match b
        | true => false
        | false => true
        end
    end

fix ascii_eqb := lam a.lam b.
match a
| Ascii a0 a1 a2 a3 a4 a5 a6 a7 =>
    match b
    | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
        if
         if
          if
           if
            if
             if if (bool_eqb a0 b0) then (bool_eqb a1 b1) else false
             then (bool_eqb a2 b2)
             else false
            then (bool_eqb a3 b3)
            else false
           then (bool_eqb a4 b4)
           else false
          then (bool_eqb a5 b5)
          else false
         then (bool_eqb a6 b6)
         else false
        then (bool_eqb a7 b7)
        else false
    end
end

fix string_eqb := lam s1.lam s2.
    match s1
    | EmptyString => 
        match s2
        | EmptyString => true
        | String _ _ => false
        end
    | String c1 s1' =>
        match s2
        | EmptyString => false
        | String c2 s2' =>
            match (ascii_eqb c1 c2)
            | true => (string_eqb s1' s2')
            | _ => false
            end
        end
    end

def main := (string_eqb "test" "test")
