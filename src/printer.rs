use crate::transpiler::{CoqProgram, CoqStmt};

const COQ_BASE: &str = r#"
Require Import Coq.Strings.String.
Open Scope string_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Relations.Relation_Operators.

Inductive tm : Type :=
  | const: string -> tm (* only constructors are constants *)
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> tm -> tm
  | mat : tm -> string -> tm -> tm -> tm
  | rec : tm -> tm.

Inductive const_hd_val: tm -> Prop :=
| const_const_hd_val: forall s, const_hd_val (const s)
| app_const_hd_val: forall t1 t2, const_hd_val t1 -> val t2 -> const_hd_val (app t1 t2)
with val: tm -> Prop :=
| const_hd_val_val: forall t, const_hd_val t -> val t
| abs_val: forall s t, val (abs s t)
| rec_val: forall s t, val (rec (abs s t)).

Definition string_list_dec:
  forall (x: string) (xs: list string), {In x xs}  + {~ In x xs} :=
  fun x xs => @in_dec _ string_dec _ _.

Fixpoint list_minus (l: list string)(x: string): list string :=
  match l with
  | nil => nil
  | a :: b => if string_dec a x then (list_minus b x) else a :: (list_minus b x)
  end.

Fixpoint list_minus_vec (l: list string)(x: list string): list string :=
  match x with
  | nil => l
  | x' :: l' => list_minus_vec (list_minus l x') l'
  end.

Fixpoint count_free_var (t: tm): list string :=
  match t with
  | const s => nil
  | var s => [s]
  | app t1 t2 => (count_free_var t1) ++ (count_free_var t2)
  | abs x t => list_minus (count_free_var t) x
  | rec t => count_free_var t
  | mat t s t1 t2 => (count_free_var t) ++ (count_free_var t1) ++ (count_free_var t2)
  end.

Fixpoint count_var (t: tm): list string :=
  match t with
  | const s => nil
  | var s => [s]
  | app t1 t2 => (count_var t1) ++ (count_var t2)
  | abs x t =>  (count_var t)
  | rec t => count_var t
  | mat t s t1 t2 => (count_var t) ++ (count_var t1) ++ (count_var t2)
  end.

Fixpoint count_free_occur (x: string)(t: tm): nat :=
  match t with
  | const s => 0
  | var s => if string_dec x s then 1 else 0
  | app t1 t2 => (count_free_occur x t1) + (count_free_occur x t2)
  | abs s t =>  if string_dec x s then 0 else (count_free_occur x t)
  | rec t => count_free_occur x t
  | mat t s t1 t2 => (count_free_occur x t) + (count_free_occur x t1) + (count_free_occur x t2)
  end.


Definition var_max_length_in_tm (t: tm):=
let var_list:= (count_var t) in
  ((fix max_length l : nat :=
  match l with
  | nil => 0
  | a :: b => if (max_length b) <? (String.length a) then (String.length a) else (max_length b)
  end
  ) var_list).

Fixpoint create_new_var (n: nat):=
match n with
| O => "A"
| S n' => append "A"  (create_new_var n')
end.

Definition new_var (tx t: tm):=
if (var_max_length_in_tm tx) <? (var_max_length_in_tm t)
then create_new_var (var_max_length_in_tm t)
else create_new_var (var_max_length_in_tm tx).

Definition subst_task: Type := list (string * tm).

Fixpoint var_subst_task (st: subst_task) (x: string) :=
match st with
| nil => var x
| (x',t') :: l => if string_dec x' x then t' else var_subst_task l x
end.

Fixpoint count_var_in_st (st: subst_task) (x: string) :=
match st with
| nil => O
| (x',t') :: l => (count_free_occur x t')+ (count_var_in_st l x)
end.

Fixpoint tm_subst (st: subst_task) (t: tm): tm:=
  match t with
     | const s => const s
     | var s => var_subst_task st s
     | app t1 t2 => app (tm_subst st t1) (tm_subst st t2)
     | abs s t0 => ((fix abs_subst st' :=
                                                              match st' with
                                                              | nil => abs s t0
                                                              | (x' , t')::l => if string_dec x' s then abs_subst l else
                                                                                    match (count_free_occur s t') with
                            | O => abs s (tm_subst st t0)
                            | _ => let xn := new_var t0 t in
                                       abs xn (tm_subst ((s, var xn)::st) t0)
                            end end
                                                              )st)

     | mat t0 s t1 t2 => mat (tm_subst st t0) s (tm_subst st t1) (tm_subst st t2)
     | rec t0 => rec (tm_subst st t0)
  end.

Fixpoint is_const_hd_val_rec (t: tm) (tl: list tm) : option (string * list tm) :=
  match t with
  | const s => Some (s, tl)
  | app t1 t2 => if is_val t2 then is_const_hd_val_rec t1 (t2 :: tl) else None
  | _ => None
  end
with is_val (t: tm): bool :=
  match t with
  | abs _ _ => true
  | rec (abs _ _) => true
  | const _ => true
  | app t1 t2 => if is_val t2 then match is_const_hd_val_rec t1 (t2 :: nil) with | Some _ => true | _ => false end else false
  | _ => false
  end.

Definition is_const_hd_val (t: tm): option (string * list tm) :=
  is_const_hd_val_rec t nil.

Fixpoint same_length {A B : Type} (l: list A) (l': list B) :=
  match l, l' with
  | nil, nil => true
  | x :: tl, x' :: tl' => same_length tl tl'
  | _, _ => false
  end.

Fixpoint next_state (t: tm): option tm :=
  match t with
  | const _ => None
  | var _ => None
  | app (rec (abs x t1)) t2 =>
    if is_val t2
    then Some (app (tm_subst [(x,(rec (abs x t1)))] t1) t2)
    else match next_state t2 with
         | Some t2' => Some (app (rec (abs x t1)) t2')
         | None => None
         end
  | app (abs x t1) t2 =>
    if is_val t2
    then Some (tm_subst [(x,t2)] t1)
    else match next_state t2 with
         | Some t2' => Some (app (abs x t1) t2')
         | None => None
         end
  | app t1 t2 =>
    match next_state t1 with
    | Some t1' => Some (app t1' t2)
    | None => match next_state t2 with
                      | Some t1' => Some (app t1 t1')
                      | None => None
                      end

    end
  | abs _ _ => None
  | mat t c t1 t2 =>
    match is_const_hd_val t with
    | Some (s, ts) => if string_dec s c then Some(fold_left app ts t1) else Some(t2)
    | None =>
        match next_state t with
        | Some t' => Some (mat t' c t1 t2)
        | None => None
        end
    end
  | rec t0 => match next_state t0 with
              | Some t0' => Some (rec t0')
              | None => None
              end
  end.

Fixpoint multi_next_state(t: tm)(limit: nat): list tm :=
  match (next_state t) with
  | Some term => match limit with
                 | S n => (multi_next_state term n) ++ [term]
                 | O => nil
                 end
  | None => nil
  end.
"#;

pub fn check_main(coq_ast: &CoqProgram) -> bool {
    let mut has_main = false;
    for node in &coq_ast.stmts {
        let CoqStmt::Definition { name, expr: _ } = node;
        if name == "main" {
            has_main = true;
            break;
        }
    }
    has_main
}

pub enum Mode {
    Run { with_steps: bool, step_limit: usize },
    Export { base: bool },
}

pub fn generate_coq_code<'a>(coq_ast: &CoqProgram, mode: Mode) -> String {
    match mode {
        Mode::Run {
            with_steps,
            step_limit,
        } => {
            if with_steps {
                format!(
                    "{}\n{}\nCompute (multi_next_state main {}).",
                    COQ_BASE, &coq_ast, step_limit
                )
            } else {
                format!(
                    "{}\n{}\nCompute (head (multi_next_state main {})).",
                    COQ_BASE, &coq_ast, step_limit
                )
            }
        }
        Mode::Export { base } => {
            if base {
                format!("{}\n{}", COQ_BASE, &coq_ast)
            } else {
                format!("{}", &coq_ast)
            }
        }
    }
}
