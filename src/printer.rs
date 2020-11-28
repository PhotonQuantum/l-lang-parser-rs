use crate::transpiler::{CoqProgram, CoqStmt};

const COQ_BASE: &str = "\
Require Import Coq.Strings.String.
Open Scope string_scope.
Require Import Coq.Lists.List.
Import ListNotations.

Inductive tm : Type :=
  | const: string -> tm
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> tm -> tm
  | mat : tm -> list (string * list string * tm) -> tm
  | rec : tm -> tm.

Section ind.

Variable
  (P: tm -> Prop)
  (Q: _ -> Prop)
  (F1: forall s, P (const s))
  (F2: forall s, P (var s))
  (F3: forall t, P t -> forall t0 : tm, P t0 -> P (app t t0))
  (F4: forall s t, P t -> P (abs s t))
  (F5: forall t, P t -> forall l, Q l -> P (mat t l))
  (F6: Q nil)
  (F7: forall cn vs t, P t -> forall l, Q l -> Q ((cn, vs, t) :: l))
  (F8: forall t, P t -> P (rec t)).

Fixpoint tm_mut_ind (t: tm): P t :=
  match t with
  | const s => F1 s
  | var s => F2 s
  | app t1 t2 => F3 t1 (tm_mut_ind t1) t2 (tm_mut_ind t2)
  | abs s t0 => F4 s t0 (tm_mut_ind t0)
  | mat t0 l => F5 t0 (tm_mut_ind t0) l
                  ((fix mat_list_ind (l: list (string * list string * tm)): Q l :=
                      match l with
                      | nil => F6
                      | (cn, vs, t) :: l0 =>
                           F7 cn vs t (tm_mut_ind t) l0 (mat_list_ind l0)
                      end) l)
  | rec t0 => F8 t0 (tm_mut_ind t0)
  end
.

End ind.

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

Definition tm_subst (x: string) (tx: tm) (t: tm) :=
  (fix tm_subst t :=
     match t with
     | const s => const s
     | var s => if string_dec x s then tx else var s
     | app t1 t2 => app (tm_subst t1) (tm_subst t2)
     | abs s t0 => if string_dec x s then abs s t0 else abs s (tm_subst t0)
                   (* This definition is OK because we assume [tx] is a closed term. *)
     | mat t0 l => mat (tm_subst t0) ((fix mat_list_subst l :=
                                         match l with
                                         | nil => nil
                                         | (cn, vs, t) :: l0 =>
                                           if string_list_dec x vs
                                           then (cn, vs, t) :: mat_list_subst l0
                                           else (cn, vs, tm_subst t) :: mat_list_subst l0
                                         end) l)
     | rec t0 => rec (tm_subst t0)
     end) t.

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
    then Some (app (tm_subst x (rec (abs x t1)) t1) t2)
    else match next_state t2 with
         | Some t2' => Some (app (rec (abs x t1)) t2')
         | None => None
         end
  | app (abs x t1) t2 =>
    if is_val t2
    then Some (tm_subst x t2 t1)
    else match next_state t2 with
         | Some t2' => Some (app (abs x t1) t2')
         | None => None
         end
  | app t1 t2 =>
    match next_state t1 with
    | Some t1' => Some (app t1' t2)
    | None => None
    end
  | abs _ _ => None
  | mat t l =>
    match is_const_hd_val t with
    | Some (s, ts) =>
        match l with
        | nil => None
        | (cn, vs, t0) :: l0 =>
          if string_dec s cn
          then if same_length ts vs
               then Some (fold_left app ts (fold_right abs t0 vs))
               else None
          else Some (mat t l0)
        end
    | None =>
        match next_state t with
        | Some t' => Some (mat t' l)
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

";

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
    Run {
        with_steps: bool,
        recursion_limit: usize,
    },
    Export {
        base: bool,
    },
}

pub fn generate_coq_code<'a>(coq_ast: &CoqProgram, mode: Mode) -> String {
    match mode {
        Mode::Run {
            with_steps,
            recursion_limit,
        } => {
            if with_steps {
                format!(
                    "{}\n{}\nCompute (multi_next_state main {}).",
                    COQ_BASE, &coq_ast, recursion_limit
                )
            } else {
                format!(
                    "{}\n{}\nCompute (head (multi_next_state main {})).",
                    COQ_BASE, &coq_ast, recursion_limit
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
