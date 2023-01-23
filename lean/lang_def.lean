import .lovelib

@[derive decidable_eq]
inductive ty : Type
| TNat : ty
| TBool : ty
| TFun : ty → ty → ty

#print decidable_eq
#check decidable
#check has_equiv

-- define all expressions
inductive exp : Type
| EVar (x : string) : exp -- Type of Var(x)
| ELam (x : string) (A : ty) (e : exp) : exp
| ERec (f x : string) (A B : ty) (e : exp) : exp -- TFun A → B
| EApp (e1 e2 : exp) : exp -- Type of e1 (Type of e2)
| ETrue : exp -- TBool
| EFalse : exp -- TBool
| EIf (e1 e2 e3 : exp) : exp -- Type of e2 and e3
| Ezero : exp -- TNat
| ESucc : exp -- TNat → TNat
| EPred : exp -- TNat → TNat
| EIsZero : exp -- TNat → TBool

-- type context
inductive ctx : Type
| ctx_nil : ctx
| ctx_snoc (Γ : ctx) (x : string) (A : ty) : ctx

-- Exercise 1
-- operation to lookup the type of a variable in a typing context:
def ctx_lookup (x : string) : ctx → option ty
| ctx.ctx_nil          := option.none
| (ctx.ctx_snoc Γ y A) := if y = x then option.some A else ctx_lookup Γ

inductive typed : ctx → exp → ty → Prop
| Var_typed (Γ : ctx) (x : string) (A : ty) (p : ctx_lookup x Γ = option.some A) : typed Γ (exp.EVar x) A
| True_typed {Γ : ctx} : typed Γ exp.ETrue ty.TBool
| False_typed {Γ : ctx} : typed Γ exp.EFalse ty.TBool
| If_typed (Γ : ctx) (e1: exp) (e2: exp) (e3: exp) (A: ty) (p1 : typed Γ e1 ty.TBool) (p2: typed Γ e2 A) (p3: typed Γ e3 A) : typed Γ (exp.EIf e1 e2 e3) A
| Zero_typed {Γ : ctx} : typed Γ exp.Ezero ty.TNat
| Succ_typed {Γ : ctx} (A : ty) (p : (ty.TFun ty.TNat ty.TNat) = A): typed Γ exp.ESucc A
| Pred_typed {Γ : ctx} (A : ty) (p : (ty.TFun ty.TNat ty.TNat) = A): typed Γ exp.EPred A
| IsZero_typed {Γ : ctx} (A : ty) (p : (ty.TFun ty.TNat ty.TBool) = A) : typed Γ exp.EIsZero A
| Lam_typed (Γ : ctx) (x : string) (e : exp) (aa et A : ty) (p : (ty.TFun aa et) = A) (p2 : typed (ctx.ctx_snoc Γ x aa) e et) : typed Γ (exp.ELam x aa e) A
| Rec_typed (Γ : ctx) (f: string) (x : string) (aa bb A: ty) (e : exp) (p1 : (ty.TFun aa bb) = A) (p2: typed (ctx.ctx_snoc (ctx.ctx_snoc Γ x aa) f (ty.TFun aa bb)) e bb) : typed Γ (exp.ERec f x aa bb e) A
| App_typed (Γ : ctx) (e1 e2 : exp) (e2t A : ty) (p1 : typed Γ e2 e2t) (p2 : typed Γ e1 (ty.TFun e2t A)) : typed Γ (exp.EApp e1 e2) A

-- Exercise 2
constants (Γ : ctx)
lemma test_id_nat : typed Γ (exp.ELam "x" ty.TNat (exp.EVar "x")) (ty.TFun ty.TNat ty.TNat) :=
  begin
    apply typed.Lam_typed,
    refl,
    apply typed.Var_typed,
    simp [ctx_lookup],
  end

lemma test_isZero : typed Γ (exp.ELam "x" ty.TNat exp.EIsZero) (ty.TFun ty.TNat (ty.TFun ty.TNat ty.TBool)) :=
  begin
    apply typed.Lam_typed,
    refl,
    apply typed.IsZero_typed,
    refl,
  end

lemma test_everything : typed Γ
  (exp.ERec "f" "x" ty.TNat ty.TNat (exp.EIf (exp.EApp exp.EIsZero (exp.EVar "x")) (exp.Ezero) (exp.EApp exp.ESucc (exp.EApp exp.ESucc (exp.EApp (exp.EVar "f") (exp.EApp exp.EPred (exp.EVar "x"))))))) (ty.TFun ty.TNat ty.TNat) :=
  begin
    apply typed.Rec_typed,
    refl,
    apply typed.If_typed,
      apply typed.App_typed,
      apply typed.Var_typed,
      simp [ctx_lookup],
      refl,
    apply typed.IsZero_typed,
    refl,
    apply typed.Zero_typed,
    apply typed.App_typed,
    apply typed.App_typed,
    apply typed.App_typed,
    apply typed.App_typed,
    apply typed.Var_typed,
    simp [ctx_lookup],
    refl,
    apply typed.Pred_typed,
    refl,
    apply typed.Var_typed,
    simp [ctx_lookup],
    apply typed.Succ_typed,
    refl,
    apply typed.Succ_typed,
    refl,
  end

-- Exercise 4
-- def f(x : Nat) : Nat → Bool:
--   return lambda y : Nat:
--     if x == 0:
--       if y == 0:
--         return true
--       else:
--         return false
--     else:
--       if y == 0:
--         return false
--       else:
--         return (f(x - 1))(y - 1)
lemma test_check_equal : typed Γ
(
  exp.ERec "f" "x" ty.TNat (ty.TFun ty.TNat ty.TBool)
  (
    exp.ELam "y" ty.TNat
    (
      exp.EIf (exp.EApp exp.EIsZero (exp.EVar "x"))
      (
        exp.EIf (exp.EApp exp.EIsZero (exp.EVar "y"))
          exp.ETrue
          exp.EFalse
      )
      (
        exp.EIf (exp.EApp exp.EIsZero (exp.EVar "y"))
          exp.EFalse
          (
            exp.EApp
            (exp.EApp (exp.EVar "f") (exp.EApp exp.EPred (exp.EVar "x")))
            (exp.EApp exp.EPred (exp.EVar "y"))
          )
      )
    )
  )
)
(ty.TFun ty.TNat (ty.TFun ty.TNat ty.TBool)) :=
begin
  apply typed.Rec_typed,
  {
    refl,
  },
  {
    apply typed.Lam_typed,
    {
      refl,
    },
    {
      apply typed.If_typed,
      {
        apply typed.App_typed,
        {
          apply typed.Var_typed,
            refl,
        },
        {
          apply typed.IsZero_typed,
            refl,
        },
      },
      {
        apply typed.If_typed,
        {
          apply typed.App_typed,
          {
            apply typed.Var_typed,
              refl,
          },
          {
            apply typed.IsZero_typed,
              refl,
          },
        },
        {
          apply typed.True_typed,
        },
        {
          apply typed.False_typed,
        },
      },
      {
        apply typed.If_typed,
        {
          apply typed.App_typed,
          {
            apply typed.Var_typed,
              refl,
          },
          {
            apply typed.IsZero_typed,
              refl,
          },
        },
        {
          apply typed.False_typed,
        },
        {
          apply typed.App_typed,
          {
            apply typed.App_typed,
            {
              apply typed.Var_typed,
              refl,
            },
            {
              apply typed.Pred_typed,
                refl,
            },
          },
          {
            apply typed.App_typed,
            {
              apply typed.App_typed,
              {
                apply typed.Var_typed,
                refl,
              },
              {
                apply typed.Pred_typed,
                  refl,
              },
            },
            {
              apply typed.Var_typed,
                refl,
            },
          },
        }
      },
    },
  },
end

-- Exercise 4
def type_infer : ctx → exp → option ty
| Γ (exp.EVar x)           := ctx_lookup x Γ
| Γ exp.ETrue              := some ty.TBool
| Γ exp.EFalse             := some ty.TBool
| Γ (exp.EIf e1 e2 e3)     :=
  match type_infer Γ e1 with
  | some ty.TBool :=
    match type_infer Γ e2, type_infer Γ e3 with
    | some tA, some tB  := if tA = tB then (some tA) else none
    | _, _            := none
    end
  | _ := none
  end
| Γ exp.Ezero             := some ty.TNat
| Γ exp.ESucc             := some (ty.TFun ty.TNat ty.TNat)
| Γ exp.EPred             := some (ty.TFun ty.TNat ty.TNat)
| Γ exp.EIsZero           := some (ty.TFun ty.TNat ty.TBool)
| Γ (exp.ELam x A e)      :=
  match type_infer (ctx.ctx_snoc Γ x A) e with
  | some B  := some (ty.TFun A B)
  | none    := none
  end
| Γ (exp.ERec f x A B e)  :=
  match type_infer (ctx.ctx_snoc (ctx.ctx_snoc Γ x A) f (ty.TFun A B)) e with
  | some C := if B = C then some (ty.TFun A B) else none
  | _ := none
  end
| Γ (exp.EApp e1 e2)      :=
  match type_infer Γ e1, type_infer Γ e2 with
  | some (ty.TFun A B), some C := if A = C then some B else none
    | _, _                 := none
  end

-- Exercise 5
-- TODO: Not Implemented Yet

-- Exercise 6
lemma type_infer_complete (Γ : ctx) (e : exp) (A : ty) : typed Γ e A → type_infer Γ e = option.some A :=
begin
  intro h,
  induction h,
    simp [type_infer, h_p],
    simp [type_infer],
    simp [type_infer],
    simp [type_infer, h_p1, h_p2, h_p3],
    simp [type_infer, h_p1, h_p2, h_p3, h_ih_p1, h_ih_p2, h_ih_p3],
    simp [type_infer],
    simp [type_infer, h_p],
    simp [type_infer, h_p],
    simp [type_infer, h_p],
    simp [type_infer, h_p2, h_ih, h_p],
    {
      simp [type_infer],
      simp [h_ih],
      simp [type_infer],
      exact h_p1,
    },
    simp [type_infer, h_p1, h_p2, h_ih_p1, h_ih_p2],
end

-- Acknowledge
-- https://www.cs.cornell.edu/courses/cs4160/2019sp/terse/plf/Typechecking.html
-- Although I read the above link, it is still a tough proof for me
-- I guess I should use a lot of finishes to shrink the proof a lot and a lot
lemma type_infer_sound: ∀Γ e A, type_infer Γ e = option.some A → typed Γ e A :=
begin
  intros Γ e,
  induction' e;
  intros T h;
  cases' h,

  {
    -- case Var
    simp [type_infer] at cases_eq,
    destruct (ctx_lookup x Γ),
    intro htt,
    apply typed.Var_typed,
      exact cases_eq,
      intros val hhh,
    apply typed.Var_typed,
      exact cases_eq,
  },
  {
    -- case Lam
    simp [type_infer] at cases_eq,
    generalize htt : Γ.ctx_snoc x A = GG,
    generalize hto : type_infer GG e = TOO,
    have httr : GG = Γ.ctx_snoc x A, from
      begin
        apply eq.symm,
        exact htt,
      end,
    rw [httr] at hto,
    rw [hto] at cases_eq,
    cases' TOO,

      by_contra,
      simp [type_infer] at cases_eq,
      exact cases_eq,

      apply typed.Lam_typed,
        -- Need to fix the type variable first
        swap 3,
        exact val,

        simp [type_infer] at cases_eq,
        exact cases_eq,

        apply ih,
        exact hto,
  },
  {
    -- case Rec
    simp [type_infer] at cases_eq,
    generalize htt : Γ.ctx_snoc x A = GG,
    generalize httt : GG.ctx_snoc f (A.TFun B) = GGG,
    generalize hto : type_infer GGG e = TOOO,
    have httr : GG = Γ.ctx_snoc x A, from
      begin
        apply eq.symm,
        exact htt,
      end,
    rw [httr] at httt,
    have htttr : GGG = (Γ.ctx_snoc x A).ctx_snoc f (A.TFun B), from
      begin
        apply eq.symm,
        exact httt,
      end,
    rw [htttr] at hto,
    rw [hto] at cases_eq,
    cases' TOOO,

      by_contra,
      simp [type_infer] at cases_eq,
      exact cases_eq,

      apply typed.Rec_typed,
        simp [type_infer] at cases_eq,
        rw [if_pos] at cases_eq,
          simp [option.iget_some] at cases_eq,
          exact cases_eq,

        by_contra,
          have hc : (B = val) = false, from
            begin
              simp [h],
            end,
            simp [hc] at cases_eq,
            exact cases_eq,

      apply ih,
      rw hto,
      simp *,
      simp [type_infer] at cases_eq,
        apply eq.symm,
        by_contra,
          have hc : (B = val) = false, from
            begin
              simp [h],
            end,
          simp [hc] at cases_eq,
          exact cases_eq,
  },
  {
    -- case apply
    simp [type_infer] at cases_eq,
    generalize hto : type_infer Γ e = TO,
    generalize htoo : type_infer Γ e_1 = TOO,
    cases' TO,
      by_contra,
      rw [hto] at cases_eq,
      simp [type_infer] at cases_eq,
      exact cases_eq,

      cases' TOO,
        by_contra,
        rw [htoo] at cases_eq,
        rw [hto] at cases_eq,
        cases' val,
          simp [type_infer] at cases_eq,
          exact cases_eq,

          simp [type_infer] at cases_eq,
          exact cases_eq,

          simp [type_infer] at cases_eq,
          exact cases_eq,

        apply typed.App_typed,
          swap 3,
          exact val_1,

          apply ih_e_1,
          exact htoo,

          apply ih_e,
          simp [hto],
          rw [hto, htoo] at cases_eq,
          cases' val,
            simp [type_infer] at cases_eq,
            by_contra,
            exact cases_eq,

            simp [type_infer] at cases_eq,
            by_contra,
            exact cases_eq,

            simp [type_infer] at cases_eq,
            have hvalval1 : val = val_1, from
            begin
              by_contra,
              have hne : val ≠ val_1, from
              begin
                simp *,
              end,
              simp [hne] at cases_eq,
              exact cases_eq,
            end,
            rw [if_pos] at cases_eq,
            simp [option.iget] at cases_eq,
            simp *,
            assumption,
  },
  {
    -- case True
    simp [typed.True_typed],
  },
  {
    -- case False
    simp [typed.False_typed],
  },
  {
    -- case If
    simp [type_infer] at cases_eq,
    generalize hto1 : type_infer Γ e_1 = TO1,
    generalize hto2 : type_infer Γ e_2 = TO2,
    generalize hto : type_infer Γ e = TO,
    rw [hto] at cases_eq,
    cases' TO,
      simp [type_infer] at cases_eq,
      by_contra,
      exact cases_eq,

      cases' val,
        simp [type_infer] at cases_eq,
        by_contra,
        exact cases_eq,

      {
        simp [type_infer] at cases_eq,
        apply typed.If_typed,
        cases' TO1,
          rw [hto1] at cases_eq,
          simp [type_infer] at cases_eq,
          by_contra,
          exact cases_eq,

          cases' TO2,
            rw [hto1, hto2] at cases_eq,
            simp [type_infer] at cases_eq,
            by_contra,
            exact cases_eq,

            apply ih_e,
            exact hto,

          apply ih_e_1,
          rw hto1,
          rw [hto1, hto2] at cases_eq,
          cases' TO1,
            simp [type_infer] at cases_eq,
            by_contra,
            exact cases_eq,

            simp,
            cases' TO2,
              simp [type_infer] at cases_eq,
              by_contra,
              exact cases_eq,

              simp [type_infer] at cases_eq,
              have hvalval1 : val = val_1, from
              begin
                by_contra,
                have hne : val ≠ val_1, from
                begin
                  simp [h],
                end,
                simp [hne] at cases_eq,
                exact cases_eq,
              end,
              simp [hvalval1] at cases_eq,
              simp *,

          apply ih_e_2,
          cases' TO2,
            cases' TO1,
              simp [type_infer, hto1, hto2] at cases_eq,
              by_contra,
              exact cases_eq,

              simp [type_infer, hto1, hto2] at cases_eq,
              by_contra,
              exact cases_eq,

            cases' TO1,
              simp [type_infer, hto1, hto2] at cases_eq,
              by_contra,
              exact cases_eq,

              simp [type_infer, hto1, hto2] at cases_eq,
              have hvalval1 : val_1 = val, from
              begin
                by_contra,
                have hne : val_1 ≠ val, from
                begin
                  simp [h],
                end,
                simp [hne] at cases_eq,
                exact cases_eq,
              end,
              simp [hvalval1] at cases_eq,
              simp *,
      },

        simp [type_infer] at cases_eq,
        by_contra,
        exact cases_eq,
  },
  {
    -- case Zero
    simp [typed.Zero_typed],
  },
  {
    -- case Succ
    simp [typed.Succ_typed],
  },
  {
    -- case Pred
    simp [typed.Pred_typed],
  },
  {
    -- case IsZero
    simp [typed.IsZero_typed],
  },
end
