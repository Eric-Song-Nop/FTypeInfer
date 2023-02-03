import .lovelib
import data.set
open set

@[derive decidable_eq]
inductive ty : Type
| TNat : ty
| TBool : ty
| TFun : ty → ty → ty
| TVar : ℕ → ty
| TForAll : ty → ty

@[derive decidable_eq]
inductive bi : Type
| VarBind : ty → bi
| TarBind : bi -- Tar is short for type variable, to have same length as Var

#print decidable_eq
#check decidable
#check has_equiv
#check option

-- -- type context
-- inductive ctx : Type
-- | ctx_nil : ctx
-- | ctx_snoc (Γ : ctx) (x : bi) : ctx

-- -- operation to lookup the type of a variable in a typing context:
-- def ctx_lookup_bi (x : bi) : ctx → option bi
-- | ctx.ctx_nil          := option.none
-- | (ctx.ctx_snoc Γ y) := if y = x then option.some y else ctx_lookup_bi Γ

-- operation to lookup the type of a variable in a typing context:
def bi_lookup (i : ℕ) (Γ : list bi) : option ty :=
match (list.nth Γ i) with
| none := none
| some b := match b with
  | bi.VarBind t := some t
  | _ := none
  end
end

-- define all expressions
inductive exp : Type
| EVar (i : ℕ) : exp -- Type of Var(x)
| ELam (A : ty) (e : exp) : exp
| ERec (A B : ty) (e : exp) : exp -- TFun A → B
| EApp (e1 e2 : exp) : exp -- Type of e1 (Type of e2)
| ETrue : exp -- TBool
| EFalse : exp -- TBool
| EIf (e1 e2 e3 : exp) : exp -- Type of e2 and e3
| Ezero : exp -- TNat
| ESucc : exp -- TNat → TNat
| EPred : exp -- TNat → TNat
| EIsZero : exp -- TNat → TBool

| ETAbs (e : exp) : exp
| ETApp (e : exp) (T : ty) : exp

def add_bi (ctx : list bi) (b : bi) : list bi := (b::ctx)

def typeShiftAbove : ty → ℕ → ℕ → ty
| (ty.TVar x) d cc := if x >= cc then ty.TVar (x + d) else ty.TVar(x)
| (ty.TFun t1 t2) d cc := ty.TFun (typeShiftAbove t1 d cc) (typeShiftAbove t2 d cc)
| (ty.TForAll t) d cc := ty.TForAll (typeShiftAbove t d (cc + 1))
| tyT _ _ := tyT

def typeShiftBelow : ty → ℕ → ℕ → ty
| (ty.TVar x) d cc := if x >= cc then ty.TVar (x - d) else ty.TVar(x)
| (ty.TFun t1 t2) d cc := ty.TFun (typeShiftAbove t1 d cc) (typeShiftAbove t2 d cc)
| (ty.TForAll t) d cc := ty.TForAll (typeShiftAbove t d (cc + 1))
| tyT _ _ := tyT

def tsa (d : ℕ) (tyT : ty) : ty := typeShiftAbove tyT d 0
def tsb (d : ℕ) (tyT : ty) : ty := typeShiftBelow tyT d 0

def typeSubst : ty → ty → ℕ → ty
| (ty.TVar i) tyS c := if i = c then tsa c tyS else (ty.TVar i)
| (ty.TFun t1 t2) tyS c := ty.TFun (typeSubst t1 tyS c) (typeSubst t2 tyS c)
| (ty.TForAll t) tyS c := ty.TForAll(typeSubst t tyS (c + 1))
| tyT _ _ := tyT

def typeSubstTop (tyS tyT : ty): ty :=
  tsb 1 (typeSubst tyT (tsa 1 tyS) 0)


inductive typed : list bi → exp → ty → Prop
| Var_typed (Γ : list bi) (x : ℕ) (A : ty) (p : bi_lookup x Γ = option.some A) : typed Γ (exp.EVar x) A
| True_typed {Γ : list bi} : typed Γ exp.ETrue ty.TBool
| False_typed {Γ : list bi} : typed Γ exp.EFalse ty.TBool
| If_typed (Γ : list bi) (e1: exp) (e2: exp) (e3: exp) (A: ty) (p1 : typed Γ e1 ty.TBool) (p2: typed Γ e2 A) (p3: typed Γ e3 A) : typed Γ (exp.EIf e1 e2 e3) A
| Zero_typed {Γ : list bi} : typed Γ exp.Ezero ty.TNat
| Succ_typed {Γ : list bi} (A : ty) (p : (ty.TFun ty.TNat ty.TNat) = A): typed Γ exp.ESucc A
| Pred_typed {Γ : list bi} (A : ty) (p : (ty.TFun ty.TNat ty.TNat) = A): typed Γ exp.EPred A
| IsZero_typed {Γ : list bi} (A : ty) (p : (ty.TFun ty.TNat ty.TBool) = A) : typed Γ exp.EIsZero A
| Lam_typed (Γ : list bi) (e : exp) (aa et A : ty) (p : (ty.TFun aa et) = A) (p2 : typed (add_bi Γ (bi.VarBind aa)) e et) : typed Γ (exp.ELam aa e) A
| Rec_typed (Γ : list bi) (aa bb A: ty) (e : exp) (p1 : (ty.TFun aa bb) = A) (p2: typed (add_bi (add_bi Γ (bi.VarBind aa)) (bi.VarBind (ty.TFun aa bb))) e bb) : typed Γ (exp.ERec aa bb e) A
| App_typed (Γ : list bi) (e1 e2 : exp) (e2t A : ty) (p1 : typed Γ e2 e2t) (p2 : typed Γ e1 (ty.TFun e2t A)) : typed Γ (exp.EApp e1 e2) A

| TAbs_typed {Γ : list bi} (e : exp) (A T: ty) (p1 : typed (add_bi Γ bi.TarBind) e A) (p2 : T = ty.TForAll A): typed Γ (exp.ETAbs e) T
| TApp_typed {Γ : list bi} (tt1 : exp) (TT2 A : ty) {TT12 : ty} (p1 : typed Γ tt1 (ty.TForAll TT12)) (p2 : typeSubstTop TT2 TT12 = A) : typed Γ (exp.ETApp tt1 TT2) A

def type_infer : list bi → exp → option ty
| Γ (exp.EVar x)           := bi_lookup x Γ
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
| Γ (exp.ELam A e)      :=
  match type_infer (add_bi Γ (bi.VarBind A)) e with
  | some B  := some (ty.TFun A B)
  | none    := none
  end
| Γ (exp.ERec A B e)  :=
  match type_infer (add_bi (add_bi Γ (bi.VarBind A)) (bi.VarBind (ty.TFun A B))) e with
  | some C := if B = C then some (ty.TFun A B) else none
  | _ := none
  end
| Γ (exp.EApp e1 e2)      :=
  match type_infer Γ e1, type_infer Γ e2 with
  | some (ty.TFun A B), some C := if A = C then some B else none
    | _, _                 := none
  end
| Γ (exp.ETAbs e) :=
  match type_infer (add_bi Γ (bi.TarBind)) e with
  | some C := some (ty.TForAll C)
  | _ := none
  end
| Γ (exp.ETApp e t) :=
  match type_infer Γ e with
  | some ty1 := match ty1 with
    | ty.TForAll ttt := some (typeSubstTop t ttt)
    | _ := none
    end
  | _ := none
  end

lemma type_infer_complete (Γ : list bi) (e : exp) (A : ty) : typed Γ e A → type_infer Γ e = option.some A :=
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
    -- These tow line are extended for ETAbs and ETApp
    simp [type_infer, h_p1, h_p2, h_ih],
    simp [type_infer, h_p1, h_p2, h_ih, typeSubstTop],
    finish,
end

lemma type_infer_sound: ∀Γ e A, type_infer Γ e = option.some A → typed Γ e A :=
begin
  intros Γ e,
  revert Γ,
  induction' e;
  intros Γ TT h;
  cases' h,

  {
    -- case Var
    simp [type_infer] at cases_eq,
    destruct (bi_lookup i Γ),
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
    generalize htt : add_bi Γ (bi.VarBind A) = GG,
    generalize hto : type_infer GG e = TOO,
    have httr : GG = add_bi Γ (bi.VarBind A), from
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
    generalize htt : add_bi Γ (bi.VarBind A) = GG,
    generalize httt : add_bi GG (bi.VarBind (A.TFun B)) = GGG,
    generalize hto : type_infer GGG e = TOOO,
    have httr : GG = add_bi Γ (bi.VarBind A), from
      begin
        apply eq.symm,
        exact htt,
      end,
    rw [httr] at httt,
    have htttr : GGG = add_bi (add_bi Γ (bi.VarBind A)) (bi.VarBind(A.TFun B)), from
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

            -- Is this magic?
            finish,
            finish,
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

        finish,
        finish,
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
  {
    -- case Type Abs
    simp [type_infer] at cases_eq,
    generalize htt : add_bi Γ bi.TarBind = GG,
    generalize hto : type_infer GG e = TOO,
    have httr : GG = add_bi Γ bi.TarBind, from
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

      apply typed.TAbs_typed,
        -- Need to fix the type variable first
        swap 3,
        exact val,

        simp [type_infer] at cases_eq,
        apply ih,
        exact hto,

        simp [type_infer] at cases_eq,
        simp [cases_eq],
  },
  {
    -- case TApp
    simp [type_infer] at cases_eq,
    generalize hto : type_infer Γ e = TO,
    cases' TO,
      by_contra,
      finish,

      rw [hto] at cases_eq,
      simp [type_infer, typeSubstTop] at cases_eq,
      cases' val,
        finish,
        finish,
        finish,
        finish,
        apply typed.TApp_typed,
        swap 3,
          exact val,

          apply ih,
          exact hto,

          simp [type_infer] at cases_eq,
          exact cases_eq,
  },
end
