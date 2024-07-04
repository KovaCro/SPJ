data Term = Var Int | Lam Term | App Term Term | Error
  deriving (Show, Read, Eq)

data TypedTerm = TVar Int | TLam TypedTerm Type | TApp TypedTerm TypedTerm
  deriving (Show, Read, Eq)

data Type = T Int | Arrow Type Type
  deriving (Show, Read, Eq)

-- Lista varijabli i njihovih tipova
type Context = [(Int, Type)]

-- d-place shift u termu
shift :: Int -> Term -> Term
shift d t = f 0 t
  where f c v@(Var x) = if x >= c then Var (d + x) else v
        f c (Lam t) = Lam $ f (c + 1) t
        f c (App t u) = App (f c t) (f c u)

-- Primjer (λλ 2 1 (λ 3))  
example_shift = shift 2 (Lam (Lam (App (App (Var 2) (Var 1)) (Lam (Var (3))))))

-- Supstitucija [y -> s]t
subst :: Int -> Term -> Term -> Term
subst j s t = f 0 t
  where f c v@(Var x) = if j + c == x then shift c s else v
        f c (Lam t) = Lam $ f (c + 1) t
        f c (App t u) = App (f c t) (f c u)

-- Primjer [1 -> λ0 1] (λλ 3 0)
example_subst = subst 1 (Lam (App (Var 0) (Var 1))) (Lam (Lam (App (Var 3) (Var 0))))

-- Beta redukcija
beta :: Term -> Term -> Term
beta s t = shift (-1) $ subst 0 (shift 1 s) t

-- Primjer (λ0) (λ1)
example_beta = beta (Lam (Var 1)) (Var 0)

-- Korak evaluacije
eval_step :: Term -> Term
eval_step (App (Lam t) u) = beta u t
eval_step (App t u) = App (eval_step t) (eval_step u)
eval_step (Lam t) = Lam $ eval_step t
eval_step t = t

-- Evaluacija
eval :: Term -> Term
eval t = if t == t' then t else eval t'
  where t' = eval_step t

-- Primjer (λ(λ0 1) 0) (λ0)
example_eval = eval (App (Lam (App (Lam (App (Var 0) (Var 1))) (Var 0))) (Lam (Var 0)))

-- Obrisi Type iz Terma
eraseType :: TypedTerm -> Term
eraseType (TVar x) = Var x
eraseType (TLam t _) = Lam (eraseType t)
eraseType (TApp t1 t2) = App (eraseType t1) (eraseType t2)

-- Primjer (λ:A(λ:B 0 1) 0) (λ:C 0)
example_erase = eraseType (TApp (TLam (TApp (TLam (TApp (TVar 0) (TVar 1)) (T 1)) (TVar 0)) (T 0)) (TLam (TVar 0) (T 2)))

-- Spaja Typeove
unify :: Type -> Type -> Maybe ()
unify (Arrow t11 t12) (Arrow t21 t22) = do
  unify t11 t21
  unify t12 t22
unify t1 t2 = if t1 == t2 then Just () else Nothing

-- U Contextu varijable s indexima -1 su bounded i uređenog poretka su
inferType :: TypedTerm -> Context -> Maybe Type
inferType (TVar x) ctx = 
  case lookup x ctx of
    Just t -> Just t
    _ -> return (snd (ctx!!x))
inferType (TLam t1 ty) ctx = do
    t1ty <- inferType t1 ([(-1, ty)]++ctx)
    Just (Arrow ty t1ty)
inferType (TApp t1 t2) ctx = do
  t1ty <- inferType t1 ctx
  t2ty <- inferType t2 ctx
  case t1ty of
    Arrow t' t'' -> if unify t' t2ty == Just () then Just t'' else Nothing
    _ -> Nothing

-- A = T 0, B = T 1
-- Primjer (λ:Aλ:(A->B) 0)
example_infer1 = inferType (TLam (TLam (TVar 0) (Arrow (T 0) (T 1))) (T 0)) []
-- Primjer (λ:Aλ:(A->B) 0 1)
example_infer2 = inferType (TLam (TLam (TApp (TVar 0) (TVar 1)) (Arrow (T 0) (T 1))) (T 0)) []
-- Primjer (λ:Aλ:(A->B) 0 1) (x:A)
example_infer3 = inferType (TApp (TLam (TLam (TApp (TVar 0) (TVar 1)) (Arrow (T 0) (T 1))) (T 0)) (TVar 10)) [(10, T 0)]
-- Primjer (λ:Aλ:(A->B) 0 1) (x:B)
example_infer4 = inferType (TApp (TLam (TLam (TApp (TVar 0) (TVar 1)) (Arrow (T 0) (T 1))) (T 0)) (TVar 10)) [(10, T 1)]

-- Evaluacija Typed Lambde
teval :: TypedTerm -> Context -> Term
teval t c = if inferType t c == Nothing then Error else eval $ eraseType $ t

-- Primjer (λ:Aλ:(A->B) 0 1) (x:A)
example_teval1 = teval (TApp (TLam (TLam (TApp (TVar 0) (TVar 1)) (Arrow (T 0) (T 1))) (T 0)) (TVar 10)) [(10, T 0)]
-- Primjer (λ:Aλ:(A->B) 0 1) (x:B)
example_teval2 = teval (TApp (TLam (TLam (TApp (TVar 0) (TVar 1)) (Arrow (T 0) (T 1))) (T 0)) (TVar 10)) [(10, T 1)]
-- Primjer (λ:(A->A)λ:A 1 0)) (λ:A 0)
example_teval3 = teval (TApp (TLam (TLam (TApp (TVar 1) (TVar 0)) (T 0)) (Arrow (T 0) (T 0))) (TLam (TVar 0) (T 0))) []