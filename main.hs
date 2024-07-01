data Term = Var Int | Lam Term | App Term Term
  deriving (Show, Read, Eq)

data TypedTerm = TVar Int | TLam TypedTerm Type | TApp TypedTerm TypedTerm
  deriving (Show, Read, Eq)

data Type = A | B | C | Arrow Type Type
  deriving (Show, Read, Eq)

-- Lista varijabli i njihovih tipova
type Context = [(Int, Type)]

-- d-place shift u termu
shift :: Int -> Term -> Term
shift d t = f 0 t
  where f c v@(Var x) = if x >= c then Var (d + x) else v
        f c (Lam t) = Lam $ f (c + 1) t
        f c (App t u) = App (f c t) (f c u)

-- Primjer (\.\.2 1 (\.3))  
example_shift = shift 2 (Lam (Lam (App (App (Var 2) (Var 1)) (Lam (Var (3))))))

-- Supstitucija [y -> s]t
subst :: Int -> Term -> Term -> Term
subst j s t = f 0 t
  where f c v@(Var x) = if j + c == x then shift c s else v
        f c (Lam t) = Lam $ f (c + 1) t
        f c (App t u) = App (f c t) (f c u)

-- Primjer [1 -> \.0 1] (\.\.3 0)
example_subst = subst 1 (Lam (App (Var 0) (Var 1))) (Lam (Lam (App (Var 3) (Var 0))))

-- Beta redukcija
beta :: Term -> Term -> Term
beta s t = shift (-1) $ subst 0 (shift 1 s) t

-- Primjer (\.0) (\.1)
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

-- Primjer (\.(\.0 1) 0) (\.0)
example_eval = eval (App (Lam (App (Lam (App (Var 0) (Var 1))) (Var 0))) (Lam (Var 0)))

-- Obrisi Type iz Terma
eraseType :: TypedTerm -> Term
eraseType (TVar x) = Var x
eraseType (TLam t _) = Lam (eraseType t)
eraseType (TApp t1 t2) = App (eraseType t1) (eraseType t2)

-- Primjer (\.:A(\.:B 0 1) 0) (\.:C 0)
example_erase = eraseType (TApp (TLam (TApp (TLam (TApp (TVar 0) (TVar 1)) B) (TVar 0)) A) (TLam (TVar 0) C))

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

-- Primjer (\.:A\.:(A->B) 0)
example_infer1 = inferType (TLam (TLam (TVar 0) (Arrow A B)) A) []
-- Primjer (\.:A\.:(A->B) 0 1)
example_infer2 = inferType (TLam (TLam (TApp (TVar 0) (TVar 1)) (Arrow A B)) A) []