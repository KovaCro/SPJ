data Term = Var Int | Lam Term | App Term Term
  deriving (Show, Read, Eq)
  
shift :: Int -> Term -> Term
shift d t = f 0 t
  where f c v@(Var x) = if x >= c then Var (d + x) else v
        f c (Lam t) = Lam $ f (c + 1) t
        f c (App t u) = App (f c t) (f c u)

subst :: Int -> Term -> Term -> Term
subst j s t = f 0 t
  where f c v@(Var x) = if j + c == x then shift c s else v
        f c (Lam t) = Lam $ f (c + 1) t
        f c (App t u) = App (f c t) (f c u)

beta :: Term -> Term -> Term
beta s t = shift (-1) $ subst 0 (shift 1 s) t

eval_step :: Term -> Term
eval_step (App (Lam t) u) = beta u t
eval_step (App t u) = App (eval_step t) (eval_step u)
eval_step (Lam t) = Lam $ eval_step t
eval_step t = t

eval :: Term -> Term
eval t = if t == t' then t else eval t'
  where t' = eval_step t