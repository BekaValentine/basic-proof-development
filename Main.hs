import Control.Applicative
import Control.Monad.State





-- Here we define terms of the STLC with natural numbers and booleans.

data Term = Var Int
          | Pair Term Term
          | Fst Term
          | Snd Term
          | Lam Term
          | App Term Term
          | Zero
          | Suc Term
          | Rec Term Term Term
          | T
          | F
          | If Term Term Term
  deriving (Show,Eq)


-- And here are the types. Prod is product/pair, Fun is functions.

data Type = Prod Type Type
          | Fun Type Type
          | Nat
          | Boolean
  deriving (Show,Eq)


-- The STLC has one judgment `A true` that a proposition is true. Other type
-- theories would have other judgments, eg. `A at time t` or `A false`.

data Judgment = IsTrue Type
  deriving (Show,Eq)


-- A context is just a list of types that are assigned to de Bruijn index vars

type Context = [Judgment]


-- A hypothetical judgment is a claim that some term is a proof of some
-- judgment under some hypotheses. This corresponds to `Γ ⊢ M : T`

data HypJudgment = HypJudgment Context Term Judgment
  deriving (Show,Eq)


-- The main job of this type of theorem prover/type checker is to solve a
-- proof problem. Any given problem consists of a number of hypothetical
-- judgments that correspond to the as-of-yet unproven leaves of a derivation
-- tree.

type ProofProblem = [HypJudgment]


-- A tactic is just some way of expanding one hypothetical judgment into some
-- other ones, possibly none if the tactic outright proves the judgment. The
-- simplest tactics, as shown below, are individual proof rules, expanding one
-- problem into its immediate subproblems. This is all that's required in a
-- type checker. In a general proof assistant, however, you would want to have
-- more general tactics that can do fancier things like apply as many basic
-- tactics as possible whenever there's no real choice to make. Tactics can
-- also fail, rather than simply succeed completely, hence we use `Maybe`.

type Tactic = HypJudgment -> Maybe ProofProblem





-- The hypothesis tactic looks to see if a variable is in scope at the
-- specified type. This corresponds to the inference rule
--
--   ---------------- hyp
--   Γ, x : A ⊢ x : A
--
-- Notice that, in the bottom-up direction, we have a proof problem that gets
-- broken down into no subproblems, so we return just the empty list. This
-- fails precisely when the i'th variable in the context is not a proof of the
-- judgment j.

hyp :: Tactic
hyp (HypJudgment ctx (Var i) j) | ctx !! i == j =
  return []
hyp _ = Nothing


-- Product introduction decomposes a pair into its two parts. This corresponds
-- to the inference rule
--
--   Γ ⊢ M : A    Γ ⊢ N : B
--   ---------------------- Prod-I
--     Γ ⊢ (M,N) : A × B

prodIntro :: Tactic
prodIntro (HypJudgment ctx (Pair m n) (IsTrue (Prod a b))) =
  return [ HypJudgment ctx m (IsTrue a)
         , HypJudgment ctx n (IsTrue b)
         ]
prodIntro _ = Nothing


-- Product elimination 1 decomposes a fst into checking its argument. This
-- corresponds to the inference rule
--
--   Γ ⊢ P : A × B
--   -- Prod-E-1
--   Γ ⊢ fst P : A
--
-- This tactic needs a type argument because, in the bottom-up direction, the
-- type B has to show up out of thin air. Nothing in the problem so far can
-- tell you what B should be. This can be dealt with by using unification with
-- bidirectionally-styled tactics.

prodElim1 :: Type -> Tactic
prodElim1 b (HypJudgment ctx (Fst p) (IsTrue a)) =
  return [ HypJudgment ctx p (IsTrue (Prod a b)) ]
prodElim1 _ _ = Nothing


-- Product elimination 2 does similar, but for the left type argument.

prodElim2 :: Type -> Tactic
prodElim2 a (HypJudgment ctx (Snd p) (IsTrue b)) =
  return [ HypJudgment ctx p (IsTrue (Prod a b)) ]
prodElim2 _ _ = Nothing



-- Function introduction decomposes a lambda into its body at the return type,
-- putting the argument type into the context for the variable bound by the
-- lambda.

funIntro :: Tactic
funIntro (HypJudgment ctx (Lam m) (IsTrue (Fun a b))) =
  return [ HypJudgment (IsTrue a:ctx) m (IsTrue b) ]
funIntro _ = Nothing


-- Function elimination decomposes an application into a check of the argument
-- at a function type, and the argument at the argument type. We need an extra
-- type argument b/c we only know the return value of the application.

funElim :: Type -> Tactic
funElim a (HypJudgment ctx (App f x) (IsTrue b)) =
  return [ HypJudgment ctx f (IsTrue (Fun a b))
         , HypJudgment ctx x (IsTrue a)
         ]
funElim _ _ = Nothing



-- Nat introduction 1 checks that a Zero is a Nat, succeeding immediately.

natIntro1 :: Tactic
natIntro1 (HypJudgment ctx Zero (IsTrue Nat)) =
  return []
natIntro1 _ = Nothing


-- Nat introduction 2 checks that a Successor is a Nat by decomposing it into
-- a check that the smaller number is in fact a Naturall number.

natIntro2 :: Tactic
natIntro2 (HypJudgment ctx (Suc m) (IsTrue Nat)) =
  return [ HypJudgment ctx m (IsTrue Nat) ]
natIntro2 _ = Nothing


-- Nat elimination is the fold on nats, the structural recursion principle.
-- We decompose it into sub-problems to check that the zero case is indeed an
-- appropriate value for the base case, and that the successor case is indeed
-- a recursive step case with a variable for the full recursive computation.
-- It also decomposes into a check that the number is in fact a Nat.

natElim :: Tactic
natElim (HypJudgment ctx (Rec z s m) (IsTrue c)) =
  return [ HypJudgment ctx z (IsTrue c)
         , HypJudgment (IsTrue c:ctx) s (IsTrue c)
         , HypJudgment ctx m (IsTrue Nat)
         ]
natElim _ = Nothing



-- Boolean introduction 1 succeeds immediately when the program is T.

boolIntro1 :: Tactic
boolIntro1 (HypJudgment ctx T (IsTrue Boolean)) =
  return []
boolIntro1 _ = Nothing


-- Boolean introduction 2 succeeds immediately when the program is F.

boolIntro2 :: Tactic
boolIntro2 (HypJudgment ctx F (IsTrue Boolean)) =
  return []
boolIntro2 _ = Nothing


-- Boolean elim is an If expression, so we decompose it into a subproblem to
-- check that the condition is a Boolean, and that the two clauses are the
-- type that we're checking against.

boolElim :: Tactic
boolElim (HypJudgment ctx (If b m n) (IsTrue c)) =
  return [ HypJudgment ctx b (IsTrue Boolean)
         , HypJudgment ctx m (IsTrue c)
         , HypJudgment ctx n (IsTrue c)
         ]
boolElim _ = Nothing





-- A tactical script is a stateful computation that will compute over some
-- proof problem, breaking down the first hypothetical judgment on the list.

type TacticScript = StateT ProofProblem Maybe ()


-- tac lifts a tactic into a script in the way described above.

tac :: Tactic -> TacticScript
tac t =
  do s <- get
     case s of
       [] -> fail "Already done."
       h:hs -> do
         hs' <- lift (t h)
         put (hs' ++ hs)



-- It would be lovely to be able to write this and then run it with all of the
-- tactics above, except with those extra arguments in the elims, we can't.
-- This is another reason to use a variant with unification.

tryAllRepeatedly :: [Tactic] -> TacticScript
tryAllRepeatedly ts =
  StateT $ \s ->
    case runStateT (sequence_ (map tac ts)) s of
      Nothing -> Just ((),s)
      Just ((),s') -> runStateT (tryAllRepeatedly ts) s'




main :: IO ()
main = do
  print $ runStateT proof [hj]
  where
    ctx :: Context
    ctx = []
    
    
    -- Let's try a tactical proof with the term   (\x.x) 0
    
    tm :: Term
    tm = App (Lam (Var 0)) Zero
    
    
    -- and we'll prove that it has the type Nat
    
    ty :: Type
    ty = Nat
    
    
    -- This is now our goal, corresponding to   ⊢ (\x.x) 0 : Nat
    
    hj :: HypJudgment
    hj = HypJudgment ctx tm (IsTrue ty)
    
    
    -- If you comment out the tactics, introducing them one at a time, top
    -- down, you can see the way the problem unfolds.
    
    proof :: StateT [HypJudgment] Maybe ()
    proof =
      do tac (funElim Nat)
         tac funIntro
         tac hyp
         tac natIntro1
         return ()
