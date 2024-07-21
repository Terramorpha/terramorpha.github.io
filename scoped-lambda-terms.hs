data Var a = Z | S a
  deriving (Show, Functor)

data Term a = V a         -- Variable references
  | Abs (Term (Var a))    -- λ abstraction
  | App (Term a) (Term a) -- Function application
  deriving (Show, Functor)

data ABC = A | B | C

t :: Term ABC
t = App (V A) (V B)

type ABCZ = Var ABC

fresh :: ABCZ
fresh = Z -- The new variable added by `Var`.

rename :: (a -> b) -> Term a -> Term b
rename = fmap

sub :: (v1 -> Term v2) -> Term v1 -> Term v2

sub s (V ref) = s ref
sub s (App a b) = App (sub s a) (sub s b)

sub s (Abs body) = Abs (sub (shiftSub s) body)

shiftSub :: (a -> Term b) -> Var a -> Term (Var b)
-- If this variable is bound by the `Abs`, we must not touch it
shiftSub f Z = V Z
-- If it is not, we must compute its replacement and shift it.
shiftSub f (S r) = rename S (f r)

-- Example

data Null
  deriving Show

body :: Term (Var Null)
body = (App (V Z) (V Z))

func :: Term Null
func = Abs body

x = sub (const func) body

termRet :: a -> Term a
termRet = V

data Semiring v = Zero
  | One
  | Add (Semiring v) (Semiring v)
  | Mul (Semiring v) (Semiring v)
  | Sref v
  deriving (Functor)

srSub :: (v1 -> Semiring v2) -> Semiring v1 -> Semiring v2
srSub f Zero = Zero
srSub f One = One
srSub f (Add a b) = Add (srSub f a) (srSub f b)
srSub f (Mul a b) = Mul (srSub f a) (srSub f b)
srSub f (Sref v) = f v
