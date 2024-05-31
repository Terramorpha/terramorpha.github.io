{-# LANGUAGE DataKinds #-}

{-# LANGUAGE TypeFamilies #-}

{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE QuantifiedConstraints #-}

{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

import GHC.Exts (Constraint)

data Fix f = In (f (Fix f))

data Plus s = -- s for self. This is the point of recursion
  Plus s s
  deriving (Functor, Show)

data Free f x = Return x | Join (f (Free f x))
  deriving Functor

data Sum (fs :: [* -> *]) (x :: *) where
  Head :: f x -> Sum (f ': fs) x
  Tail :: Sum fs x -> Sum  (f ': fs) x

class (e :: * -> *) :∈: (es :: [* -> *]) where
  inject :: e x -> Sum es x

instance {-# OVERLAPPING #-} f :∈: (f ': fs) where
  inject = Head

instance f :∈: fs => f :∈: (g':fs) where
  inject = Tail . inject

data A s = A s
data B s = B s

test1 :: Sum '[A, B] Int
test1 = inject $ B 12

class (l :: [* -> *]) :⊆: (r :: [* -> *]) where
  permute :: Sum l x -> Sum r x

instance '[] :⊆: fs where
  -- no constructors for Sum '[] x
  permute _ = error "impossible"

instance (f :∈: gs, fs :⊆: gs) => (f ': fs) :⊆: gs where
  permute (Head h) = inject h
  permute (Tail t) = permute t

data C s = C s

test2 :: Sum '[B, C, A] Int
test2 = permute test1

data Eff (fs :: [* -> *]) (x :: *) where
  Pure :: x -> Eff fs x
  Impure :: Sum fs (Eff fs x) -> Eff fs x

-- To unwrapp empty effects into pure values
unwrapEff :: Eff '[] x -> x
unwrapEff (Impure _) = error "impossible"
unwrapEff (Pure x) = x

class (forall x. Show x => Show (f x)) => PreservesShow f

type family AllPreserveShow (fs :: [* -> *]) :: Constraint where
  AllPreserveShow (f ': fs) = (PreservesShow f, AllPreserveShow fs)
  AllPreserveShow '[] = ()

instance (AllPreserveShow fs, Show x) => Show (Sum fs x) where
  show (Head h) = show h
  show (Tail t) = show t

instance (AllPreserveShow fs, Show x) => Show (Eff fs x) where
  show (Pure x) = show x
  show (Impure t) = show t

type family AllFunctors (fs :: [* -> *]) :: Constraint where
  AllFunctors (f ': fs) = (Functor f, AllFunctors fs)
  AllFunctors '[] = ()

instance AllFunctors fs => Functor (Sum fs) where
  fmap f (Head h) = Head $ fmap f h
  fmap f (Tail t) = Tail $ fmap f t

instance AllFunctors fs => Functor (Eff fs) where
  fmap f (Pure x) = Pure $ f x
  fmap f (Impure fx) = Impure $ (fmap . fmap) f fx

effJoin :: AllFunctors fs => Eff fs (Eff fs x) -> Eff fs x
effJoin (Pure x) = x
effJoin (Impure fx) = Impure $ (fmap effJoin) fx

effBind :: AllFunctors fs => Eff fs x -> (x -> Eff fs y) -> Eff fs y
effBind fx f = effJoin $ fmap f fx

instance (AllFunctors fs) => Applicative (Eff fs) where
  pure = Pure
  ff <*> fx = effBind ff (\f -> fmap f fx)

instance (AllFunctors fs) => Monad (Eff fs) where
  (>>=) = effBind

effInj :: (AllFunctors fs, f :∈: fs) => f x -> Eff fs x
effInj e = Impure $ fmap Pure $ inject e

data GetString a = GetString (String -> a)
  deriving Functor

data GetInt a = GetInt (Int -> a)
  deriving Functor

type MyEff = [GetString, GetInt]

comp :: Eff MyEff String
comp = do
  int <- effInj $ GetInt id
  str <- effInj $ GetString id
  return $ str ++ show int

effPerm :: forall fs gs x. (AllFunctors fs, fs :⊆: gs) => Eff fs x -> Eff gs x
effPerm (Pure x) = Pure x
effPerm (Impure sx) = Impure $ permute @fs @gs $ fmap (effPerm @fs @gs) sx

handle :: forall fs g gs x. (Functor g, AllFunctors gs, AllFunctors fs,fs :⊆: (g ': gs))
  => (forall x. g x -> Eff gs x) -> Eff fs x -> Eff gs x
handle trans (Pure x) = (Pure x)
handle trans (Impure x) = case permute @fs @(g ': gs) x of
  Head h -> let val = fmap (handle trans) h
                val' = trans val
            in effJoin val'
  Tail t -> let val = fmap (handle @fs @g @gs trans) t
            in Impure val

comp' :: Eff '[GetString] String
comp' = handle func comp
  where func :: GetInt x -> Eff '[GetString] x
        func (GetInt f) = return $ f 0

data Handler (f :: * -> *) (fs :: [* -> *]) where
  Handler :: (forall x. f x -> Eff fs (x, Handler f fs)) -> Handler f fs

handleFold :: forall fs g gs x. (Functor g, AllFunctors gs, AllFunctors fs,fs :⊆: (g ': gs))
  => Handler g gs -> Eff fs x -> Eff gs x
handleFold _ (Pure x) = Pure x
handleFold (Handler fold) (Impure x) = case permute @fs @(g ': gs) x of
  Tail t -> Impure $ fmap (handleFold (Handler fold)) t
  Head h -> do
    (val, fold') <- fold h
    handleFold fold' val

data GenSym x = GenSym (Int -> x)
  deriving Functor

syms :: Eff '[GenSym] [Int]
syms = do
  x <- effInj $ GenSym id
  y <- effInj $ GenSym id
  z <- effInj $ GenSym id
  return [x, y, z+1]

symsEvaled :: Eff '[] [Int]
symsEvaled = handleFold (fh 0) syms
  where fh :: Int -> Handler GenSym '[]
        fh k = Handler $ \(GenSym cont) -> return $ (cont k, fh (k+1))
