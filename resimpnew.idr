module resimp

-- IO operations which read a resource
data Reader : Set -> Set where
    MkReader : IO a -> Reader a

getReader : Reader a -> IO a
getReader (MkReader x) = x

ior : IO a -> Reader a
ior = MkReader

-- IO operations which update a resource
data Updater : Set -> Set where
    MkUpdater : IO a -> Updater a

getUpdater : Updater a -> IO a
getUpdater (MkUpdater x) = x

iou : IO a -> Updater a
iou = MkUpdater

-- IO operations which create a resource
data Creator : Set -> Set where
    MkCreator : IO a -> Creator a

getCreator : Creator a -> IO a
getCreator (MkCreator x) = x

ioc : IO a -> Creator a
ioc = MkCreator
  
infixr 5 :->

using (i: Fin n, gam : Vect Ty n, gam' : Vect Ty n, gam'' : Vect Ty n)

  data Ty = R Set
          | Val Set
          | Choice Set Set
          | (:->) Set Ty

  interpTy : Ty -> Set
  interpTy (R t) = IO t
  interpTy (Val t) = t
  interpTy (Choice x y) = Either x y
  interpTy (a :-> b) = a -> interpTy b

  data HasType : Vect Ty n -> Fin n -> Ty -> Set where
       stop : HasType (a :: gam) fO a
       pop  : HasType gam i b -> HasType (a :: gam) (fS i) b

  data Env : Vect Ty n -> Set where
       Nil : Env Nil
       (::) : interpTy a -> Env gam -> Env (a :: gam)

  envLookup : HasType gam i a -> Env gam -> interpTy a
  envLookup stop    (x :: xs) = x
  envLookup (pop k) (x :: xs) = envLookup k xs

  update : (gam : Vect Ty n) -> HasType gam i b -> Ty -> Vect Ty n
  update (x :: xs) stop    y = y :: xs
  update (x :: xs) (pop k) y = x :: update xs k y

  envUpdate : (p:HasType gam i a) -> (val:interpTy b) -> 
              Env gam -> Env (update gam p b)
  envUpdate stop    val (x :: xs) = val :: xs
  envUpdate (pop k) val (x :: xs) = x :: envUpdate k val xs

  envTail : Env (a :: gam) -> Env gam
  envTail (x :: xs) = xs

  data Args  : Vect Ty n -> List Set -> Set where
       ANil  : Args gam []
       ACons : HasType gam i a -> 
               Args gam as -> Args gam (interpTy a :: as)

  funTy : List Set -> Ty -> Ty
  funTy list.Nil t = t
  funTy (a :: as) t = a :-> funTy as t

--   applyArgs : {as : List Set} ->
--               Env gam -> interpTy (funTy as t) -> Args gam as -> interpTy t
-- --   applyArgs env f ANil  = f
--   applyArgs env f (ACons x xs) = ?appArgs --applyArgs env (f (envLookup x env)) xs

  data Res : Vect Ty n -> Vect Ty n -> Ty -> Set where

{-- Resource creation and usage. 'Let' creates a resource - the type
    at the end means that the resource must have been consumed by the time
    it goes out of scope, where "consumed" simply means that it has been
    replaced with a value of type '()'. --}

       Let    : Creator (interpTy a) -> 
                Res (a :: gam) (Val () :: gam') (R t) -> 
                Res gam gam' (R t)
       Update : (a -> Updater b) -> (p:HasType gam i (Val a)) -> 
                Res gam (update gam p (Val b)) (R ())
       Use    : (a -> Reader b) -> HasType gam i (Val a) -> 
                Res gam gam (R b)

{-- Control structures --}

       Lift   : IO a -> Res gam gam (R a)
       Check  : (p:HasType gam i (Choice (interpTy a) (interpTy b))) -> 
                (failure:Res (update gam p a) (update gam p c) T) ->
                (success:Res (update gam p b) (update gam p c) T) ->
                Res gam (update gam p c) T
       While  : Res gam gam (R Bool) -> 
                Res gam gam (R ()) -> Res gam gam (R ())
       Return : a -> Res gam gam (R a)
       (>>=)  : Res gam gam'  (R a) -> (a -> Res gam' gam'' (R t)) -> 
                Res gam gam'' (R t)


  interp : Env gam -> Res gam gam' t -> 
           (Env gam' -> interpTy t -> IO u) -> IO u

  interp env (Let val scope) k
     = do x <- getCreator val;
          interp (x :: env) scope
                   (\env', scope' => k (envTail env') scope')
  interp env (Update method x) k
      = do x' <- getUpdater (method (envLookup x env))
           k (envUpdate x x' env) (return ())
  interp env (Use method x) k
      = do x' <- getReader (method (envLookup x env))
           k env (return x')
  interp env (Lift io) k 
     = k env io
  interp env (Check x left right) k =
     either (envLookup x env) 
            (\a => interp (envUpdate x a env) left k)
            (\b => interp (envUpdate x b env) right k)
  interp env (While test body) k
     = interp env test
          (\env', result =>
             do r <- result;
                if (not r) 
                   then (k env' (return ()))
                   else (interp env' body 
                        (\env'', body' => 
                           do v <- body' -- make sure it's evalled
                              interp env'' (While test body) k ))
                )
  interp env (Return v) k = k env (return v)
  interp env (v >>= f) k
     = interp env v (\env', v' => do n <- v'
                                     interp env' (f n) k)

  run : Res [] [] (R t) -> IO t
  run prog = interp [] prog (\env, res => res)

dsl res
   variable = id
   let = Let
   index_first = stop
   index_next = pop

syntax RES [x] = {gam:Vect Ty n} -> Res gam gam (R x)

