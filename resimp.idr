
-- IO operations which read a resource
data Reader : Set -> Set where
    MkReader : IO a -> Reader a;

getReader : Reader a -> IO a;
getReader (MkReader x) = x;

ior : IO a -> Reader a;
ior = MkReader;

-- IO operations which update a resource
data Updater : Set -> Set where
    MkUpdater : IO a -> Updater a;

getUpdater : Updater a -> IO a;
getUpdater (MkUpdater x) = x;

iou : IO a -> Updater a;
iou = MkUpdater;

-- IO operations which create a resource
data Creator : Set -> Set where
    MkCreator : IO a -> Creator a;

getCreator : Creator a -> IO a;
getCreator (MkCreator x) = x;

ioc : IO a -> Creator a;
ioc = MkCreator;

using (i: Fin n, gam : Vect Set n, gam' : Vect Set n, gam'' : Vect Set n) {

  infixl 5 :. ;

  data HasType : Vect Set n -> Fin n -> Set -> Set where
       stop : HasType (a :: gam) fO a
     | pop  : HasType gam i b -> HasType (a :: gam) (fS i) b;

  update : (gam : Vect Set n) -> HasType gam i b -> Set -> Vect Set n;
  update (x :: xs) stop    y = y :: xs;
  update (x :: xs) (pop k) y = x :: update xs k y;

  data [noElim] Res : Vect Set n -> Vect Set n' -> Set -> Set where

{-- Resource creation and usage. 'Let' creates a resource - the type
    at the end means that the resource must have been consumed by the time
    it goes out of scope, where "consumed" simply means that it has been
    replaced with a value of type '()'. --}

       Let    : Creator A -> Res (A :: gam) (() :: gam') T -> Res gam gam' T
     | Update : (A -> Updater B) -> (p:HasType gam i A) -> 
                Res gam (update gam p B) ()
     | Use    : (A -> Reader B) -> HasType gam i A -> 
                Res gam gam B

{-- Control structures --}

     | Lift   : |(action:IO a) -> Res gam gam a
     | Check  : (p:HasType gam i (Either A B)) -> 
                (failure:Res (update gam p A) (update gam p C) T) ->
                (success:Res (update gam p B) (update gam p C) T) ->
                Res gam (update gam p C) T
     | While  : Res gam gam Bool -> Res gam gam () -> Res gam gam ()
     | Return : A -> Res gam gam A
     | Bind   : Res gam gam'  A -> (A -> Res gam' gam'' T) -> 
                Res gam gam'' T;

  data Env : Vect Set n -> Set where
       Empty : Env VNil
     | Extend : a -> Env gam -> Env (a :: gam);
  
  envLookup : HasType gam i A -> Env gam -> A;
  envLookup stop    (Extend x xs) = x;
  envLookup (pop k) (Extend x xs) = envLookup k xs;

  envUpdate : (p:HasType gam i a) -> (val:b) -> 
              Env gam -> Env (update gam p b);
  envUpdate stop    val (Extend x xs) = Extend val xs;
  envUpdate (pop k) val (Extend x xs) = Extend x (envUpdate k val xs);

  envTail : Env (a :: gam) -> Env gam;
  envTail (Extend x xs) = xs;

  interp : Env gam -> Res gam gam' t -> IO (t & Env gam');
  interp env (Let val scope) 
     = do { x <- getCreator val;
            tenv <- interp (Extend x env) scope;
            return (fst tenv, envTail (snd tenv));
          };
  interp env (Update method x) 
     = do { x' <- getUpdater (method (envLookup x env));
            return (II, envUpdate x x' env);
          };
  interp env (Use method x) 
     = do { x' <- getReader (method (envLookup x env));
            return (x', env); 
          };
  interp env (Lift io) = do { v <- io;
                              return (v, env); };
  interp env (Check x left right) with envLookup x env {
      | Left a  = interp (envUpdate x a env) left;
      | Right b = interp (envUpdate x b env) right;
  }
  interp env (While test body) 
     = do { tenv <- interp env test;
            if (not (fst tenv)) 
               then (return (II, snd tenv))
               else (do { benv <- interp (snd tenv) body;
                          interp (snd benv) (While test body); });
          };
  interp env (Return v) = return (v, env);
  interp env (Bind v k) 
     = do { venv <- interp env v;
            interp (snd venv) (k (fst venv)); 
          };

  run : Res VNil VNil t -> IO t;
  run prog = do { v <- interp Empty prog;
                  return (fst v); };

}

dsl res {
   bind = Bind
   return = Return
   variable = id
   let = Let
   index_first = stop
   index_next = pop
}

syntax RES x = #( {gam:Vect Set n} -> Res gam gam x );

