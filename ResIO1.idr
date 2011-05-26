data ResTy = RTy Set;

-- Resource state is the current time slot, and a list mapping resouce id
-- to their current state.

ResState : Nat -> Set;
ResState n = (Nat & Vect ResTy n);

rty : ResTy -> Set;
rty (RTy t) = t;

-- a resource which is valid at a specific time at a specific location

data Resource : Nat -> Fin n -> ResTy -> Set where
    Res : {i:Fin n} -> rty a -> Resource t i a;

getResVal : {i:Fin n} -> Resource t i a -> rty a;
getResVal (Res v) = v;

using (xs:Vect ResTy n) {

  data ResEnv : Vect ResTy n -> Set where
      Empty  : ResEnv VNil
    | Extend : rty r -> ResEnv xs -> ResEnv (r :: xs);

  envLookup : (i:Fin n) -> ResEnv xs -> rty (vlookup i xs);
  envLookup fO (Extend t env) = t;
  envLookup (fS i) (Extend t env) = envLookup i env;

  update : (i:Fin n) -> A -> Vect A n -> Vect A n;
  update fO v (x :: xs) = v :: xs;
  update (fS i) v (x :: xs) = x :: (update i v xs);

  updateEnv : ResEnv xs ->
              (i:Fin n) -> rty a ->
              ResEnv (update i a xs);
  updateEnv (Extend t env) fO     val = Extend val env;
  updateEnv (Extend t env) (fS i) val = Extend t (updateEnv env i val);

}

Later : ResState n -> ResState n;
Later s = (S (fst s), snd s);

Later' : ResState n -> (i:Fin n) -> ResTy -> ResState n;
Later' s i a = (S (fst s), update i a (snd s));

data ResIO : Set -> ResState n -> ResState n -> Set where
  ResIOp : {s:ResState n} -> {s':ResState n} ->
           (ResEnv (snd s) -> IO (a & ResEnv (snd s'))) -> ResIO a s s';
 
getResAction : {n:Nat} -> {s:ResState n} -> {s':ResState n} ->
               ResIO a s s' -> (ResEnv (snd s) -> IO (a & ResEnv (snd s')));
getResAction {n} {s} {s'} (ResIOp f) = f;

using (s:ResState n, s':ResState n) {

BIND : ResIO t s s' -> (t -> ResIO u s' s'') -> ResIO u s s'';
BIND {n} {t} {s} {s'} (ResIOp c) k = 
     ResIOp (\env => do { cenv' <- c env;
                          getResAction (k (fst cenv')) (snd cenv');
                                    });

RETURN : a -> ResIO a s s;
RETURN x = ResIOp (\env => return (x, env));

GET : (i:Fin n) -> ResIO (Resource (fst s) i (vlookup i (snd s))) s s;
GET i = ResIOp (\env => return (Res (envLookup i env), env));

PUT : (i:Fin n) -> rty a ->
      ResIO () s (Later' s i a);
PUT i val = ResIOp (\env => return (II, updateEnv env i val));

CREATE : (i:Fin n) -> |(action:IO (rty a)) ->
         ResIO (rty a) s (Later' s i a);
CREATE i ival = ResIOp (\env => do { val <- ival;
                                     return (val, updateEnv env i val); });

LIFT : |(action:IO a) -> ResIO a s s;
LIFT action = ResIOp (\env => do { v <- action; return (v, env); });

rread : {i:Fin n} -> Resource (fst s) i (RTy File) -> ResIO String s s;
rread r = ResIOp (\env => do { str <- fread (getResVal r);
                               return (str, env); });

ropen : String -> (i:Fin n) -> ResIO File s (Later' s i (RTy File));
ropen fname i = CREATE i (fopen fname "r");

rclose : {i:Fin n} ->
         Resource (fst s) i (RTy File) -> 
         ResIO () s (Later' s i (RTy ())); 
rclose {i} r = CREATE i (fclose (getResVal r));

data ResProg : Set -> Vect ResTy n -> Set where
   RP : {xs':Vect ResTy n} -> {xs:Vect ResTy n} ->
        ResIO a (O,xs) (t,xs') -> ResProg a xs;

run : {xs:Vect ResTy n} -> ResEnv xs -> ResProg a xs -> IO a;
run env (RP (ResIOp f)) = do { cenv' <- f env;
                               return (fst cenv'); };

}

rlist = RTy () :: RTy () :: RTy () :: VNil;

do using (BIND, RETURN) {

  oc : ResProg () rlist;
  oc = RP do { ropen "Test" fO;
               h <- GET fO;
               str <- rread h;
               LIFT (putStrLn str);
               str <- rread h;
               LIFT (putStrLn str);
               str <- rread h;
               LIFT (putStrLn str);
               rclose h;
             };

}

main = run (Extend II (Extend II (Extend II Empty))) oc;
