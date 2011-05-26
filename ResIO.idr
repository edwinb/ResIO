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

-- IO operations which can only be run in a resource computation
data IOr : Set -> Set where
    MkIOr : IO a -> IOr a;

getIOr : IOr a -> IO a;
getIOr (MkIOr x) = x;

ior : IO a -> IOr a;
ior = MkIOr;

getResource : {i:Fin n} -> Resource t i a -> rty a;
getResource (Res v) = v;

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
               ResIO a s s' -> ResEnv (snd s) -> IO (a & ResEnv (snd s'));
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

PUT : {i:Fin n} -> 
      Resource (fst s) i (RTy a) -> 
      rty b ->
      ResIO () s (Later' s i b);
PUT {i} res val = ResIOp (\env => return (II, updateEnv env i val));

CREATE : (i:Fin n) -> 
         |(action:IOr (rty a)) ->
         ResIO (rty a) s (Later' s i a);
CREATE i ival
    = ResIOp (\env => do { val <- getIOr ival;
                           return (val, updateEnv env i val); });

UPDATE : {i:Fin n} -> 
         |(action:IOr (rty a)) ->
         Resource (fst s) i b -> 
         ResIO (rty a) s (Later' s i a);
UPDATE {i} ival res
    = ResIOp (\env => do { val <- getIOr ival;
                           return (val, updateEnv env i val); });

USE : {i:Fin n} -> 
      (rty a -> IOr b) ->
      Resource (fst s) i a -> 
      ResIO b s s;
USE {i} f res = ResIOp (\env => do { v <- getIOr (f (getResource res));
                                     return (v, env); });

SET_TIMER : (time:Nat) -> ResIO b s t -> ResIO b s (time, snd t);
SET_TIMER {t} time (ResIOp {s'=t} prog) = ResIOp {s'=(time, snd t)} prog;

do using (BIND, RETURN) {

CHECK : {i:Fin n} -> {xs':Vect ResTy n} ->
        Resource (fst s) i (RTy (Either a b)) ->
        ResIO c (Later' s i (RTy a)) (t1, xs') ->
        ResIO c (Later' s i (RTy b)) (t2, xs') ->
        ResIO c s (max t1 t2, xs');
CHECK {n} {i} {t1} {t2} res left right =
   either (getResource res)
       (\lv => SET_TIMER (max t1 t2) do { PUT res lv; left; })
       (\rv => SET_TIMER (max t1 t2) do { PUT res rv; right; });

}

LIFT : |(action:IO a) -> ResIO a s s;
LIFT action = ResIOp (\env => do { v <- action; return (v, env); });

syntax ResSub t u = #(Resource O (fO {k=O}) (RTy t) ->
                      ResIO u (O, RTy t :: VNil) (O, RTy t :: VNil));

syntax MK_USE x y = #({n:Nat} -> {s:ResState n} -> {i:Fin n} -> 
                      Resource (fst s) i (RTy x) -> ResIO y s s);

syntax MK_CREATE y = #({n:Nat} -> {s:ResState n} -> 
                       (i:Fin n) -> ResIO y s (Later' s i (RTy y)));

syntax MK_UPDATE x y = #({n:Nat} -> {s:ResState n} -> {i:Fin n} -> 
                         Resource (fst s) i (RTy x) ->
                         ResIO y s (Later' s i (RTy y)));

-- an initial empty vector of n resources
clear : (n:Nat) -> Vect ResTy n;
clear O = VNil;
clear (S k) = RTy () :: clear k;

data ResProg : Set -> Set where
   RP : {xs':Vect ResTy n} -> 
        ResIO a (O,clear n) (t,xs') -> ResProg a;

clearEnv : (n:Nat) -> ResEnv (clear n);
clearEnv O = Empty;
clearEnv (S k) = Extend II (clearEnv k);

run : ResProg a -> IO a;
run (RP {n} (ResIOp f)) = do { cenv' <- f (clearEnv n);
                               return (fst cenv'); };

resources = intToNat;

}

-- call_action is a workaround for a typechecker bug. Really need to rewrite
-- the thing - maybe a problem with the normaliser?

call_action : ResIO u (O, (RTy t :: VNil)) (O, (RTy t :: VNil)) -> 
              t -> IO (u & ResEnv (RTy t :: VNil));
call_action (ResIOp pval) rval = pval (Extend rval Empty);

CALL : {n:Nat} -> {i:Fin n} ->
       {s:ResState n} -> {t:Set} -> {u:Set} ->
       (Resource O (fO {k=O}) (RTy t) ->
                      ResIO u (O, RTy t :: VNil) (O, RTy t :: VNil)) ->
       Resource (fst s) i (RTy t) ->
       ResIO u s s;
CALL {n} {t} {u} {s} {i} p res = 
     let rval = getResource res in
     let pval = p (Res rval) in
     -- let act  = action in -- getResAction pval ? in
     ResIOp (\env => do { v <- call_action pval rval;
                          return (fst v, env); });

%hide MkIOr;

