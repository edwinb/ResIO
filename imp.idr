using (gam : Vect Set n, gam' : Vect Set n, gam'' : Vect Set n) {

  infixl 5 := ;

  data HasType : Vect Set n -> Fin n -> Set -> Set where
       stop : HasType (a :: gam) fO a
     | pop  : HasType gam i b -> HasType (a :: gam) (fS i) b;

  update : (gam : Vect Set n) -> HasType gam i b -> Set -> Vect Set n;
  update (x :: xs) stop    y = y :: xs;
  update (x :: xs) (pop k) y = x :: update xs k y;

  data [noElim] Imp : Vect Set n -> Vect Set n' -> Set -> Set where
       Let  : A -> Imp (A :: gam) (B :: gam') T -> Imp gam gam' T
     | (:=) : (p:HasType gam i A) -> B -> Imp gam (update gam p B) ()
     | Read : HasType gam i A -> Imp gam gam A
     | While : Imp gam gam Bool -> Imp gam gam () -> Imp gam gam ()
     | Return : A -> Imp gam gam A
     | Bind : Imp gam gam' A -> (A -> Imp gam' gam'' T) -> 
              Imp gam gam''  T;

  data Env : Vect Set n -> Set where
     Empty : Env VNil
   | Extend : a -> Env gam -> Env (a :: gam);

  envLookup : HasType gam i A -> Env gam -> A;
  envLookup stop    (Extend x xs) = x;
  envLookup (pop k) (Extend x xs) = envLookup k xs;

  envUpdate : (p:HasType gam i A) -> (val:B) -> 
              Env gam -> Env (update gam p B);
  envUpdate stop    val (Extend x xs) = Extend val xs;
  envUpdate (pop k) val (Extend x xs) = Extend x (envUpdate k val xs);

  envTail : Env (a :: gam) -> Env gam;
  envTail (Extend x xs) = xs;

  interp : Env gam -> Imp gam gam' t -> (t & Env gam');
  interp env (Let val scope) = let x = val in 
                               let tenv = interp (Extend x env) scope in
                               (fst tenv, envTail (snd tenv));
  interp env (x := val) = (II, envUpdate x val env);
  interp env (Read x) = (envLookup x env, env);
  interp env (While test body) 
      = let tenv = interp env test in
            if (not (fst tenv)) 
               then (II, snd tenv)
               else (let benv = interp (snd tenv) body in
                         interp (snd benv) (While test body));
  interp env (Return v) = (v, env);
  interp env (Bind v k) = let venv = interp env v in
                          interp (snd venv) (k (fst venv));

  run : Imp VNil VNil t -> t;
  run prog = fst (interp Empty prog);

}

dsl imp {
   bind = Bind
   return = Return
   variable = id
   let = Let
   index_first = stop
   index_next = pop
}

syntax IMP x = #( {gam:Vect Set n} -> Imp gam gam x );

testprog : Int -> IMP String;
testprog val 
    = imp do { let x = val;
               x' <- Read x;
               let y = val * 2;
               y' <- Read y;
               x := showInt (x' + y');
               x' <- Read x; 
               return (x' ++ "!");
            };

testwhile : Int -> IMP String;
testwhile val
  = imp do { let counter = val;
             let rstring = "";
             While (do { c' <- Read counter;
                         return (c' > 0); })
                   (do { c' <- Read counter;
                         counter := c' - 1;
                         r <- Read rstring;
                         rstring := r ++ "Count: " ++ showInt c' ++ "\n";
                       });
             r <- Read rstring;
             return r; 
           };

main = putStrLn (run (testwhile 5));