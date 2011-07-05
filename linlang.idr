{-- A language (unfinished) for describing linear operations --}

infixr 5 :->;

data LTy = TyVal Set
         | TyRes Set
         | TyReadRes Set
         | TyIO LTy
         | (:->) LTy LTy;

data Resource a = MkRes a;

using (gam : Vect LTy n) {

  data Res : Vect LTy n -> LTy -> Set;

  interpTy : LTy -> Set;
  interpTy (TyVal T) = T;
  interpTy (TyRes T) = T;
  interpTy (TyReadRes T) = T;
  interpTy (TyIO T) = IO (interpTy T);
  interpTy (A :-> T) = interpTy A -> interpTy T;

  interpIO : LTy -> Set;
  interpIO (TyVal T) = IO T;
  interpIO (TyRes T) = IO T;
  interpIO (TyReadRes T) = IO T;
  interpIO (A :-> T) = interpTy A -> interpIO T;

  data AEnv : Vect LTy n -> List LTy -> Set where
      ANil  : AEnv gam Nil
    | ACons : {as:List LTy} -> {A:LTy} ->
              Res gam A -> AEnv gam as -> AEnv gam (Cons A as);

  mkFun : List LTy -> LTy -> Set;
  mkFun Nil T = interpTy T;
  mkFun (Cons a as) T = interpTy a -> mkFun as T;

  mkTyFun : List LTy -> LTy -> LTy;
  mkTyFun Nil T = T;
  mkTyFun (Cons a as) T = a :-> mkTyFun as T;

  data [noElim] Res : Vect LTy n -> LTy -> Set where
      V    : (i:Fin n) -> Res gam (vlookup i gam)
    | I    : a -> Res gam (TyVal a)
    | Lam  : Res (A :: gam) T -> Res gam (A :-> T)
    | Bind : Res gam (TyIO A) -> Res gam (A :-> (TyIO T)) -> Res gam (TyIO T)
    | App  : Res gam (A :-> T) -> Res gam A -> Res gam T
    | Read : Res gam (TyRes A) -> Res gam (TyReadRes A)
    | Prim : (argTys : List LTy) ->
             (interpTy (mkTyFun argTys T)) ->
             Res gam (mkTyFun argTys T);


  data Env : Vect LTy n -> Set where
     Empty : Env VNil
   | Extend : interpTy a -> Env gam -> Env (a :: gam);

  envLookup : (i:Fin n) -> Env gam -> interpTy (vlookup i gam);
  envLookup fO (Extend x xs) = x;
  envLookup (fS k) (Extend x xs) = envLookup k xs;

  interp : Env gam -> Res gam T -> interpTy T;
  interp env (V i) = envLookup i env;
  interp env (I a) = a;
  interp env (Lam e) = \x => interp (Extend x env) e;
  interp env (Lam e) = \x => interp (Extend x env) e;
  interp env (Bind val e) = do {
                              val' <- interp env val;
                              interp env e val';
                            };
  interp env (App f a) = interp env f (interp env a);
  interp env (Read a) = let a' = interp env a in a'; -- ????
  interp env (Prim args fn) = fn;

  run : Res VNil (TyIO T) -> IO (interpTy T);
  run prog = interp Empty prog;

}

syntax RIO x = #({gam:Vect LTy n} -> Res gam (TyIO (TyVal x)));
syntax RIOres x = #({gam:Vect LTy n} -> Res gam (TyIO (TyRes x)));
syntax RVal x = #({gam:Vect LTy n} -> Res gam x);
syntax RArg x = Res gam x;

lopen' : RVal (TyVal String :-> TyVal String :-> TyIO (TyRes File));
lopen' = Prim [TyVal String, TyVal String] fopen;

lopen : RArg (TyVal String) -> RArg (TyVal String) -> RIOres File;
lopen fn mode = App (App lopen' fn) mode;

lread' : RVal (TyReadRes File :-> TyIO (TyVal String));
lread' = Prim [TyReadRes File] fread;

lread : RArg (TyRes File) -> RIO String;
lread h = App lread' (Read h);

lclose' : RVal (TyRes File :-> TyIO (TyVal ()));
lclose' = Prim [TyRes File] fclose;

lclose : RArg (TyRes File) -> RIO ();
lclose h = App lclose' h;

print : RArg (TyVal String) -> RIO ();
print str = App (Prim [TyVal String] putStrLn) str;

dsl (V, Lam) {
  do using (Bind, I) {

    prog : RIO ();
    prog = do { h <- lopen (I "Test") (I "r");
                str <- lread h;
                print str;
                lclose h;
              };

  }
} 

main = run prog;

