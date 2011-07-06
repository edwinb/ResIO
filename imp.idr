
update : (i:Fin n) -> a -> Vect a n -> Vect a n;
update fO     y (x :: xs) = y :: xs;
update (fS k) y (x :: xs) = x :: update k y xs;

using (gam : Vect Set n, gam' : Vect Set n, gam'' : Vect Set n) {

  infixl 5 := ;

  data [noElim] Imp : Vect Set n -> Vect Set n' -> Set -> Set where
       Let  : A -> Imp (A :: gam) (B :: gam') T -> Imp gam gam' T
     | (:=) : (i:Fin n) -> B -> Imp gam (update i B gam) ()
     | Read : (i:Fin n) -> Imp gam gam (vlookup i gam)
     | Return : A -> Imp gam gam A
     | Bind : Imp gam gam' A -> (A -> Imp gam' gam'' T) -> 
              Imp gam gam''  T;

}

dsl imp {
   bind = Bind
   return = Return
   variable = id
   let = Let
}

testprog : {gam:Vect Set n} -> Imp gam gam String;
testprog = imp do { let x = 4;
                    x' <- Read x;
                    x := showInt x';
                    x' <- Read x; 
                    return (x' ++ "!");
                  };

