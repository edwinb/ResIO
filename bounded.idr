include "so_what.idr";

-- Idris doesn't have unsigned integers, which would make this easier. 
-- We assume here that Int just means unsigned.
-- TODO: Add Unsigned ints (call it 'Word'?)

Unsigned = Int; -- HACK :)

data Bounded : Int -> Set where
     BInt : (x:Unsigned) -> (so (x<i)) -> Bounded i;

syntax bounded x = BInt x [ tryproof %intro; %decide isThatSo; %qed ];

value : Bounded i -> Unsigned; [inline]
value (BInt v _) = v;

boundProof : (b:Bounded i) -> so ((value b) < i);
boundProof (BInt _ p) = p;

charToBounded : Char -> Bounded 256;
charToBounded x = BInt (__charToInt x) (__Prove_Anything _ _ oh); -- Of course it is ;)

Word : Unsigned -> Set;
Word n = Bounded (1 << n);

infixl 8 :+: ;
infixl 6 :<:, :<=:, :>:, :>=: ;

-- modulo addition

mod_bound : Unsigned -> Bounded n;
mod_bound {n} x = BInt (mod x n) (__Prove_Anything _ _ oh); -- guaranteed by %

(:+:) : Bounded n -> Bounded n -> Bounded n;
(:+:) x y = mod_bound (value x + value y);

blift : (Unsigned -> Unsigned -> Bool) -> Bounded n -> Bounded m -> Bool;
blift op x y = op (value x) (value y);

(:<:) : Bounded n -> Bounded m -> Bool;
(:<:) = blift (<) ;

(:<=:) : Bounded n -> Bounded m -> Bool;
(:<=:) = blift (<=) ;

(:>:) : Bounded n -> Bounded m -> Bool;
(:>:) = blift (>) ;

(:>=:) : Bounded n -> Bounded m -> Bool;
(:>=:) = blift (>=) ;

data Window : (seq_width:Unsigned) -> Set where
   MkWin : Word n -> Word n -> Window n;

using (bottom: Word n, top : Word n, x : Word n) {

  data InWindow : Word n -> Window n -> Set where
     InNormal :  (so (bottom :<: top)) -> -- no wrap around
                 (so (x :>: bottom && x :<=: top)) ->
                 (InWindow x (MkWin bottom top))
   | InWrapped : (so (bottom :>=: top)) -> -- must have wrapped
                 (so (x :<=: top || x :>: bottom)) ->
                 (InWindow x (MkWin bottom top));
}

advance : (old: Window n) -> (last_ack : Word n) -> (win_size : Word n) ->
          InWindow last_ack old -> Window n;
advance (MkWin bottom top) last_ack win_size p
   = MkWin (last_ack :+: BInt 1 ?adv1) (last_ack :+: BInt 1 ?adv2 :+: win_size);

{-- some cheating is required again because we don't have unsigned ints!
    These are okay under the assumption that we never use a negative n in 
    Word n and Window n --}

adv1 proof {
	%intro;
	%fill (__Prove_Anything _ _ oh);
	%qed;
};

adv2 proof {
	%intro;
	%fill (__Prove_Anything _ _ oh);
	%qed;
};
