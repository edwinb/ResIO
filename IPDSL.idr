-- Title: IP DSL
-- Author: Edwin Brady

include "bittwiddle.idr";

-- IGNORE
-- namespace IP {
-- START

-- Section Propositions

{-- We'll allow numbers within a packet to satisfy simple properties. 
    Less than, equal, and combinations of properties for now. --}

{-- The less than predicate: --}

  data LT : Nat -> Nat -> Set where
      ltO : LT O (S k)
    | ltS : LT n m -> LT (S n) (S m);

{-- A language of propositions: --}

  data Prop : Set where
      p_lt   : Nat -> Nat -> Prop
    | p_eq   : Nat -> Nat -> Prop
    | p_bool : Bool -> Prop
    | p_and  : Prop -> Prop -> Prop
    | p_or   : Prop -> Prop -> Prop;

{-- We can convert this language to propositions in Idris. We'll have
    less than and equality on natural numbers, and arbitrary booleans
    (which might arise from simple dynamic checks). --}

  propTy : Prop -> Set;
  propTy (p_lt x y) = LT x y;
  propTy (p_eq x y) = x=y;
  propTy (p_bool b) = so b;
  propTy (p_and s t) = (propTy s & propTy t); 
  propTy (p_or s t) = Either (propTy s) (propTy t);

{-- And we can test whether or not a proposition is true, and return a 
    proof of it, if it is true. --}

  mkLT : (x:Nat) -> (y:Nat) -> Maybe (LT x y);
  mkLT O (S k) = Just ltO;
  mkLT (S n) (S m) with mkLT n m {
     | Just p = Just (ltS p);
     | Nothing = Nothing;
  }
  mkLT _ _ = Nothing;

  mkEQ : (x:Nat) -> (y:Nat) -> Maybe (x = y);
  mkEQ O O = Just (refl _);
  mkEQ (S n) (S m) with mkEQ n m {
    mkEQ (S k) (S k) | Just (refl _) = Just (refl _);
                     | Nothing = Nothing;
  }
  mkEQ _ _ = Nothing;

  testProp : (p:Prop) -> Maybe (propTy p);
  testProp (p_lt x y) = mkLT x y;
  testProp (p_eq x y) = mkEQ x y;

  -- Slightly odd to do it this way, but keeping x dynamic at the top
  -- means that partially evaluating testProp with a known expression
  -- can make the Prop structure go away.

  testProp (p_bool True) = Just oh;
  testProp (p_bool False) = Nothing;
  testProp (p_and s t) with testProp s {
      | Just sp with testProp t {
          | Just tp = Just (sp, tp);
          | Nothing = Nothing;
        }
      | Nothing = Nothing;
  }
  testProp (p_or s t) with testProp s {
      | Just sp = Just (Left sp);
      | Nothing with testProp t {
          | Just tp = Just (Right tp);
      }
  }

-- Section: Bits

{-- "Chunk" gives the types of data which can appear in our packet format.
    "bit" is a number of bits, and "prop" is some arbitrary predicate,
    which in practice would be a predicate on some other data appearing
    in the packet. "loc" tells us how many bits we've got so far.

    'Cstring' is a null-terminated C string. 'Lstring' is a string
    with an explicit length.
--}

  infixl 5 :+:;

  data Location = Unknown | At Int;

  getLoc : Location -> Int;
  getLoc (At x) = x;
  getLoc Unknown = 0; -- Not sure about this...

  data Chunk : Set where
      bit     : (width: Int) -> (so (width>0)) -> Chunk
    | options : (width: Int) -> (so (width>0)) -> List Int -> Chunk
    | Cstring : Chunk
    | Lstring : Int -> Chunk
    | text    : Chunk
    | prop    : (P:Prop) -> Chunk
    | (|+|)   : Chunk -> Chunk -> Chunk
    | seq     : Chunk -> Chunk
    | end     : Chunk;

{-- We'll want to convert Chunks to Idris types. "Fin" is a bounded number,
    so we get some guarantee that any data we have fits.
--}

  chunkTy : Chunk -> Set;
  chunkTy (bit w p) = Bounded (1 << w);
  chunkTy (options w p xs) = Option (1 << w) xs;
  chunkTy Cstring = String;
  chunkTy (Lstring i) = String; -- maybe a length proof too?
  chunkTy text = String;
  chunkTy (prop P) = propTy P;
  chunkTy (a |+| b) = (chunkTy a & chunkTy b);
  chunkTy (seq c) = List (chunkTy c);
  chunkTy end = ();

{-- Calculate number of bits needed in the packet data for a chunk: --}

  chunkLength : (t:Chunk) -> chunkTy t -> Int;
  chunkLength (bit w p) _ = w;
  chunkLength (options w p _) _ = w;
  chunkLength Cstring p = 8 * (strLen p + 1); -- Null terminated
  chunkLength (Lstring i) _ = 8 * i; -- Not null terminated
  chunkLength text p = 8 * (strLen p); -- termination char (CR, LF or CR/LF) in string
  chunkLength (prop p) _ = 0;
  chunkLength (a |+| b) x = chunkLength a (fst x) + chunkLength b (snd x);
  chunkLength (seq c) Nil = 0;
  chunkLength (seq c) (Cons y ys) 
      = chunkLength c y + chunkLength (seq c) ys;
  chunkLength end _ = 0;

{-- Helps with PE. We can do something depending on a conditional, statically,
    even if its value isn't known. But we need to fix up the types. The idea
    is that any evaluation that needs doing gets done *before* reaching 
    'depIfV'. --}

  depIfV : {P:Bool->Set} -> (x:Bool) -> 
       	  (value:P x) ->
	  |(t:P True -> T) -> |(e:P False -> T) -> T;
  depIfV True v t e = t v;
  depIfV False v t e = e v;

  depIf : {P:Bool->Set} -> (x:Bool) -> |(t:P True) -> |(e:P False) -> P x;
  depIf True t e = t;
  depIf False t e = e;

-- Section: The DSL

  infixl 5 // ;

  -- IF makes a choice based on some known data, and corresponds to a
  -- concrete type computed from that data.
  -- // makes a choice based on what parses, and corresponds to an
  -- 'Either' type. (i.e. it's alternation in ABNF)

  data PacketLang : Set;
  mkTy : PacketLang -> Set;

-- Add a "CUSTOM" option, which takes current location and a state to update.
-- We'll need this for DNS, at least, and probably lots of other stuff.
-- ideally implementing CUSTOM things should be done in pure PacketLang.

  data PacketLang : Set where
      CHUNK    : (c:Chunk) -> PacketLang
    | LOCATION : PacketLang -> PacketLang
    | IF       : Bool -> PacketLang -> PacketLang -> PacketLang
    | (//)     : PacketLang -> PacketLang -> PacketLang
    | LIST     : PacketLang -> PacketLang
    | LISTN    : (n:Nat) -> PacketLang -> PacketLang
    | SEQ      : PacketLang -> PacketLang -> PacketLang
    | BIND     : (p:PacketLang) -> (mkTy p -> PacketLang) -> PacketLang;

{-- We'll want to convert our description of types into concrete types.
--}

  mkTy : PacketLang -> Set;
  mkTy (CHUNK c)    = chunkTy c;
  mkTy (LOCATION t) = Location -> mkTy t;
  mkTy (IF x t e)   = if x then (mkTy t) else (mkTy e);
  mkTy (l // r)     = Either (mkTy l) (mkTy r);
  mkTy (LIST x)     = List (mkTy x);
  mkTy (LISTN i x)  = Vect (mkTy x) i;
  mkTy (SEQ v k)    = (x : mkTy v ** mkTy k);
  mkTy (BIND c k)   = (x ** mkTy (k x));

  genMkTy : (Chunk -> Set) -> PacketLang -> Set;
  genMkTy cTy (CHUNK c) = cTy c;
  genMkTy cTy (LOCATION t) = Location -> genMkTy cTy t;
  genMkTy cTy (IF x t e) = if x then (genMkTy cTy t) else (genMkTy cTy e);
  genMkTy cTy (l // r) = Either (genMkTy cTy l) (genMkTy cTy r);
  genMkTy cTy (LIST x) = List (genMkTy cTy x);
  genMkTy cTy (LISTN i x) = Vect (genMkTy cTy x) i;
  genMkTy cTy (SEQ v k) = (x : genMkTy cTy v ** genMkTy cTy k);
  genMkTy cTy (BIND c k) = (x ** genMkTy cTy (k x));



{-- Calculate the number of bits required to store the data in a packet. --}

  bitLength : {p:PacketLang} -> mkTy p -> Int;
  
  bitLength {p=CHUNK c} = \d => chunkLength c d;
  bitLength {p=LOCATION t} = \d : (Location -> mkTy t) => bitLength {p=t} (d Unknown);
  bitLength {p=IF x t e}
    = depIf {P=\x => mkTy (IF x t e) -> Int} x
            (\d => bitLength {p=t} d)
	    (\d => bitLength {p=e} d);
  bitLength {p = l // r}
    = \d => either d (\l => bitLength l) (\r => bitLength r);
  bitLength {p = LIST x}
      = \d => foldl ( \len, y => (bitLength {p=x} y) + len) 0 d;
  bitLength {p = LISTN _ x}
      = \d => vfoldl ( \len, y => (bitLength {p=x} y) + len) 0 d;
  bitLength {p = SEQ v k}
    = \d => bitLength (getSigIdx d) + bitLength (getSigVal d);
  bitLength {p=BIND c k}
    = \d => bitLength {p=c} (getSigIdx d) + bitLength (getSigVal d);


-- IGNORE
-- }
-- START

unmarshalChunk : (c:Chunk) -> Int -> RawPacket -> Maybe (chunkTy c);
unmarshalChunk (bit w p) pos pkt ?= 
      getField pkt pos (pos + w) (ltAdd w p);  [rewriteField]
unmarshalChunk (options w p xs) pos pkt 
      with unmarshalChunk (bit w p) pos pkt {
       | Nothing = Nothing;
       | Just jv = either (choose (validOption (value jv) xs))
                        (\lp => Nothing)
	                (\rp => Just (Opt jv rp)); 
}
unmarshalChunk Cstring pos pkt = getString pkt pos;
unmarshalChunk (Lstring i) pos pkt = getStringn pkt pos i;
-- unmarshalChunk text pos pkt = getTextString pkt pos;
unmarshalChunk (prop p) pos pkt = testProp p;
unmarshalChunk (a |+| b) pos pkt 
     with unmarshalChunk a pos pkt {
         | Nothing = Nothing;
         | Just av with unmarshalChunk b (pos + chunkLength a av) pkt {
              | Nothing = Nothing;
	      | Just bv = Just (av, bv);
         }
}
unmarshalChunk (seq a) pos pkt
     with unmarshalChunk a pos pkt {
         | Nothing = Just Nil;
	 | Just v with unmarshalChunk (seq a) (pos + chunkLength a v) pkt {
              | Nothing = Nothing;
	      | Just vs = Just (Cons v vs);
         }        
}
unmarshalChunk end pos pkt = Just II;

unmarshal' : (p:PacketLang) -> Int -> RawPacket -> Maybe (mkTy p);
unmarshal' (CHUNK c) pos pkt = unmarshalChunk c pos pkt;
unmarshal' (LOCATION t) pos pkt with unmarshal' t pos pkt {
   | Just t' = Just (\p => t');
   | Nothing = Nothing;
}
unmarshal' (IF x t e) pos pkt = -- unmarshal' t pos pkt;
   depIf {P = \x => Maybe (mkTy (IF x t e))} x
         (unmarshal' t pos pkt) (unmarshal' e pos pkt);
-- unmarshal' (IF False t e) pos pkt = unmarshal' e pos pkt;
{-
    = depIf {P = \x => Maybe (mkTy' (IF x t e))} x
            (unmarshal' t pos pkt)
            (unmarshal' e pos pkt);
-}
unmarshal' (l // r) pos pkt 
   = maybe (unmarshal' l pos pkt)
       (maybe (unmarshal' r pos pkt)
              Nothing
	      (\y => Just (Right y)))
       (\x => Just (Left x));
unmarshal' (LIST x) pos pkt
   = maybe (unmarshal' x pos pkt)
       (Just Nil)
       (\v => maybe (unmarshal' (LIST x) (pos + (bitLength {pf=x} v)) pkt)
                (Just (Cons v Nil))
		(\vs => Just (Cons v vs)));
unmarshal' (LISTN O x) pos pkt = Just VNil;
unmarshal' (LISTN (S k) x) pos pkt
   = maybe (unmarshal' x pos pkt)
       Nothing
       (\v => maybe (unmarshal' (LISTN k x) (pos + (bitLength {pf=x} v)) pkt)
                Nothing
		(\vs => Just (v :: vs)));
unmarshal' (SEQ c k) pos pkt
   = maybe (unmarshal' c pos pkt) Nothing 
        (\v => maybe (unmarshal' k (pos + (bitLength {pf=c} v)) pkt)
	             Nothing
		     (\kv => Just <| v, kv |>));
unmarshal' (BIND c k) pos pkt 
   = maybe (unmarshal' c pos pkt) Nothing 
        (\v => maybe (unmarshal' (k v) (pos + (bitLength {p=c} v)) pkt)
	             Nothing
		     (\kv => Just <| v, kv |>));

unmarshal : (p:PacketLang) -> RawPacket -> Maybe (mkTy p);
unmarshal p pkt = unmarshal' p 0 pkt;

marshalChunk : (c:Chunk) -> chunkTy c -> Int -> RawPacket -> IO Int;
marshalChunk (bit w p) v pos pkt 
   = let v' : Bounded (1 << ((pos+w)-pos)) = ? in
     do { setField pkt pos (pos + w) v';
     	  -- putStrLn ((showInt pos) ++ ", " ++ (showInt (pos+w)) ++ ": " ++ showInt (value v'));
     	  return (pos+w); 
        };
marshalChunk (options w p xs) v pos pkt 
    = marshalChunk (bit w p) (bvalue v) pos pkt;
marshalChunk Cstring v pos pkt
   = do { putStrLn ("Marshal " ++ v);
     	  setString pkt pos v;
     	  return (pos+((1 + strLen v) * 8));
        };
marshalChunk (Lstring i) v pos pkt
   = do { setStringn pkt pos v i;
     	  return (pos+(i * 8));
        };
marshalChunk text v pos pkt
   = do { setStringn pkt pos v (strLen v);
     	  return (pos+((strLen v) * 8));
        };
marshalChunk (prop p) v pos pkt = return pos;
marshalChunk (a |+| b) v pos pkt 
   = do { pos' <- marshalChunk a (fst v) pos pkt;
     	  marshalChunk b (snd v) pos pkt; };
marshalChunk (seq a) Nil pos pkt = return pos;
marshalChunk (seq a) (Cons x xs) pos pkt
   = do { pos' <- marshalChunk a x pos pkt;
     	  marshalChunk (seq a) xs pos' pkt; };
marshalChunk end v pos pkt = return pos;


marshal' : {p:PacketLang} -> mkTy p -> Int -> RawPacket -> IO Int;

marshalList : (p:PacketLang) -> List (mkTy p) -> Int -> RawPacket -> IO Int;
marshalList p Nil pos pkt = return pos;
marshalList p (Cons y ys) pos pkt = do { pos' <- marshal' {p} y pos pkt;
	      	      	       	         marshalList p ys pos' pkt; };

marshalVect : (p:PacketLang) -> (Vect (mkTy p) n) -> Int -> RawPacket -> IO Int;
marshalVect p VNil pos pkt = return pos;
marshalVect p (y :: ys) pos pkt = do { pos' <- marshal' {p} y pos pkt;
	      	           	       marshalVect p ys pos' pkt; };

{--
marshalLoc : (x : Location ** mkTy p) -> Int -> RawPacket -> IO Int;
marshalLoc <| Unknown, x |> pos pkt = marshalLoc <| At pos, x |> pos pkt;
marshalLoc <| At l, x |> pos pkt =
      do { pos' <- marshal' {p=LOCATION} (At l) pos pkt;
      	   marshal' x pos' pkt; 
         };
--}

marshal' : {p:PacketLang} -> mkTy p -> Int -> RawPacket -> IO Int;
marshal' {p=CHUNK c} = \v, pos, pkt => marshalChunk c v pos pkt;
marshal' {p=LOCATION t} = \v : (Location -> mkTy t), pos, pkt => marshal' {p=t} (v (At pos)) pos pkt;
-- marshal' {p=IF True t e} = \v, pos, pkt => marshal' {p=t} v pos pkt;
-- marshal' {p=IF False t e} = \v, pos, pkt => marshal' {p=e} v pos pkt;
marshal' {p=IF x t e} 
     = depIf {P=\x => mkTy (IF x t e) -> (Int -> (RawPacket -> IO Int))}
             x (\v, pos, pkt => marshal' {p=t} v pos pkt)
               (\v, pos, pkt => marshal' {p=e} v pos pkt);
marshal' {p = l // r} = \v, pos, pkt =>
      either v (\lv => marshal' lv pos pkt) 
               (\rv => marshal' rv pos pkt);
marshal' {p = LIST x} = \v, pos, pkt => marshalList x v pos pkt;
marshal' {p = LISTN n x} = \v, pos, pkt => marshalVect x v pos pkt;
marshal' {p=SEQ c k} = \pair, pos, pkt => 
      do { pos' <- marshal' {p=c} (getSigIdx pair) pos pkt;
      	   marshal' {p=k} (getSigVal pair) pos' pkt; 
         };
marshal' {p=BIND c k} = \pair, pos, pkt => 
      do { pos' <- marshal' {p=c} (getSigIdx pair) pos pkt;
      	   marshal' (getSigVal pair) pos' pkt; 
         };

marshal : (pf:PacketLang) -> mkTy pf -> RawPacket;
marshal pf v = unsafePerformIO
	       do { pkt <- newPacket (bitLength v);
	            -- putStrLn (showInt (bitLength v));
	      	    marshal' v 0 pkt; 
		    return pkt; 
                  };

{-- A few bits and pieces to help notation... --}

syntax bits n = CHUNK (bit n oh);
syntax bitsp n = CHUNK (bit (value n) ?);
syntax fact n = CHUNK (prop n);
syntax check n = CHUNK (prop (p_bool n));
syntax offset = CHUNK len;
syntax CString = CHUNK Cstring;
syntax Text = CHUNK text;
syntax LString i = CHUNK (Lstring i);
syntax Options n xs = CHUNK (options n oh xs);
syntax Option x = Opt (BInt x oh) oh;

infixr 5 ## ;
syntax (##) x y = <| x, y |>;

{-- Note: Instead of the syntax stuff above, it would perhaps be
    better if Idris had a reflection mechanism which converted data
    declarations (which do look a bit like ABNF, as observed by
    Saleem) into a PacketFormat and generated the associated
    machinery. --}

do using (BIND, CHUNK) {

  testPacket : PacketLang;
  testPacket = do {
  	       	 ver <- bits 2; 
		 z <- bits 4;
		 fact (p_bool (value z > 0));
		 y <- bitsp z;
		 fact (p_bool (value ver == 1));
		 CHUNK end;
               };

{-
  marshalTest : mkTy testPacket -> RawPacket;
  marshalTest dat = marshal testPacket dat;
-}

  testIfPkt : PacketLang;
  testIfPkt = do {
  	        ver <- bits 2;
--		IF (value ver == 0) 
--		   CString
		   (do { x <- bits 8;
		       	 LString 55; }); -- (value x); });
              };

}

rewriteField proof {
	%intro;
	%rewrite <- addSub w pos;
	%refine value;
	%qed;
};

testPacket_1 proof {
	%intro;
	%trivial;
	%qed;
};

marshalChunk_1 proof {
	%intro pkt, pos, w, p;
	%rewrite <- addSub w pos;
	%intro;
	%rewrite addSub w pos;
	%fill v;
	%qed;
};

-- readTestIf = \p => unmarshal testIfPkt p; [%spec]
-- writeTestIf = \p => marshal testIfPkt p;  [%spec]

