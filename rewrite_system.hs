-- Rewrite System

-- Signature
type Signature = [(String, Int)]

type Position = [Int]

data Substitution a = Substitution [(a, a)]

-- Rewrite class
class Rewrite a where
  -- Get all vars from an object
  getVars :: a -> [a]
  -- Check if an object is valid from a signature
  valid :: Signature -> a ->  Bool
  -- Get all matches of a pattern in an object
  match :: a -> a -> [(Position, Substitution a)]
  -- Apply all the substitutions
  apply :: a -> Substitution a -> a
  -- Replace the object with the rules
  replace :: a -> [(Position, a)] -> a
  -- Evaluate an object
  evaluate :: a -> a

-- Rules
data Rule a = Rule (a, a)

instance Show a => Show (Rule a) where
  show (Rule (a, b)) = (show a) ++ " --> " ++ (show b)

type RewriteSystem a = [Rule a]

validRule :: (Rewrite a, Eq a) => Signature -> Rule a -> Bool
validRule s (Rule (a, b)) = (valid s a) && (valid s b) 
                            && (all (\x -> elem x varsA) $ getVars b)
  where
    varsA = getVars a

validRewriteSystem :: (Rewrite a, Eq a) => Signature -> RewriteSystem a -> Bool
validRewriteSystem s rs = all (\x -> validRule s x) rs

type Strategy a = ([(Position, a)] -> [(Position, a)])

-- Aux function for oneStepRewrite. Returns the list of [(Position, a)]
-- from a RewriteSystem and an object after applying rules
getReplacements :: Rewrite a => RewriteSystem a -> a -> [(Position, a)]
getReplacements rs a = concatMap f rs
  where
    f (Rule (x,y)) = map(\(p1, p2) -> (p1, apply y p2)) (match x a)

-- Makes a one-step rewrite
oneStepRewrite :: (Rewrite a, Eq a) => RewriteSystem a -> a -> (Strategy a) -> a
oneStepRewrite rs a st
  | replacements == [] = a
  | otherwise = replace a $ st $ replacements
  where replacements = getReplacements rs a

-- Complete rewrite (May halt!)
rewrite :: (Rewrite a, Eq a) => RewriteSystem a -> a -> (Strategy a) -> a
rewrite rs a s = until (\x -> x == (oneStepRewrite rs x s)) 
                 (\x -> evaluate $ oneStepRewrite rs x s) a

nrewrite :: (Rewrite a, Eq a) => RewriteSystem a -> a -> (Strategy a) -> Int -> a
nrewrite rs a s n
  | n == 0 = a
  | otherwise = nrewrite rs (oneStepRewrite rs a s) s (n-1)

--------------
-- RStrings --
--------------

-- Rewrite Strings. Is a list of Strings where each element
-- is a unit (a character followed by numbers)
data RString = RString [String]

isNumber :: Char -> Bool
isNumber c = (c >= '0') && (c <= '9')

-- Decompose a String in a elements of one character followed by numbers
decompose :: String -> [String]
decompose "" = []
decompose (s:ss) 
  = ((s : takeWhile isNumber ss)) : (decompose $ dropWhile isNumber ss)

-- Reads an string and turns into an RString
readRString :: String -> RString
readRString s = RString (decompose s)

-- Read RStringSystem
readRStringSystem :: [(String, String)] -> RewriteSystem RString
readRStringSystem l = map (\(x,y) -> Rule (readRString x, readRString y)) l

-- Show instance of RString
instance Show RString where
  show (RString s) = foldl (\x y -> x++y) "" s

instance Eq RString where
  (RString a) == (RString b) = a == b

instance Rewrite RString where
  -- Get vars of our object. For strings will only be "X" as a dummy object
  getVars (RString s) = [RString ["X"]]

  -- Check if an object is valid with a signature
  valid sign (RString s) = all (\x -> elem x list) s
    where list = map (fst) sign

  --match :: a -> a -> [(Position, Substitution a)]
  -- Assuming "X" is the var symbol
  match (RString pattern) (RString string) = matching 0 pattern string
    where
      matching i pattern [] = []
      matching i pattern string = act ++ (matching (i+1) pattern (tail string))
        where
          act = if pattern == (take l string)
                then [([i], Substitution [(RString ["X"], 
                      RString (drop l string))])]
                else []
            where l = length pattern

  -- apply :: a -> Substitution a -> a
  apply (RString s) (Substitution [(RString var, RString subs)]) 
    = RString (s ++ subs)
  apply (RString s) _ = (RString s)

  --replace :: a -> [(Position, a)] -> a
  replace (RString s) [([i], (RString subs))] = RString $ (take i s) ++ subs
  replace rstring [] = rstring

  --evaluate :: a -> a
  evaluate = id

-- RString strategies
leftmost :: [(Position, a)] -> [(Position, a)]
leftmost [] = []
leftmost [([i], x)] = [([i], x)]
leftmost l
  | (head $ fst $ head next) < i = next
  | otherwise = [head l]
  where
    next = leftmost $ tail l
    i = head $ fst $ head $ l


-- rightmost strategy
rightmost :: [(Position, a)] -> [(Position, a)]
rightmost [] = []
rightmost [([i], x)] = [([i], x)]
rightmost l
  | (head $ fst $ head next) > i = next
  | otherwise = [head l]
  where
    next = rightmost $ tail l
    i = head $ fst $ head $ l

---------------------
------- Trees -------
---------------------

data RTerm = Var (String) | Symb (String, Int) [RTerm] | Num String

-- Merge two substitutions
mergeRTermSubs :: Substitution RTerm -> Substitution RTerm -> Substitution RTerm
mergeRTermSubs (Substitution a) (Substitution b) = Substitution (a ++ b)

-- Check if a substitution is valid, there are no different subst. for same var
validRTermSubst :: Substitution RTerm -> Bool
validRTermSubst (Substitution []) = True
validRTermSubst (Substitution ((xl, xr):list)) 
  = all (\(l, r) -> (l /= xl) || (l == xl && r == xr)) list 
    && validRTermSubst (Substitution list)

-- Erase duplicate substitutions
redRTermSubst :: Substitution RTerm -> Substitution RTerm
redRTermSubst (Substitution list)
  = Substitution (foldl (\l x -> if elem x l
                                 then l
                                 else x:l) [] list)

-- RTerm match auxiliar functions
matching :: Position -> RTerm -> RTerm -> [(Position, Substitution RTerm)]
matching pos pattern tree
  | doesMatch && validRTermSubst subs = [(pos, redRTermSubst subs)]
  | otherwise = []
  where
    (doesMatch, subs) = doesPatternMatch pattern tree
      where
        -- Check if there is a match, and get the substitutions
        doesPatternMatch :: RTerm -> RTerm -> (Bool, Substitution RTerm)
        doesPatternMatch patt@(Var varname) tree 
          = (True, Substitution [(patt, tree)])
        doesPatternMatch patt@(Num patnum) tree@(Num treenum) 
          = (patnum == treenum, Substitution [(patt, tree)])
        doesPatternMatch patt@(Symb (pattname, pattargn) pattlist) 
                         tree@(Symb (treename, treeargn) treelist)
          | pattname == treename && pattargn == treeargn = (isOk, auxsubs)
          | otherwise = (False, Substitution [])
          where
            (isOk, auxsubs) 
              = foldl (\(ok, sub) (plist, tlist)-> 
                (ok && (fst $ doesPatternMatch plist tlist), 
                mergeRTermSubs sub $ snd $ doesPatternMatch plist tlist))
                (True, Substitution []) $ zip pattlist treelist

        doesPatternMatch _ _ = (False, Substitution [])

instance Rewrite RTerm where
  --getVars :: a -> [a]
  getVars rt@(Var name) = [rt]
  getVars (Symb x l) = concatMap (getVars) l
  getVars _ = []
  
  --valid :: Signature -> a ->  Bool
  valid sign (Symb ("+", _) _) = True
  valid sign (Symb ("*", _) _) = True
  valid sign symb@(Symb (str, narg) args) = (elem (str, narg) sign) 
                                            && (all (valid sign) args)
  valid sign _ = True

  -- traverse tree, check match at each node
  --match :: a -> a -> [(Position, Substitution a)]
  match pattern tree = traverse [] pattern tree
    where
      -- Traverse all the tree, and get all substitutions at each position
      traverse :: Position -> RTerm -> RTerm -> [(Position, Substitution RTerm)]
      traverse pos pattern (tree@(Symb (_, n) list)) 
        = (matching pos pattern tree) 
          ++ concatMap (\i -> traverse (pos++[i]) pattern (list !! i)) [0..(n-1)]
      traverse pos patter tree = (matching pos pattern tree)

  --apply :: a -> Substitution a -> a
  apply patt@(Var name) (Substitution subs) = snd $ head 
                                            $ filter ((==patt) . fst) subs
  apply patt@(Symb (name, n) list) subs = Symb (name, n) 
                                        $ map (\x -> apply x subs) list
  apply patt _ = patt

  --replace :: a -> [(Position, a)] -> a
  replace pattern [] = pattern
  replace pattern list = traverse [] pattern list
    where
      traverse :: Position -> RTerm -> [(Position, RTerm)] -> RTerm
      traverse pos patt list
        | elem pos $ map fst list = snd $ head 
                                  $ filter (\(x,y) -> pos == x) list
        | otherwise = auxtraverse pos patt list
        where
          auxtraverse :: Position -> RTerm -> [(Position, RTerm)] -> RTerm
          auxtraverse pos patt@(Symb (name, n) children) list 
            = (Symb (name, n) 
              (map (\i -> traverse (pos++[i]) (children !! i) list) [0..(n-1)]))
          auxtraverse pos patt list = patt

  --evaluate :: a -> a
  evaluate (Symb (f, n) children) 
    = auxevaluate (Symb (f, n) (map evaluate children))
    where
      auxevaluate (Symb ("+",2) [(Num x), (Num y)]) 
        = (Num (show $ (read x) + (read y)))
      auxevaluate (Symb ("*",2) [(Num x), (Num y)]) 
        = (Num (show $ (read x) * (read y)))
      auxevaluate x = x
  evaluate x = x

instance Show RTerm where
  show (Var x) = x
  show (Num x) = x
  show (Symb (name, args) []) = name
  show (Symb (name, args) sons) = name ++ "( " ++ foldl f "" sons ++ " )"
    where
      f text rterm
        | text == "" = (show rterm)
        | otherwise = text ++ " , " ++ show rterm

instance Show a => Show (Substitution a) where
  show (Substitution list) = "[" ++ (foldl f "" list) ++ "]"
    where
      f l (x,y)
        | l == "" = l ++ "(" ++ (show x) ++ "," ++ (show y) ++ ")"
        | otherwise = l ++ ",(" ++ (show x) ++ "," ++ (show y) ++ ")"

instance Eq RTerm where
  (Symb (ln, largn) llist) == (Symb (rn, rargn) rlist) 
    = ln == rn && largn == rargn && llist == rlist
  (Var x) == (Var y) = x == y
  (Num x) == (Num y) = x == y
  _ == _ = False

-- aux functions for reading
-- Length of terms to read from actual one
termLength :: Int -> [(String, Int)] -> Int
termLength _ [] = 0
termLength 0 _ = 0
termLength n ((s, x):list)
  | x <= 0 = 1 + (termLength (n - 1) list)
  | otherwise = 1 + (termLength (x + n - 1) list)

-- Splits the list of (String, Int) so fst is what it will use
splitChild :: Int -> [(String, Int)] -> ([(String, Int)], [(String, Int)])
splitChild n list = splitAt (termLength n list) list

auxRead :: [(String, Int)] -> (RTerm, [(String, Int)])
auxRead ((s, -2):list) = (Num s, snd $ splitChild 0 list)
auxRead ((s, -1):list) = (Var s, snd $ splitChild 0 list)
auxRead ((s, 0):list) = (Symb (s, 0) [], snd $ splitChild 0 list)
auxRead ((s, i):list) = (Symb (s, i) children, snd $ splitChild i list)
    where 
      children = take i $ map fst $ drop 1 
               $ iterate (auxRead . snd) (Var "dummy", list)

-- Read an RTree
readRTree :: [(String, Int)] -> RTerm
readRTree l = x
  where (x, y) = auxRead l

readRTermSystem :: [([(String, Int)], [(String, Int)])] -> RewriteSystem RTerm
readRTermSystem l = map (\(x,y) -> Rule (readRTree x, readRTree y)) l 

-- quick sort function to sort by length of position of tuples
qsortPos :: [(Position, a)] -> [(Position, a)]
qsortPos [] = []
qsortPos (p:xs) = (qsortPos $ filter ((< l) . length . fst) xs) ++ [p] ++ 
                  (qsortPos $ filter (not . (< l) . length . fst) xs)
  where
    l = length $ fst p

-- Strategies
isPrefix :: Position -> Position -> Bool
isPrefix as bs
  | length bs < length as = False
  | otherwise = as == take (length as) bs

-- Sort by length decreasing and remove conflicts
parallelinnermost :: [(Position, a)] -> [(Position, a)]
parallelinnermost xs = foldl f [] $ reverse $ qsortPos xs
  where
    f list (ap,aa)
      | any (isPrefix ap) $ map fst list = list
      | otherwise = (ap,aa):list


paralleloutermost :: [(Position, a)] -> [(Position, a)]
paralleloutermost xs = foldl (\list (ap,aa) -> if any (`isPrefix` ap) $ map fst list
                                              then list
                                              else (ap,aa):list) [] $ qsortPos xs
  where
    f list (ap,aa)
      | any (`isPrefix` ap) $ map fst list = list
      | otherwise = (ap,aa):list

leftmostinnermost :: [(Position, a)] -> [(Position, a)]
leftmostinnermost xs = [foldl (\(mp,ma) (p,a) -> if mp < p
                                                then (mp,ma)
                                                else (p,a)) a as]
  where (a:as) = parallelinnermost xs

leftmostoutermost :: [(Position, a)] -> [(Position, a)]
leftmostoutermost xs = [foldl (\(mp,ma) (p,a) -> if mp < p
                                                then (mp,ma)
                                                else (p,a)) a as]
  where (a:as) = paralleloutermost xs

