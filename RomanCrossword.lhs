\begin{code}
import Data.List
import Data.Function

\end{code}

Layout helper

\begin{code}
layout :: Show a => [a] -> IO ()
layout = putStr . unlines . map show

ls =  (layout . convertToNumeral) 

\end{code}

PART 0

Symbol	I	V	X	L	C	D	M
Value	1	5	10	50	100	500	1000

1. Convert Roman numerals to any positive integer up to 3999

The solution is based on the realisation that Roman numerals can be viewed as a 
point between lower, mid and upper symbols, where the magnitude of the number defines
the subset of symbols. From this we can see the following pattern is always obeyed in the
standard system:  (L)+++-M+++-H. Where L, M, H are a subset of symbols from a set of numerals. 
This can also be written as 

N<3  | N=4  | N=5 | N<9 & N>5 | N=9
L*N, |LM,   | M   | M+(d*L)   | L-H, 

N is the number being converted, and d := the difference between the number and 
the midpoint of the range (i.e. 5).

N.b. In contiguous magnatudes, the L of the second set is necessarily the H of the preceding set. 

When viewed in this way we can see that the numeral symbols can be grouped with the magnitude for which they are bounds as follows: 

Units: "IVX"
Tens: "XLC"
Hundreds: "CDM"
Thousands: "M"

Note, that thousands only has a lower bound, hence the invariant that 3999 is the largest number that 
can be represented in this system. 

The elegance of this number system is that the L*N, LM, M, M + (d*L) L-H described above holds at the 
micro and macro level, meaning that we can utilise it to convert every digit of a number, and then simply concatenate the results back together E.g. 

24 = Tens 2, units 4 
Tens 1 = 2 * Lower bound for tens = XX
Units = 4 = Mid bound - lower bound for units = IV
24 = XXIV

The below algorithm does exactly this, namely: 

0. If N > 3999 error,
1.  Zip the reversed number with the corresponding subset of numerals. (n.b. `show` is used here to allow reversal of an int by first representing it as a string )
    -- e.g. given N = 123, this zip would yield
    [(3, "CDM"), (2, "XLC"), (1, "IVX")]
2. Via a list comprehension, pass each tuple of this list to be converted (using `convertPostion` function), where `convertPostion` Implements the  L*N, LM, M, M + (d*L) L-H conversion pattern.
    -- e.g. ["C", "XX", "III"]
3. Concatenate the resulting list of Strings together for the final output: 
    -- e.g. "CXXIII"

\begin{code}

symbols = ["IVX","XLC","CDM","M"]

convertToNumeral :: Int -> String
convertToNumeral num 
    | num > 3999 = error "Too big for number system!"
    | otherwise = concat [ convertPostion x | x <- reverse (zip (reverse (show num)) symbols)]


convertPostion :: (Char, [Char])  -> String
convertPostion y 
    | x <= 3 =  replicate x lower
    | x == 4 = lower : [mid]
    | x == 5 = [mid]
    | x == 9 = lower : [higher]
    | otherwise = mid : replicate (x - 5) lower
    where (x, symbols) =  (read [fst y] :: Int, snd y)
          (lower, mid, higher) = (symbols !! 0, symbols !! 1, symbols !! 2)

\end{code}

2. Upperbound

Axioms: 

1. 2* D, 1* M in grid
2. Appearing in three entries, meaning that each appear separately from each other
3. All entries are > three characters long

The upper bound can be deduced logically by first working out the lowest and highest possible values in a searchspace if we were going to use a brute force approach. 
We know that the upper bound must contain an M, so the lower bound is at least > 1000. Conversely, we know from axiom 2 that the three characters are split over separate entries, 
meaning that an "MD" combination is not possible. Therefore we know that the upperbound must be less than 1400 as this is where MD pairing first appears. Therefore the upper bound is the 
highest entry > three characters between 1000..1399. This actually turns out to be the maximum of this range, 1399, "MCCCXCIX". 

\begin{code}

upperBound = fst (last  [(x,  numeral) | x <- [1000..1399], let numeral = convertToNumeral x, isPrime x && length numeral > 3 && 'M' `elem` numeral  && not ('D' `elem` numeral )])

\end{code}

We can make this a lot more efficient by starting at the upper limit for the upper bound and working backwards if all axiom predicates are not met: 

\begin{code}
upperBound' :: Int
upperBound' = fi 1399


fi :: Int -> Int
fi x
    | predicates = x
    | otherwise = fi (x - 1)
    where numeral = convertToNumeral x
          predicates = (isPrime x && length numeral > 3 && 'M' `elem` numeral  && not ('D' `elem` numeral ))

\end{code}

Note, this above implementation works before we've already deduced that the upper limit for the upper bound is 1399, therefore the algorithm is relying on the hard coded 
`upperBound' = f 1399`. For example if we change this line to `upperBound' = f 3999` the algorithm would fail as it fails to take into account only axiom 2, i.e. multiple 'M' are 
not explicitly disallowed. If we wanted to abstract away some of the brain work and make this an entirely brute force approach that didn't rely on the initial hardcoded upper limit we 
would have to check only instances of the letter occurs in the match. 

\begin{code}
upperBound'' :: Int
upperBound'' = f' 3999

f' :: Int -> Int
f' x
    | predicates = x
    | otherwise = f' (x - 1)
    where numeral = convertToNumeral x
          predicates = (isPrime x && length numeral > 3 && dm )
          dm = length (filter (`elem` ['D', 'M']) numeral ) == 1

\end{code}


This implementation confirms that our initial non brute force approaches were indeed correct:

ghci> upperBound
1399
(0.02 secs, 8,241,440 bytes)
ghci> upperBound'
1399
(0.00 secs, 138,328 bytes)
ghci> upperBound''
1399
(0.05 secs, 54,489,448 bytes)

N.b. see below for details for the `isPrime` function used here.

Initially it looked at this point that the solution had been found, however upon reaching q.6
I was forced to question the assumptions made of the upper bound, at which point the realisation was made that 
axiom two was incorrect as the entries could be overlapping in the grid. With this in mind, we can adjust the algorithm 
to simply find the largest three character prime containing only one 'M'.  

\begin{code}
upperBound''' :: Int
upperBound''' = f'' 3999

f'' :: Int -> Int
f'' x
    | predicates = x
    | otherwise = f'' (x - 1)
    where numeral = convertToNumeral x
          predicates = (isPrime x && length numeral > 3 && dm )
          dm = length (filter (`elem` ['M']) numeral ) == 1

\end{code}


Which yields:

ghci> upperBound'''
1889

3. Bounded Primes

For this problem the 'Sieve of Eratosthenes' is used to filter primes. 
Turner (1975) is attributed to defining a functional implementation of the Sieve. 
In the Sieve algorithm, whenever a prime is identify all multiples of that prime can
be removed ('sieved') out of the search space for possible primes, as it is known that they are 
divisible by at least the identified prime. 

Turner's implementation has been shown to be suboptimal asymptotically (https://www.cs.hmc.edu/~oneill/papers/Sieve-JFP.pdf).
O'Neill (2009), brands the implementation as the 'unfaithful Sieve' arguing it is not an accurate 
translation of the Sieve as described by Eratosthenes (due to how the non-primes are eliminated immediately after primes are found, 
rather than lazily and starting from the primes' square and working back towards the prime (O'Neill (2009))). 

O'Neill instead presents the 'genuine Sieve of Eratosthenes' as follows, (n.b. this is slightly altered to handle x <= 1):

\begin{code}
primes = 2 : [x | x <- [3..], isPrime x]
isPrime x 
    | x <= 1 = False
    | otherwise = all (\p -> x `mod` p > 0) (factorsToTry x)
    where factorsToTry x = takeWhile (\p -> p*p <= x) primes
\end{code}

algorithm works as follows:

primes := the list of all numbers which satisfy the predicate `isPrime`
isPrime:= Uses `all` and a lambda function to check that all values `p` of the iterable `factorsToTry` modulo x are greater 1.
factorsToTry:= uses a takewhile loop to iterate all ps in primes that are <= x, starting from p squared.
E.g. factorsToTry 17 is equal to [2,3]. 

This is a beautiful implementation in haskell as both `primes` and `factorsToTry` reference each other in their definitions, meaning that
the lazy evaluation properties of haskell are put to optimum use as the `primes` infinite list is being dynamically evaluated up to x just 
at the point it is required for computation.

https://www.cs.hmc.edu/~oneill/papers/Sieve-JFP.pdf
https://wiki.haskell.org/index.php?title=Prime_numbers&oldid=36858#Postponed_Filters_Sieve

\begin{code}
type Roman = String 
roman :: Int -> Roman
roman a = convertToNumeral a

type Pair = (Int, Roman)

boundedPrimes :: [Pair]
boundedPrimes = [(x, roman x) | x <- [2..upperBound'''], isPrime x]

\end{code}

The `Roman` type has been made to derive Show, Eq, and Ord. This is to enable ease
of comparison later to solve the equations. As a Pair is constructed of a tuple (Int, Roman)
an element wise comparison will be used, meaning that a simple a > b for any pair (a, b) Pairs is possible.

4. Numeral Length

\begin{code}


n1', n2', n3', n4', n5', n6', n7', n8' :: [Int]
n1' = integerOfNumeralLength 1
n2' = integerOfNumeralLength 2
n3' = integerOfNumeralLength 3
n4' = integerOfNumeralLength 4
n5' = integerOfNumeralLength 5
n6' = integerOfNumeralLength 6
n7' = integerOfNumeralLength 7
n8' = integerOfNumeralLength 8
n9' = integerOfNumeralLength 9


p1', p2', p3', p4', p5', p6', p7', p8', p9' :: [Pair]
p1' = numeralsOfLength 1
p2' = numeralsOfLength 2
p3' = numeralsOfLength 3
p4' = numeralsOfLength 4
p5' = numeralsOfLength 5
p6' = numeralsOfLength 6
p7' = numeralsOfLength 7
p8' = numeralsOfLength 8
p9' = numeralsOfLength 9

-- Note these all have the additional ' as they are redefined below.

integerOfNumeralLength :: Int -> [Int]
integerOfNumeralLength x = [fst x | x <- numeralsOfLength x]

-- not used but here's a list of all possible numerals
numerals = take upperBound [numeral | x <- [1..], let numeral = convertToNumeral x] 

numeralsOfLength :: Int -> [Pair]
numeralsOfLength x 
    | x == 0 = []
    | x > 3999 = []
    | otherwise = [(i, numeral) | i <- [1..upperBound], let numeral = convertToNumeral i, length numeral == x && isPrime i]
\end{code}


This implementation works fine, however the issue with it is that for any value of i all numerals are checked. We could say that
it is not really in the spirit of haskell, as the `numerals` list is greedily computed and exhaustively checked every time the `numeralsOfLength`
function is called. A better solution is to lazily group the numerals by their length and then retrieve just the relevant grouping.

This can be refactored using sortBy, GroupBy and on as follows: 

\begin{code}
numeralsOfLength' :: Int -> [(Int, String)]
numeralsOfLength' x = pairs !! (x -1)
    where pairs = groupBy ((==) `on` (length . snd)) (sortBy (compare`on` (length . snd)) nums)
          nums = [(i, numeral) | i <- [1..upperBound], let numeral = convertToNumeral i, isPrime i]
\end{code}

This is an improvement as we now group all numerals together and then just return the x-1 position (because of zero indexing)
for a given x, rather than exhaustively checking up to upperbound for any x, but currently it an [(Int, String) ] not a [Pair].

A further refactor is required to make this return a Pair:

\begin{code}
numeralsOfLength'' :: Int -> [Pair]
numeralsOfLength'' x = pairs !! (x -1)
    where pairs = groupBy ((==) `on` l) (sortBy (compare `on` l) boundedPrimes)
          l = (length . snd)

\end{code}

There is a further improvement here to reuse `boundedPrimes` rather than calculate the prime pairs on the fly.

If we can now put this together (p1, n1... p9, n9) type annotations for the improved function above.

\begin{code}

nl = numeralsOfLength''

n1, n2, n3, n4, n5, n6, n7, n8 :: [Int]
n1 = inl 1
n2 = inl 2
n3 = inl 3
n4 = inl 4
n5 = inl 5
n6 = inl 6
n7 = inl 7
n8 = inl 8
n9 = inl 9


p1, p2, p3, p4, p5, p6, p7, p8, p9 :: [Pair]
p1 = nl 1
p2 = nl 2
p3 = nl 3
p4 = nl 4
p5 = nl 5
p6 = nl 6
p7 = nl 7
p8 = nl 8
p9 = nl 9

inl :: Int -> [Int]
inl x = [fst x | x <- nl x]

\end{code}

PART 1

5. Equation 6 - two letter primes for a,b 

Given we know that a, b are two character primes we need to find all the possible permutations of the 
two character primes. 

p2 = [(2, "II"),(11, "XI"),(101, "CI")]

\begin{code}
enum = zip [0..] n2
ab = [(snd x, convertToNumeral (snd x), snd (enum !! i), convertToNumeral (snd (enum !! i))) | x <- enum, i <- [0..(length enum -1)], fst x /= i]
\end{code}

The algorithm makes use of the `zip` function with `n2` from step 4 produce a numbering of the items in 
`n2`. This approach was based on the `enumerate` concept in python, in which an iterable, x can be enumerated 
to yield each item and an index for item in x. 

E.g.

`enum = zip [0..] n2` 

yields the following list of tuples: `[(0,2),(1,11),(2,101)]`, where the first entry is the ith position of `[0..]`

We then can iterate enum (as 'x'), and a range up to the length of enum-1 (as 'i'). The predicate `fst x /= i`
is used to guard against adding combinations of the same item, when collecting tuples of `snd x, snd (enum !! i)`
on the left side of the list comprehension. 

Running this we can see the possible values for a,b are: 
[("II","XI"),("II","CI"),("XI","II"),("XI","CI"),("CI","II"),("CI","XI")]

This can be made a bit more reusable by wrapping it in a function that takes the n-iterable to enumerate, where n is the length of the numeral. 

\begin{code}
candidatePairs :: [Int] -> [(Int, String, Int, String)]
candidatePairs [] = []
candidatePairs (x:xs) = [(snd x, convertToNumeral (snd x), snd (enum !! i), convertToNumeral (snd (enum !! i))) | x <- enum, i <- [0..(length enum -1)], fst x /= i]
    where enum = zip [0..] (x:xs)
\end{code}

This implemention works insofar as it returns the correct candidate pairs for a given n value, but it could be improved as currently it returns all candidates as a list 
of quads (Int, String, Int, String). 

E.g. `candidatePairs n2` returns the following List. 
[(2,"II",11,"XI"),(2,"II",101,"CI"),(11,"XI",2,"II"),(11,"XI",101,"CI"),(101,"CI",2,"II"),(101,"CI",11,"XI")]

Whilst this is fine to read in the display, it is limited promatically as built in tuple functions such as `fst`, `snd` have no meaning here.

The below refactoring returns a tuple of Pairs for each candidate pair to overcome this.

\begin{code}
candidatePairs' :: [Int] -> [(Pair, Pair)]
candidatePairs' [] = []
candidatePairs' (x:xs) = [(toPair x, toPair (enum !! i)) | x <- enum, i <- [0..(length enum -1)], fst x /= i]
    where enum = zip [0..] (x:xs)
          toPair z = (snd z, roman (snd z))
\end{code}

E.g. `candidatePairs' n2` returns the following List of tuples of Pairs: 
[((2, "II"),(11, "XI")),((2, "II"), ...]

6. s,t possible values

One way to approach solving this is to iterate the possible values of b -a from step 5, and then compare the difference to all possible of deltas of n9. 
For example, the first two positions of `n9` are [283,337], assuming t > 3, the difference is 54, meaning that is there is an a-b combination = 54 
this combination would satify the equation.

We can use the candidatePairs' function to find all candidate of length two are then calculate the difference between each candidate: 

[(fst (fst x) - fst (snd x)) | x <- candidatePairs' n2]

This yields the list: `[-9,-99,9,-90,99,90]`. We can now use this list to search for the n9 space, as if any of these distances are found a potential solution 
for the equation has been found. An optimisation is possible here as for a given pair from n9, (x, y) and a distance d from these deltas, if y -x = d, then x-y = -d, 
therefore we can eleminate the negative numbers from deltas and just use the absolute values of the distances to reduce the search space. This can be done by converting 
the list of absolute distance to a set (o(n log n)) using `Set.fromList` from Data.Set, however as sets are not really purpose built for iterating over, it makes more 
sense to keep the data as a List and make use of the symetry that we know exists. This can be achieved with the `nub` function from `Data.List` 
(https://hackage.haskell.org/package/base-4.14.1.0/docs/Data-List.html#v:nub).

As a reminder, the approach to solving this is to calculate all possible deltas from n9 and find those which are equal to any of the deltas from n2. The issue 
with this is that it is clearly an inefficient approach as for every i in n9, the difference has to be calculated against every other i' o(n**2), and then compared 
against the target deltas of n2. 

A better approach is to use to make use of transitivity and the fact the n9 list is ordered. Rather than comparing all values for every iteration as described above, 
we instead compare all values from a given starting point until difference is > the maximum of the deltas from the previous step (aka. the potential b-a values). 

E.g. Given the list of values l, ([a,b,...n]) and a maximum delta m, we can say that for each i,j in l: 

1. if i - j > m: then all to the right of than j are also > than m. 
2. if i - j is in deltas, i, j are potential values for s,t. 

Therefore we can build an algorithm which stats at i and finds all potential pairs of i until the gap reaches m, at this point more onto the next value in l 
and reapeat, finally once we reach the end of l, return the accumulator.

The algorithm is implemented as follows: 

0. Build find the potential pairs for all all left -> right slices of the input list, passing in the slice as `x` and the [(0,0)] as the empty accumulator.
    0.a `slice` is based on the python slice opperator taking a start:end indexes of a list and returning a new list to from these position. 
    In this implemetion just a `from` index is needed as we are always slicing to the end of the input. 
    e.g. slice 1 [0..2] would return [1,2]
1. Pattern match an empty list as xs and return the accumulator
2. Pattern match delta in deltas - add the two numbers being compared to acc, and recurse on the next position in l. 
3. Patten match delta > m - In this case we know through transitivity that delta the rest of the tail, so return the accumulator (meaning the next slice from 0 will be passed in)
4. Patten match delta < m - Continue recursion from the current value of x, but don't add anything to the accumulator as it isn't a match.
5. Finally convert all non (0,0) items from the accumulator and return whats left.
    5.a. Removing all non zero Pairs leaves empty lists in their place, for neatness we should tidy these up. 
    5.b We've been working with [[Pair]] so far so convenience of map, filter etc. we now just need to convert what's left into [(Pair, Pair)]


Whilst is approach is more efficient the alternative non transitive algorithm, it does come at a slight trade off in terms of the elegance of the code. 
For example, it would have been possible to implement this using a fold method if didn't care about exhausting all checks in the input on each recursion.
Further, as the recursive function takes a accumulator we need to first call it with an accumulator, there is no concept of an empty Pair, so the best we can 
manage is to pass in the value 0 to `toPair`(e.g. (0, "")) and then filter these values from the output.


\begin{code}
sts:: [(Pair, Pair)]
sts = map toTup res
    where xs = n9
          res = filter (notEmptyList) (notZero (concat [d x [[zero, zero]] | x <- [slice s xs | s <- [0..length xs -1]]])) -- 0
          slice from xs = take (length xs - from) (drop from xs) --0.a
          zero = toPair 0
          notZero a = map (\x -> f (x)) a where f = filter ( > zero) --5
          notEmptyList a = (not . null) a  -- 5.a
          toTup [x, y]  = (x, y)      -- 5.b
          
        
d :: [Int] -> [[Pair]] -> [[Pair]]
d (x:xs) acc
    | null xs  = acc  --1 
    | delta `elem` deltas = d (x : tail xs) ([toPair x, toPair (head xs)]: acc)  --2
    | delta > m = acc  -- 3
    | delta < m = d (x : tail xs) acc -- 4
    where delta =  abs (x - head xs)
          deltas = nub [abs (fst (fst x) - fst (snd x)) | x <- candidatePairs' n2]
          m = maximum deltas

toPair :: Int -> Pair 
toPair x = (x, roman x)

\end{code}


PART 2

7. 

d == Vt + c + n
d -c -n == Vt

- Minimum value for t (q.6 -sts !! 0 )
- Find minimum values for c (3 chars), n  (6) - these give a lower bound for d. 
- what possible values for d (4 chars) > the lower bound?

\begin{code}
ds :: [Int]
ds = filter (>= g) (map (fst) p4)
    where lc = (n3 !! 0)
          ln = (n6 !! 0)
          vt = fst (fst (sts !! 0)) * 5
          g = vt + lc + ln 
\end{code}

8. Possible values for dtns 

We can deduce from step 5 that the value for t must be the lowest value of sts any 5 * any other leaves no values for d within the upper limit when adding the 
lowest possible values for c,n. We can confirm this by altering the fuction above to use the next possible t in the sequence: 

\begin{code}
ds' :: [Int]
ds' = filter (>= g) (map (fst) p4)
    where lc = (n3 !! 0)
          ln = (n6 !! 0)
          vt = fst (snd (sts !! 0)) * 5
          g = vt + lc + ln 
\end{code}
 
ghci> ds'
[]

Therefore we can plug the value for t into the equation. We can simplify the right hand side of the equation to find possible values for c,n:

d - Vt = c + n 

1. Iterate the possible values for d. 
2. Iterate possible iterate value of c + n to find those which = d - vt. 

Note, a optimisation making use of transitivity is possible in a similar manner to question 6, but in this case the simple solution has been favoured as the 
n * m inputs list (n3, n6) are much smaller so in this case simplicity can be favoured over optimisation.

\begin{code}
dtcns :: [(Int, Int,Int, Int)]
dtcns = [(t+c+n, t,c,n) | c <- n3, n <- n6, let cn = c+n, let t = (fst (fst (sts !! 0))),  cn `elem` [d - t * 5 | d <- ds]]
\end{code}

In the above list comprehension, the second nest list comprehension of all values of ds - Vt is created, then for possible all values v of c+n, if v is in that list 
then the value of t+c+n is a potential solution for d.

ghci> dtcns
[(379,283,7,89),(469,283,7,179),(469,283,19,167),(379,283,59,37),(469,283,59,127)]

9. s, t values 

So we know now that t = 283, and therefore s must equal the corresponding tuple from sts. 

\begin{code}
s,t :: Int
s = (fst . snd ) (sts !! 0)
t = (fst . fst ) (sts !! 0)
sr, tr:: Roman 
sr = roman s
tr = roman t
\end{code}

ghci> s
373
ghci> sr
"CCCLXXIII"
ghci> t
283
ghci> tr
"CCLXXXIII"


10. sts'

As we know that 20d has to be a two character numeral we know that 20a has to start with a 'C'. Therefore 
any non 'C' prefix-numerals can be ruled out of consideration of sts, we can therefore use the list existing sts 
implemention as a list comprehension and rull out any entries whose numerals do not begin with a 'C'.

\begin{code}

sts' ::  [(Pair, Pair)]
sts' = [x | x <- sts, (snd . fst) x !! 0 == 'C' || (snd . snd) x !! 0 == 'C' ]
          
\end{code}

sts'
[((283,"CCLXXXIII"),(373,"CCCLXXIII"))]

11. Pattern match

This generalisation can be achieved with a simple recursive function and pattern matching and an accumulating parameter, 
which in this case is simply a Boolean value of the previous characters checked. The rules for which are:

1. '.' is a wildcard - it matches any character
2. If xi == yi for i in x,y those characters are a match
3. Match of [] [] returns the accumulator

\begin{code}
type Pattern = String

match :: String -> String -> Bool
match x y = match' x y True

match' :: String -> String -> Bool -> Bool  
match' _ _ False  = False
match'(x:xs) ('.':ys) b  = match' xs ys b
match'(x:xs) (y:ys) _  = match' xs ys (x == y)
match' [] [] b = b
match' _ "" b = b

\end{code}

Some tests:

ghci> match "xy" ".x"
False
ghci> match "xyz" "..x"
False
ghci> match "xyz" "..z"
True
ghci> match "xyz" "x.z"
True
ghci> match "xyz" ".yz"
True
ghci> match "xyz" ".y."
True
ghci> match "xyz" "..."
True
ghci> match "xyz" "x.."
True
ghci> match "CCLXXXIII" "C........"
True
ghci> match "CCLXXXIII" "C....D..."
False
ghci> match "CCLXXXIII" "D....X..."
False

Note, the accumulating parameter for match is started as True, this is because the all wildcard pattern should match any numeral of the same length.

12. a, b values

We know that t=283 and s=373 so we can start substituting in the values to the equation:

s + b = t + a 
= s - t + b = a 
= 373 - 283 + b = a
= 90 + b = a
= 90 = a - b 

\begin{code}
a,b :: Int 
(a, b) =  [(a,b) | a <- n2, b <- n2, a-b == 90] !! 0
\end{code}

ghci> a
101
ghci> b
11

This can be verified with:

ghci> s + b == t + a
True

13. Equation 3 - m 

In a similar manner to 12, we can substitute in our know values for a, s to the equation to solve for m. 

m + IV = s + IIa
= m + IV = 373 = 202
= m + IV = 575
= m = 571

\begin{code}
m :: Int
m = filter (== 571) n5 !! 0
\end{code}

Using this much basic maths to hardcode the value for m feels slightly cheating, so we could reimplement this entirely using haskell:

\begin{code}
m' :: Int
m' = filter (== (s + 2 * a - 4)) n5 !! 0
\end{code}

ghci> m'
571
ghci> m' == m
True

STEP THREE

14. Equation 5 - qrs values

We can reuse the above `match` to help us here as we know that the fix values for points that cross in the grid. 
The numerals "CCCLXXIII" | "CCLXXXIII" must occupy 7a, 20a in either order. In the case of 7a the shared character is the second, and 20a the shared is the eight. 
Therefore the placements can be deduced by finding matching seven character numerals with corresponding patterns.

This presents a good opportunity for generalisation, namely we can define a function `crossMatch` which returns matching pairs from a given list of Pairs given some 
index at which the lines cross. For example, `crossMatch p4 "XI" 1` should return all numerals of length four that share a character at index one (of the search set) with the input numeral (in this case 'I').

In order to implement `crossMatch` we first need a way to dynamically generate patterns to match. This is achieved by implementing a function which given a Roman and an index will return 
a string of '.' occupying all positions except the index (at which point the character of the numeral at that position is returned). 
e.g. `fillDots "XII" 0` should return "X.." whereas `fillDots "XII" 1` should return ".I.". This patterns can then be fed into the `crossMatch` function to find all matches for the given pattern 
within a group of numerals. 

Previously some of the functions have been implemented using recursion and an accumulating parameter, for this implemention it was decided to follow a similar approach but using the foldl abstraction 
instead of recursion.

fillDots

1. Iterates a ziped list of the input numeral (r) and it's length (as in the `enum` pattern seen earlier) and the accumulating parameter is instaniated as an empty string. 
2. Pattern matching within the lambda is used to extract i, r from the enum
3. if i == ix (where ix is the index passed in to the function) add the r value to the accumulating parameter
4. otherwise, add the '.' character

ghci> fillDots "CCLXXIII" 0
"C......."

crossMatch

`crossMatch` is now implemented in a similar manner, but folding along all numerals in a list of Pairs, and
accumulating all values which match a given pattern from a starting numeral and index. 

e.g. `crossMatch p2 "CI" 0` will find all matching two character numerals where the zeroth character is 'C'. 

ghci> crossMatch p2 "CI" 0
[(101,"CI")]

(Incidently, we've now answered 20d with this!)

An additional helper function `overlap` is required to wrap the previously  defined `match` function. This is because the assumption of `match x, y` is that x and y are the same length,
in fact we're now looking for patterns which would fit an when overlapping rather than direct like for like spaces of the same length. 
To handle this, we simply need to take the first n characters of the x as these are all that are required to say whether two numerals of different length overlap around a shared character.  

\begin{code}
crossMatch:: [Pair] -> Roman -> Int -> [Pair]
crossMatch (p:ps) r ix = foldl (\acc p -> if overlap r (fillDots (snd p) ix ) then acc ++ [p] else acc) [] (p:ps)

overlap :: Roman -> Roman  -> Bool
overlap a b = match (take (length b) a) b

fillDots :: Roman -> Int -> String
fillDots r ix = foldl (\acc (i, r) -> if i == ix then acc ++ [r]  else acc ++ ".") "" (zip [0..] r)

\end{code}

We can now put the above generic code together to find the possible values for qrs. To do this in the general sense we need to 
Find all cross matches p r i for a given p of n length numerals, for all rs to be fit across the grid and for all i's of the crossed index.

e.g. `(crossMatch p7 sr 1 ++ crossMatch p7 tr 1 ++ crossMatch p7 sr 6 ++ crossMatch p7 tr 6)`

Where 1, 6 are the crossing indexes in the grid of the shorter length space. Note coincidently both the first and sixth index (counting from zero) in sr and tr are the same ('C', 'I') so in this case we could 
simplify the implemention to just: `(crossMatch p7 sr 1 ++ crossMatch p7 sr 6)`` or `(crossMatch p7 tr 1 ++ crossMatch p7 tr 6)`.

ghci> crossMatch p7 tr 1 ++ crossMatch p7 tr 6 == crossMatch p7 sr 1 ++ crossMatch p7 sr 6
True

If we wanted to further genericise this would could do so by defining a function which avoids the need to hardcode the `pool` stage below, but rather takes a list 
of pairs, a list of cross matching indexes and list of numerals to match against and permutates the possible outcomes into `crossMatch` to find the pool of candiate matches.

Note this currently gives us a list of all possible values of qr, we need to finally turn this into a [(Pair, Pair)] in order to fulfill the function handle, we can find 
these by plugining in the equation to a list comprehension as below.

\begin{code}
qrs :: [(Pair, Pair)]
qrs = [(q, r) | q <- pool, r <- pool, (fst q) + 15 == 4 * (fst r)]
    where pool = nub (crossMatch p7 sr 1 ++ crossMatch p7 tr 1 ++ crossMatch p7 sr 6 ++ crossMatch p7 tr 6)

qrs' :: [(Pair, Pair)]
qrs' = [(q, r) | q <- p7, r <- p7, (fst q) + 15 == 4 * (fst r)]

\end{code}

ghci> qrs
[((317,"CCCXVII"),(83,"LXXXIII"))]

As a point of comparison `qrs'` doesn't use a pool of cross matched numerals of (p7 sr tr), and we 
can see that the last two candidates can be ruled out when considering the grid. 

ghci> qrs'
[((317,"CCCXVII"),(83,"LXXXIII")),((1741,"MDCCXLI"),(439,"CDXXXIX"))]

15. `check` function

The `fillDots` function above gets us most of the way there for implementing `check`. A slight refactor (indeed simplification) of the above logic 
allows for `check`.

\begin{code}
check :: Int -> Int -> Char -> Pattern
check n i c = foldl (\acc ix -> if i == ix then acc ++ [c]  else acc ++ ".") "" [0..n]
\end{code}

ghci> check 7 1 'C'
".C......"
ghci> check 7 0 'C'
"C......."
ghci> check 7 6 'C'
"......C."

16. 

\begin{code}
sevens :: [Pattern]
sevens = [check 7 x (p !! x) |  (x, p) <- [ (x,p) | x<-[1,6], p<-[sr,tr]]]

\end{code}

Here a nested list comprehension is used to gather all combinations of sr,tr and [1,6] (where 1, 6 are the indices of the crossing points to check). 
This is then patten matched in the encompassing list comprehension to pass every combination into the `check` function.  

ghci> sevens
[".C......",".C......","......I.","......I."]

As discussed above, coincidently both sr st and tr have the same characters at the first and sixth indices:

ghci> sr !! 6
'I'
ghci> tr !! 6
'I'
ghci> tr !! 1
'C'
ghci> sr !! 1
'C'

Hence the duplicate patterns seen.

17. qr values

Step 14. actually skipped ahead slightly and already answered this question by implementing the `crossMatch` with the equation itself:
ghci> qrs
[((317,"CCCXVII"),(83,"LXXXIII"))]

We can simply round this off with pattern matching:

\begin{code}
q,r :: Int
qr, rr :: Roman
((q, qr), (r, rr)) = qrs !! 0
\end{code}

ghci> q
317
ghci> qr
"CCCXVII"
ghci> r
83
ghci> rr
"LXXXIII"
ghci> 

We can confirm the workings but plugin the results for q, r back into the equation: 

ghci> q + 15 == 4 * r
True

STEP FOUR

18. Equation 4 - nps 

IIn = IIp + a + III

\begin{code}

nps :: [(Pair, Pair)]
nps = [(toPair n, toPair p) | n <- ns, p <- n6, 2 * n == 2 * p + a + 3]
    where ns = [n | (_,_,_, n) <- dtcns]
\end{code}


5. STEP FIVE

19. Equation 2 

e + f + g + h + k + VII = s + m

The choose algorithm with two recursive calls, one to move from left to right of 
the input list and one to accumulate all choices of length k from that subset.

e.g. given the list [a..e]

The problem can be expressed as:

choose' k scope rest ++ choose k rest

where choose' is a function call which which accumulates all choices of length k from a given scope and rest, 
and implements the following behaviour:

1. Pattern match s (r:rs:rss) (signifying the scope and the rest)
2. When length s == k, return s
3. where length s < k, increase the scope by adding the head of the rest (e.g. r)

N.b. (r:rs:rss) pattern matching is required rather than `head` / `tail` to avoid a 
'*** Exception: Prelude.head: empty list', exception, therefore we also need patterns 
to match the empty list and a list with fewer that three items (i.e. the counterpart to r:rs:rss)

E.g. the ['a'.. 'e'] is traversed in the following manner:

s       r   rs  rss
a       b   c   de  choose' k (a ++ [b]) cde
ab      c   d   e   choose' k (ab ++ [c]) de
abc     d   e   []  choose' k (abc ++ [d]) e
abcd    e   []  []  choose' k (abcd ++ [e]) []


\begin{code}
choose' :: Eq a => Int -> [a] -> [a] -> [[a]] 
choose' k s (r:rs:rss)
    | length s < k = choose' k (s ++ [r]) (rs:rss)  ++ choose' k s (rs:rss)
    | length s == k = [s] 
choose' k s (r:[])
    | length s == k = [s] 
    | otherwise =  choose' k (s ++ [r]) []
choose' k s []
    | length s == k = [s] 
    | otherwise = []

choose :: Eq a => Int -> [a] -> [[a]] 
choose k (x:xs) = choose' k [x] xs ++ choose k xs
choose k [] = []
    
\end{code}

ghci> choose 0 ['a'..'e']
[]
ghci> choose 1 ['a'..'e']
["a","b","c","d","e"]
ghci> choose 2 ['a'..'e']
["ab","ac","ad","ae","bc","bd","be","cd","ce","de"]
ghci> choose 3 ['a'..'e']
["abc","abd","abe","acd","ace","ade","bcd","bce","bde","cde"]
ghci> choose 4 ['a'..'e']
["abcd","abce","abde","acde","bcde"]
ghci> choose 5 ['a'..'e']
["abcde"]
ghci> choose 6 ['a'..'e']
[]

20. Equation 2

e + f + g + h + k + VII == s + m 
= e + f + g + h + k + VII == 944
= e + f + g + h + k == 937

The approach for this is as follows:

1. Find all candidates by first choosing 5 from n4 (all e..k exist in n4)
2. Then filter these to only those which satisfy the equation - this yields a list of list of integers

ghci> ns = filter (\x -> sum x == s + m - 7) (choose 5 n4)
ghci> ns
[[13,29,103,251,541],[13,53,211,251,409],[13,103,107,211,503],[29,53,103,211,541],[31,71,103,191,541],[31,71,103,211,521]]

3. We then need to map each of these to pairs. As we're trying to map the ints in the list, we actually need to map to a map.
This is achieved with currying and function application via `$` - `map (map toPair) $ ns`.  (http://learnyouahaskell.com/higher-order-functions#curried-functions)

ghci> map (map toPair) $ ns
[[(13,"XIII"),(29,"XXIX"),(103,"CIII"),(251,"CCLI"),
(541,"DXLI")],[(13,"XIII"),(53,"LIII"),(211,"CCXI"),
(251,"CCLI"),(409,"CDIX")],...]

The `$` application allows for right-associative function application, i.e. allowing us to apply the `toPair` call to the mapped values from ns. This is just 
syntactic sugar for using a lambda to achieve the same thing, e.g. `efghks = map (\x -> map toPair x) ns`, but it does provide convenience for effectively changing the order of 
precedence between function calls. For example:

gchi> (\x -> x * 2) $ 2 + 3
10
gchi> (\x -> x * 2) 2 + 3
7

ghci> map (\x -> map toPair x) ns == efghks 
True

\begin{code}
efghks :: [[Pair]]
efghks = map (map toPair) $ ns
    where ns = filter (\x -> sum x == s + m - 7) (choose 5 n4)
\end{code}

An alternative, cleaner implementation is possible if providing arithmetic operations on pairs. In this case there would be no need to map toPair to the intermediate output
as all operations could just be applied on the pairs. 

\begin{code}
(+.) :: Pair -> Pair -> Pair
(+.) (x, _) (y, _) = toPair (x + y)
\end{code}

ghci> p4 !! 0 +. (p4 !! 1)
(30,"XXX")
ghci> p4 !! 0
(13,"XIII")
ghci> p4 !! 1
(17,"XVII")

To fully implement this we'd want Pair to derive `num` and then declare all arithmetic operator for Pairs, but this partial implementation does give us enough to refactor the above 
code without the intermediate step:

\begin{code}
sum' :: [Pair] -> Pair
sum' (x:xs) =  x +. sum' xs
sum' [] = toPair 0

efghks' :: [[Pair]]
efghks' = filter (\x -> (sum' x) +. toPair 7 == (toPair s +. toPair m )) (choose 5 p4)
\end{code}

ghci> efghks'
[[(13,"XIII"),(29,"XXIX"),(103,"CIII"),(251,"CCLI"),(541,"DXLI")],
[(13,"XIII"),(53,"LIII"),(211,"CCXI"),(251,"CCLI"),(409,"CDIX")],
[(13,"XIII"),(103,"CIII"),(107,"CVII"),(211,"CCXI"),(503,"DIII")], 
[(29,"XXIX"),(53,"LIII"),(103,"CIII"),(211,"CCXI"),(541,"DXLI")],
[(31,"XXXI"),(71,"LXXI"),(103,"CIII"),(191,"CXCI"),(541,"DXLI")],
[(31,"XXXI"),(71,"LXXI"),(103,"CIII"),(211,"CCXI"),(521,"DXXI")]]
ghci> efghks' == efghks
True

STEP 6 

21. d into 15a

First we need to convert the potential `ds` into patterns which we can then use to check 
for cross matches with 15a. This is achieved by mapping each value of `ds` to a numeral, and then 
turning this into a pattern using the `fillDots` function, (n.b. the 1 passed into `fillDots` is the index at
which we know 15a crosses with 16d):

map (\y ->  fillDots (convertToNumeral y) 1 ) ds 
[".D..",".D.."]

We can then map each of these patterns against the `efghks` patterns. In the event that none fit, we've proven that these values neither value for d fits in 16d. 

      16d  
15a. -X--
      -
      -
      -

N.b 'X' above denotes the crossing point in the grid, not the character 'X'.


Therefore, 16.d needs to match the following pattern: 
gchi> layout $ check 3 0 'D'
'D'
'.'
'.'
'.'

Therefore we can say that for all of j in efghks, if there exists a j for which the 
zeroth character matches the first character of the pattern '.D..', then this combination of 
patterns is a potential solution for this match.

Conversely, if d were to be place in 16d, the cross patterns require a efghks with the first 
character matching the zeroth character of d:

gchi> map (\y ->  fillDots (convertToNumeral y) 0 ) ds 
["M...","M..."]

Meaning that a four character numeral  beginning with 'M' must exist in efghks for this ordering to work.

\begin{code}

fits :: Pattern -> Int ->  Pattern -> Int -> Bool 
fits x xi y yi = x !! xi == y !! yi

dfits15a :: Bool
dfits15a = any (==True) (map (\y -> fits a15s 1 y 0) d16s)
    where d16s = map (\(x, j) -> check 3 0 (j !! 0)) (nub $ concat efghks)
          a15s  = check 3 1 'D'

dfits16d :: Bool
dfits16d = any (==True) (map (\y -> fits d16s 0 y 1) a15s)
    where a15s = map (\(x, j) -> check 3 1 (j !! 1)) (nub $ concat efghks)
          d16s  = check 3 0 'M'
\end{code}

gchi> dfits15a
True
gchi> dfits16d 
False

22. m in 22a

Knowing that "CCCLXXIII" must occupy 1d meanings that in order for m to fit in 
3d there would have to exist a p in p5 which obeyed the pattern "C.D..". We can 
confirm this isn't the case quite simply as below:

\begin{code}
mfits3d :: Bool
mfits3d = not $ null [x | (_, x) <- p5,  match x "C.D.."]
\end{code}


23. efghks''

The list comprehension over the flattened `efghks` list shows that there fact only one entry that 
matches either "D.C." or "D.C.": 

gchi> [(x, y) | (x, y) <- nub $ concat efghks,  (match y "D.C." || match y "D.L.")]
[(541,"DXLI")]

As this is a list with just one item, we can simply plug it into a filter to rule out any members of `efghks` that do not contain this entry:

\begin{code}
efghks'' :: [[Pair]]
efghks'' = filter (\x -> p !! 0 `elem` x) efghks
    where p = [(x, y) | (x, y) <- nub $ concat efghks,  (match y "D.C." || match y "D.L.")]
\end{code}

gchi> efghks''
[[(13,"XIII"),(29,"XXIX"),(103,"CIII"),(251,"CCLI"),(541,"DXLI")],[(29,"XXIX"),(53,"LIII"),(103,"CIII"),(211,"CCXI"),(541,"DXLI")],[(31,"XXXI"),(71,"LXXI"),(103,"CIII"),(191,"CXCI"),(541,"DXLI")]]

Furthermore, this also gives us 16d and 20a and therefore 7a.

24. efghks'''

A very similar approach can be taken here:


\begin{code}
efghks''' :: [[Pair]]
efghks''' = [x | x <- efghks'', y <- cs, y `elem` x ]
    where cs = [(x, y) | (x, y) <- nub $ concat efghks,  match y ".C.."]
\end{code}

gchi> efghks'''
[[(13,"XIII"),(29,"XXIX"),(103,"CIII"),(251,"CCLI"),(541,"DXLI")],[(29,"XXIX"),(53,"LIII"),(103,"CIII"),(211,"CCXI"),(541,"DXLI")]]

STEP SEVEN

25. p into 9a

We can prove that p only fits into 9a by contradiction. Let us assume that p does fit into 19a if this were to be the case then the values crossing 
at 13d and 14d would match the patterns "..XX." and "..IIX" respectively (due to the crossing points from 20a). 
Therefore the absence of both of these patterns from `p5` would prove that p does not fit into 19a. 

This can be tested with the same logic as was previously used testing whether a pattern fits a space, but let's create a more general function for it.

\begin{code}
fitsSpace :: [Pair] -> Pattern -> Bool
fitsSpace  ps p = not $ null [x | (_, x) <- ps,  match x p]

fitsPatterns :: [Pair] -> [Pattern] -> Bool
fitsPatterns ps p = all (==True ) $ map (\x -> fitsSpace ps x) p

\end{code}

gchi> fitsPatterns p5 [".XXL", ".IIX"]
False

26. npdc

First let us remind ourselves of the of the pool of potential values for dtcns:

gchi> dtcns 
[(379,283,7,89),(469,283,7,179),(469,283,19,167),(379,283,59,37),(469,283,59,127)]

We now know that t is 283 and that n is one of 89, 179:

gchi> nps
[((89,"LXXXIX"),(37,"XXXVII")),((179,"CLXXIX"),(127,"CXXVII"))]

We can therefore further eliminate some of the combinations from `dtcns`: 

\begin{code}
dtcns' :: [(Int, Int, Int, Int)]
dtcns' = [(d,t,c,n) | (d,t,c,n)  <- dtcns, n `elem` [89, 179]]

\end{code}

gchi> dtcns'
[(379,283,7,89),(469,283,7,179)]

Now we've narrowed down `dtcns` once find which n fits the space in 19a we have therefore solved all of these values 
and p (as p must therefore be the corresponding p in the `nps` to which the correct n belongs). 

To find the correct n, we can reuse exactly the same logic as in the previous step as we know that whatever value fits in 19a must 
also cross match with the patterns at 17d and 18d. 

Therefore one for the numerals "LXXXIX", "CXXVII" must have corresponding matches in `p5`. 

From "LXXXIX" the overlapping patterns at 13a and 14a would be ["..XX.", "..XIX"], and can confirm that there is indeed a match for both of these crossovers within `p5`:

gchi> fitsPatterns p5 ["..XX.", "..XIX"]
True

This doesn't yet rule out "CXXVII", so to confirm that the only possible solution for `dtcns` is (379,283,7,89) we can plug in the alternative patterns:

gchi> fitsPatterns p5 ["..XX.", "..IIX"]
False

Therefore, `dtcns` must equal (379,283,7,89). Having deduced that n = 89, we know therefore that p must be 37 (recall `nps = [((89,"LXXXIX"),(37,"XXXVII")),((179,"CLXXIX"),(127,"CXXVII"))]`). 

STEP EIGHT

27. 

\begin{code}

p3'' :: [Pair]
p3'' = filter (\(_, x) -> not ('M' `elem` x || 'D' `elem` x)) p3


pats:: [Pattern]
pats = ["..X", "V..", "...", "..X", "I.I", "LX.", "..I", ".IX"]

\end{code}

gchi> p3''
[(3,"III"),(7,"VII"),(19,"XIX"),(41,"XLI"),(59,"LIX"),(61,"LXI"),(109,"CIX"),(151,"CLI")]


28. 

Various implementations for this were considered such as the common solution of swapping character at index i,j whilst traversing the input in a recursive function:

1. Starting from the first character, swap it with each possible character in the string. 
2. Repeat starting with the the next character 
3. Once we reach the final character of the string there are no more swaps to be made - return the values.

Or Heap's algorithm which switches items in the input depending on whether the current iteration through the input is an odd or even number.

These approaches were rejected as they didn't seem to be the most functional in nature. That is to say reconstructing the input list by swapping indexes but leaving the rest untouched seems a functional antipattern 
due to the requirement of data mutability; any attempt to do this in an immutable way would just require more temporary storage and would ultimately feel like working around the problem.

Instead a similar blueprint to the `choose` algorithm was followed, using the idea of finding the permutations of the scope and then the permutations of the rest. 

1. Swap character 0 with all other characters (including itself) in the input
2. For each of these subsets, perms = x ++ perms xs
3. When the acc == length input, return the acc.


\begin{code}

-- Not currently working - infinite type error
--perms :: [a] -> [[a]]
--perms (x:xs) =  [[x] ++ perms xs | (x:xs) <-ps, not $ null xs]
    --[[x] ++ swap i xs | (i, (x:xs)) <- zip [0..length $ ps] ps]
 --   where ps = [swap i $ x:xs | i <- [0..length xs]]
--perms [] = [[]]


--perms' (x:xs) acc  
--    | length acc == length x:xs = acc
--    | other

swap :: Int -> [a] -> [a]
swap i (x:xs) = [snd $ z !! i] ++ smaller ++ rest
    where smaller = [x | (j, x) <- z, j < i ]
          rest = [x | (j, x) <- z, j > i ]
          z = zip [0..length $ x:xs] (x:xs) 


\end{code}

N.b. Unfortunately, Due to time constraints, I was unable to fully implement the algorithm and so have used the standard `Data.List.permutations` for the following questions.

29. 

As there are n! permutations for a given input time complexity is important for this predicate. 
For a given permutation of the values of p3'' we need to check each againsts it's corresponding pattern, however we 
do not need to check every single pattern. As all permutations need to match with a pattern, if any of the patterns do not match 
we can immediately return False for that grouping; only exhausting the search space when all patterns do match a corresponding set of permutations.

This is a prime example of the benefit of haskell's lazily evaluation - in an eagerly evaluated language the zip operation of would require n! space as all of the 'zipping'
would be performed ahead of running the `ok'` function (i.e. constructing the full [(Pair, Pattern)]...) for all of `ps`. Here the zip is only subsequently evaluated in ok' 
after the pattern matching has occurred.


\begin{code}

ok :: [Pair] -> Bool
ok ps = ok' $ zip ps pats

ok' :: [(Pair, Pattern)] -> Bool
ok' (((_, p), pat):rest)  -- pattern match [((3,"III"),"..X"),((7,"VII"),"V.."),((19,"XIX"),"...")...]
    | match p pat = ok' rest
    | otherwise = False
ok' [] = True 

\end{code}

gchi> ok p3''
False

We can now use the predicate to simply filter the results for matching permutations:


gchi> filter (ok) $  permutations p3''
[[(19,"XIX"),(7,"VII"),(41,"XLI"),(59,"LIX"),(3,"III"),(61,"LXI"),(151,"CLI"),(109,"CIX")],
[(59,"LIX"),(7,"VII"),(41,"XLI"),(19,"XIX"),(3,"III"),(61,"LXI"),(151,"CLI"),(109,"CIX")],
[(59,"LIX"),(7,"VII"),(151,"CLI"),(19,"XIX"),(3,"III"),(61,"LXI"),(41,"XLI"),(109,"CIX")],
[(19,"XIX"),(7,"VII"),(151,"CLI"),(59,"LIX"),(3,"III"),(61,"LXI"),(41,"XLI"),(109,"CIX")],
[(109,"CIX"),(7,"VII"),(151,"CLI"),(59,"LIX"),(3,"III"),(61,"LXI"),(41,"XLI"),(19,"XIX")],
[(59,"LIX"),(7,"VII"),(151,"CLI"),(109,"CIX"),(3,"III"),(61,"LXI"),(41,"XLI"),(19,"XIX")],
[(59,"LIX"),(7,"VII"),(41,"XLI"),(109,"CIX"),(3,"III"),(61,"LXI"),(151,"CLI"),(19,"XIX")],
[(109,"CIX"),(7,"VII"),(41,"XLI"),(59,"LIX"),(3,"III"),(61,"LXI"),(151,"CLI"),(19,"XIX")],
[(109,"CIX"),(7,"VII"),(151,"CLI"),(19,"XIX"),(3,"III"),(61,"LXI"),(41,"XLI"),(59,"LIX")],
[(19,"XIX"),(7,"VII"),(151,"CLI"),(109,"CIX"),(3,"III"),(61,"LXI"),(41,"XLI"),(59,"LIX")],
[(19,"XIX"),(7,"VII"),(41,"XLI"),(109,"CIX"),(3,"III"),(61,"LXI"),(151,"CLI"),(59,"LIX")],
[(109,"CIX"),(7,"VII"),(41,"XLI"),(19,"XIX"),(3,"III"),(61,"LXI"),(151,"CLI"),(59,"LIX")]]
gchi> length (filter (ok) $  permutations p3'')
12

STEP NINE 

30. efghk values 

We can deduce the values for efghk by first filtering out all of those which contain the now eliminated "LIII" numeral, and the applying further logic from the already
completed grid. 

filter  (\x -> not $ (53,"LIII") `elem` x) efghks'' 
[[(13,"XIII"),(29,"XXIX"),(103,"CIII"),(251,"CCLI"),(541,"DXLI")],[(31,"XXXI"),(71,"LXXI"),(103,"CIII"),(191,"CXCI"),(541,"DXLI")]]

We already know that 18d fits the pattern "..IX" which we can use as the next filter.


\begin{code}
e,f,g,h,k :: Int
[(e, er), (f, fr), (g, gr), (h, hr), (k,kr)] = [x | x <- filter (\x -> not $ (53,"LIII") `elem` x) efghks'', fitsPatterns x ["..IX"]] !! 0
\end{code}

gchi> [(e, er), (f, fr), (g, gr), (h, hr), (k,kr)]
[(13,"XIII"),(29,"XXIX"),(103,"CIII"),(251,"CCLI"),(541,"DXLI")]


31. 

The first remaining entries are trivial to find:

\begin{code}

find4 p = [(x, y) | (x, y) <- fours, match y p]
    where fours = [(13,"XIII"),(29,"XXIX"),(103,"CIII"),(251,"CCLI"),(541,"DXLI")]

a2d = find4 ".C.."
--[(251,"CCLI")]

a18d = find4 "..IX"
-- [(29,"XXIX")]

\end{code}

3d, isn't quite as simple using this same method as there are still four potential results at this stage:

gchi> a3d = [(x, y) | (x, y) <- p5, match y ".CX.."]
gchi> a3d
[(241,"CCXLI"),(619,"DCXIX"),(641,"DCXLI"),(691,"DCXCI")]

However knowing that 1a matches "CC..." we can easily find the correct answer (and indeed 1a). 

\begin{code}
find' xs pats = filter (\x -> fitsPatterns [x] pats) xs
a3d = find' p5 [".CX..", "CC..."]
-- [(311,"CCCXI")]

-- We can add an extra 'c' to this pattern now that 3d is filled to find 1a: 
a1a = find' p5 ["CCC.."]
-- [(311,"CCCXI")]

a4d = find' p5 [".XV.."]
-- [(67,"LXVII")]

a13ds = find' p5 ["..XX."]

\end{code}

The cross of 13d, 13a and 11d have to be found together as they are so interlinked. Using the same approach above 
show there are still multiple results possible for 13a and 13d which satisfy both space:

gchi> a13ds = find' p5 ["..XX."]
gchi> a13ds
[(131,"CXXXI"),(421,"CDXXI"),(571,"DLXXI"),(1031,"MXXXI")]

gchi> find' p3 ["L.I"]
[(61,"LXI")]
gchi> find' p3 ["M.I"]
[(1051,"MLI")]
gchi> find' p3 ["C.I"]
[(151,"CLI"),(401,"CDI")]

So only by introducing 11d can we solve all three spaces:

\begin{code}
a13as = nub $ concat [x | x <- (map (\p -> find' p3 [p]) (map (\(x, y) -> (take 2 $ fillDots y 0 )++ "I") a13ds)), not (null x)]
-- [(151,"CLI"),(401,"CDI"),(601,"DCI"),(1051,"MLI")]
\end{code}

In `a13as`  the  `(map (\(x, y) -> (take 2 $ fillDots y 0 )++ "I") a13ds)`` is used to generate a list of patterns to match 13a, and which are then in turned mapped to 
the find' prime function. 

gchi> (map (\(x, y) -> (take 2 $ fillDots y 0 )++ "I") a13ds)
["C.I","C.I","D.I","M.I"]

gchi> a13as
[(61,"LXI"),(151,"CLI"),(401,"CDI"),(1051,"MLI")]

We can then build the matching patterns for 11d in a similar way from `a13as` potential solutions and then feed this back into filter the search:

\begin{code}
a11ds =  nub $ concat [x | x <- (map (\p -> find' p3 [p]) [[y !! 0] ++ "." ++ [y !! 2] | (_, y) <-a13as ]), not (null x)]
-- [(151,"CLI"),(401,"CDI"),(601,"DCI"),(1051,"MLI")]

a11as = nub $ concat [x | x <- (map (\p -> find' p4 [p]) [[y !! 0] ++ "I.." | (_, y) <- a11ds ]), not (null x)]
-- [(103,"CIII"),(503,"DIII")]

\end{code}

This still yields multiple possible solutions, so we will need to broaden our search to include 5d. As it happens all of the potential solutions for 11d end in "I", 
so we know that the answer for 5d must match ".III".

\begin{code}
a5ds = find' p4 [".III"]
-- [(13,"XIII"),(53,"LIII"),(103,"CIII"),(503,"DIII")]
\end{code}

We're slightly closer, but there are still multiple solutions for all positions currently. Let's remind ourselves of all the values in the search space: 

gchi> a13ds
[(131,"CXXXI"),(421,"CDXXI"),(571,"DLXXI"),(1031,"MXXXI")]
gchi> a13as
[(151,"CLI"),(401,"CDI"),(601,"DCI"),(1051,"MLI")]
gchi> a11ds
[(151,"CLI"),(401,"CDI"),(601,"DCI"),(1051,"MLI")]
gchi> a11as
[(103,"CIII"),(503,"DIII")]
gchi> a5ds
[(13,"XIII"),(53,"LIII"),(103,"CIII"),(503,"DIII")]

Note that a13as and a11ds fit the same numerals.

Let us assume that a13d = (131,"CXXXI")
- In this case a13a must either (151,"CLI"),(401,"CDI").
- We can rule out "CDI" as there would be no corresponding ".D." pattern in a11ds. In fact we can go further, and say 
that the only two patterns that share a central character in a11ds (which is the same set as a13as) are (151,"CLI"), (1051,"MLI"). 
This means that these two must occupy these spaces, but we don't yet know the order.

Therefore. we know now that 13a in fact has to fit ".LI" we can plug this back into a13ds apply further filtering.  

gchi> find' a13as [".LI"]
[(151,"CLI"),(1051,"MLI")]

\begin{code}

a13as' = find' a13as [".LI"]

a13ds' = map (\x -> find' a13ds [x]) ["CXX", "MXX"]
-- [[(131,"CXXXI")],[(1031,"MXXXI")]]
\end{code}

Going back to 13a, whichever of [(151,"CLI"),(1051,"MLI")] it is, 11d is the other. We can use this to match 11a.

Assuming 13a = [(151,"CLI")], then 11d = [(1051,"MLI"], which means that 11a must match "MI.."

\begin{code}
a11as' = map (\x -> find' a11as [x]) ["CI..", "MI.."]
-- [[(103,"CIII")],[]]
\end{code}

We can see now that "CIII" is the only possible solution for 11a. Let's now focus back on 13d, as it should fit "M.XX."

\begin{code}
a13d = find' p5 ["M.XX."]
-- [[(1031,"MXXXI")]]
\end{code}

Great - we're getting there. In this case, 15 should match ".DXI"

\begin{code}
a15a = find' p4 [".DXI"]
-- [[(1511,"MDXI")]]
\end{code}

Everything now falls into place for this section. The only piece remaining is 5d, which we know must match ".III". All of the potential solutions found for 5d do 
fit this pattern, so to help us narrow it down we need to consider 5a, and in turn 6d. As (101,"CI") has already been filled in 20d, know that 6a must be one of 
[(2,"II"),(11,"XI")]. We can now map this to 5a along with the potential solution to 5d to fill these slots.

We've used a (CI), but not yet b (XI), therefore we can deduce that 6d must be b, In which case 5a must match "..X"

\begin{code}
-- pattern for matching 5a
a5as = map (\x -> find' p3 [x] ) (nub [[x !! 0] ++ "." ++ [y !! 1] | (_, x) <- a5ds, (_, y) <- take 2 p2])
\end{code}

The following are all trivial to find:

gchi> a14a = find' p5 ["L.XIX"]
gchi> a14a
gchi> a14a
[(79,"LXXIX")]
gchi> a8d = find' p3 ["LX."]
gchi> a8d
[(61,"LXI")]
gchi> a12a = find' p3 ["V.I"]
gchi> a12a
[(7,"VII")]
gchi> a21a = find' p3 ["I.I"]
gchi> a21a
[(3,"III")]

I was unable to find unique solutions for the remain 3 tiles as there was a large cross over in the search space between them, clearly there was a mis-step here somewhere but due to time constraints I was unfortunately not able to complete the solution.

gchi> find' p3 ["..X"]
[(19,"XIX"),(59,"LIX"),(109,"CIX"),(509,"DIX"),(1009,"MIX")]
gchi> b
11
gchi> find' p4 [".III"]
[(13,"XIII"),(53,"LIII"),(103,"CIII"),(503,"DIII")]
gchi> a17d
[(19,"XIX"),(59,"LIX"),(109,"CIX"),(509,"DIX"),(1009,"MIX")]
gchi> map (\x -> find' p3 [x] ) (nub [[x !! 0] ++ "." ++ [y !! 1] | (_, x) <- a5ds, (_, y) <- take 2 p2])
[[(41,"XLI")],[(61,"LXI")],[(151,"CLI"),(401,"CDI")],[(601,"DCI")]]


Bibliography

https://wiki.haskell.org/Anonymous_function
http://zvon.org/other/haskell/Outputprelude/takeWhile_f.html
https://www.cs.hmc.edu/~oneill/papers/Sieve-JFP.pdf
https://wiki.haskell.org/index.php?title=Prime_numbers&oldid=36858#Postponed_Filters_Sieve
http://learnyouahaskell.com/making-our-own-types-and-typeclasses#type-synonyms
http://learnyouahaskell.com/modules#data-list
https://stackoverflow.com/questions/33394756/haskell-function-length-doesnt-work-with-custom-data-type
https://hackage.haskell.org/package/base-4.14.1.0/docs/Data-List.html#v:nub
https://hackage.haskell.org/package/base-4.14.1.0/docs/Prelude.html#v:drop
https://hackage.haskell.org/package/base-4.14.1.0/docs/Data-List.html#v:tails
http://learnyouahaskell.com/higher-order-functions#curried-functions
https://hackage.haskell.org/package/base-4.14.1.0/docs/GHC-List.html#v:concat
http://zvon.org/other/haskell/Outputprelude/any_f.html

