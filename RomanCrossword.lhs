\begin{code}
import Data.List
import Data.Function
--import qualified Data.Set as Set  
\end{code}

ghci RomanCrossword.lhs

PART 0

Symbol	I	V	X	L	C	D	M
Value	1	5	10	50	100	500	1000

1. Convert Roman numerals to any positive integer up to 3999

The solution is based on the realisation that Roman numerals can be viewed as a 
point between lower, mid and upper symbols, where the magnatude of the number defines
the subset of symbols. From this we can see the following pattern is always obeyed in the
standard system:  (L)+++-M+++-H. Where L, M, H are a subset of symbols from set of numerals. 
This can also be written as 

N<3  | N=4  | N=5 | N<9 & N>5 | N=9
L*N, |LM,   | M   | M+(d*L)   | L-H, 

N is the number being converted, and d := the difference between the number and 
the mid point of the range (i.e. 5).

N.b. In contiguous magnatudes, the L of the second set is neccasarliy the H of the preceeding set. 

When viewed in this way we can see that the numeral symbols can be grouped with the magnatude for 
which they are bounds as follows: 

Units: "IVX"
Tens: "XLC"
Hundreds: "CDM"
Thousands: "M"

Note, that thousands only has a lower bound, hence the invarient that 3999 is the largest number that 
can be represented in this system. 

The elegance of this number system is that the L*N, LM, M, M + (d*L) L-H desribed above holds at the 
micro and macro level, meaning that we can utalise it to convert every digit of a number, and then simply contatonate the results 
back together E.g. 

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
3. Concatonate the resulting list of Strings together for the final output: 
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
2. Appearing in three entries, meaning that each appear seperately from each other
3. All entries are > three characters long

The upper bound can be deduced logically by first working out the lowest and highest possible values in a searchspace if we were going to use a brute force approach. 
We know that the upper bound must contain an M, so the lower bound is at least > 1000. Conversly, we know from axiom 2 that the three characters are split over seperate entries, 
meaning that an "MD" combination is not possible. Therefore we know that the upperbound must be less than 1400 as this is where MD pairing first appear. Therefore the upper bound is the 
highest entry > three characters between 1000..1399. This actually turns out to be the maximum of this range, 1399, "MCCCXCIX". 

\begin{code}

upperBound = fst (last  [(x,  numeral) | x <- [1000..1399], let numeral = convertToNumeral x, isPrime x && length numeral > 3 && 'M' `elem` numeral  && not ('D' `elem` numeral )])

\end{code}

We can make this a lot more efficient by starting at the upper limit for the upper bound and working backwards if all axiom predicates are not met: 

\begin{code}
upperBound' :: Int
upperBound' = f 1399

f :: Int -> Int
f x
    | predicates = x
    | otherwise = f (x - 1)
    where numeral = convertToNumeral x
          predicates = (isPrime x && length numeral > 3 && 'M' `elem` numeral  && not ('D' `elem` numeral ))

\end{code}

Note, this above implemention works before we've already deduced that the upper limit for the upper bound is 1399, therefore the algorithm is relying on the hard coded 
`upperBound' = f 1399`. For example if we change this line to `upperBound' = f 3999` the algorithm would fail as it fails to take into account only axiom 2, i.e. multiple 'M' are 
not explictly disallowed. If we wanted to abstract away some of the brain work and make this an entirely bruteforce approach that didn't rely on the inital hardcoded upper limit we 
would have to check only instance of the letter occurs in the match. 

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


This implemention confirms that our inital non bruteforce approachs were indeed correct:

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
to simple find the largest three character prime containing only one 'M'.  

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

For this problem the 'Sieve of Eratosthenes' is used to filter identify primes. 
Turner (1975) is attributed to defining a functional implemention of the Sieve. 
In the Sieve algorithm, whenever a prime is identify all multiples of that prime can
be removed ('sieved') out of the search space for possible primes, as it is known that they are 
divisable by the at least the identified prime. 

Turner's implemention has been shown to be suboptimal asymtopically (https://www.cs.hmc.edu/~oneill/papers/Sieve-JFP.pdf).
O'Neill (2009), brands the implemention as the 'unfaithful Sieve' arguing it is not an accurate 
translation of the Seive as described by Eratosthenes (due to how the non-primes are elimated immediately after primes are found, 
rather than lazily and starting from the primes' square and working back towards the prime (O'Neill (2009))). 

O'Neill instead presents the 'genuine Seive of Eratosthenes' as follows, (n.b. this is slightly altered to handle x <= 1):

\begin{code}
primes = 2 : [x | x <- [3..], isPrime x]
isPrime x 
    | x <= 1 = False
    | otherwise = all (\p -> x `mod` p > 0) (factorsToTry x)
    where factorsToTry x = takeWhile (\p -> p*p <= x) primes
\end{code}

algorithm works as follows:

primes := the list of all numbers which satify the predicate `isPrime`
isPrime:= Uses `all` and a lambda function to check that all values `p` of the iterable `factorsToTry` modulo x are greater 1.
factorsToTry:= uses a takewhile loop to iterate all ps in primes that are <= x, starting from p squared.
E.g. factorsToTry 17 is equal to [2,3]. 

This is a beautiful implemention in haskell as both `primes` and `factorsToTry` reference each other in their definitions, meaning that
the lazy evaluation properties of haskell are put to optimum use as the `primes` infinite list is being dynamically evaluated up to x just 
at the point it is required for computation.

-- TODO: Maybe reimplement the algo?

https://www.cs.hmc.edu/~oneill/papers/Sieve-JFP.pdf
https://wiki.haskell.org/index.php?title=Prime_numbers&oldid=36858#Postponed_Filters_Sieve

\begin{code}
data Roman = Roman String deriving (Show, Eq, Ord)
type Pair = (Int, Roman) -- TODO: make work with Integer as per spec!

boundedPrimes :: [Pair]
boundedPrimes = [(x, Roman (convertToNumeral x)) | x <- [2..upperBound'''], isPrime x]

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
    | otherwise = [(i, Roman numeral) | i <- [1..upperBound], let numeral = convertToNumeral i, length numeral == x && isPrime i]
\end{code}


This implemention works fine, however the issue with it is that for any value of i all numerals are checked. We could say that
it is not really in the spirit of haskell, as the `numerals` list is greedily computed and exhaustively checked everytime the `numeralsOfLength`
function is called. A better solution is to lazily group the numerals by their length and then retrieve just the relevent grouping.

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
          l = (length' . snd)

length' :: Roman -> Int
length' (Roman x) = length x
\end{code}

Note, we have to implement a custom length' function to work  on numerals, this  is because the type signature 
for the inbuilt length is `length :: Foldable t => t a -> Int`. As the Roman type is not 
a foldable, we need handle only running length on the numeral String of the Roman, not the Roman itself. Attempting to do so results in: 
` Couldn't match expected type ‘[a0]’ with actual type ‘Roman’` 
https://stackoverflow.com/questions/33394756/haskell-function-length-doesnt-work-with-custom-data-type

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

p2 = [(2,Roman "II"),(11,Roman "XI"),(101,Roman "CI")]

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
          toPair z = (snd z, Roman (convertToNumeral (snd z)))
\end{code}

E.g. `candidatePairs' n2` returns the following List of tuples of Pairs: 
[((2,Roman "II"),(11,Roman "XI")),((2,Roman "II"), ...]

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
manage is to pass in the value 0 to `toPair`(e.g. (0,Roman "")) and then filter these values from the output.


\begin{code}
sts:: [(Pair, Pair)]
sts = map toTup res
    where xs = n9
          res = filter (notEmptyList) (notZero (concat [d x [[toPair 0, toPair 0]] | x <- [slice s xs | s <- [0..length xs -1]]])) -- 0
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
toPair x = (x, Roman (convertToNumeral x))

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

Therefore we can plug the value for t into the equation. We can simplify the right hand side of the equation and to find possible values for c,n:

d - Vt = c + n 

1. Iterate the possible values for d. 
2. Iterate possible iterate value of c + n to find those which = d - vt. 

Note, a optimisation making use of transitivity is possible in a similar manner to question 6, but in this case the simple solution has been favoured as the 
n * m inputs list (n3, n6) are much smaller so in this case simplicity can be favoured over optimisation.


\begin{code}
dtcns::[(Int, Int,Int, Int)]
dtcns = [(t+c+n, t,c,n) | c <- n3, n <- n6, let cn = c+n, let t = (fst (fst (sts !! 0))),  cn `elem` [d - t * 5 | d <- ds]]
\end{code}

In the above list comprehension, the second nest list comprehension of all values of ds - Vt is created, then for possible all values v of c+n, if v is in that list 
then the value of t+c+n is a potential solution for d.

ghci> dtcns
[(379,283,7,89),(469,283,7,179),(469,283,19,167),(379,283,59,37),(469,283,59,127)]


