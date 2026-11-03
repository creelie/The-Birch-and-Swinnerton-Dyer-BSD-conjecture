/-! Finite arithmetic behind the Sha[p] = 0 certificates: Frobenius traces by counting points,
the Serre--Dickson surjectivity witnesses, good ordinary reduction, and rational points.
Everything is decided by the kernel (`decide +kernel`); no axioms beyond `propext` are used. -/

namespace BSDCert

/-- `b ^ e mod m` by repeated squaring (structural recursion on a fuel bound). -/
def powModF : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, m => 1 % m
  | f + 1, b, e, m =>
    if e = 0 then 1 % m else
      let t := powModF f (b * b % m) (e / 2) m
      if e % 2 = 1 then t * b % m else t

def powMod (b e m : Nat) : Nat := powModF 64 b e m

/-- Legendre symbol of `a` modulo an odd prime `q`, as 0, 1 or -1. -/
def leg (a : Int) (q : Nat) : Int :=
  let r := (a % q).toNat
  if r = 0 then 0 else if powMod r ((q - 1) / 2) q = 1 then 1 else -1

/-- Number of affine points of `y^2 + a1 x y + a3 y = x^3 + a2 x^2 + a4 x + a6` over `F_q`, `q` odd:
completing the square gives `(2y + a1 x + a3)^2 = g(x)`. -/
def affCount (a1 a2 a3 a4 a6 : Int) (q : Nat) : Int :=
  (List.range q).foldl (fun (s : Int) (x : Nat) =>
    let x : Int := x
    let g := 4 * (x ^ 3 + a2 * x ^ 2 + a4 * x + a6) + (a1 * x + a3) ^ 2
    s + 1 + leg g q) 0

/-- Number of affine points by direct search (used for `q = 2`). -/
def bruteCount (a1 a2 a3 a4 a6 : Int) (q : Nat) : Int :=
  (List.range q).foldl (fun (s : Int) (x : Nat) => (List.range q).foldl (fun (s : Int) (y : Nat) =>
    let x : Int := x
    let y : Int := y
    if (y ^ 2 + a1 * x * y + a3 * y - (x ^ 3 + a2 * x ^ 2 + a4 * x + a6)) % q = 0 then s + 1 else s) s) 0

/-- Trace of Frobenius `a_q = q + 1 - #E(F_q)` (the point at infinity counted once). -/
def ap (a1 a2 a3 a4 a6 : Int) (q : Nat) : Int :=
  q - (if q = 2 then bruteCount a1 a2 a3 a4 a6 q else affCount a1 a2 a3 a4 a6 q)

/-- Discriminant of the Weierstrass model. -/
def disc (a1 a2 a3 a4 a6 : Int) : Int :=
  let b2 := a1 ^ 2 + 4 * a2
  let b4 := 2 * a4 + a1 * a3
  let b6 := a3 ^ 2 + 4 * a6
  let b8 := a1 ^ 2 * a6 + 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3 ^ 2 - a4 ^ 2
  9 * b2 * b4 * b6 - b2 ^ 2 * b8 - 8 * b4 ^ 3 - 27 * b6 ^ 2

def isPrime (n : Nat) : Bool :=
  n ≥ 2 && (List.range n).all (fun d => d < 2 || d * d > n || n % d != 0)

def md (a : Int) (p : Nat) : Nat := (a % p).toNat

/-- `q1`: `a_q ≠ 0` and `a_q^2 - 4q` a non-square mod `p`. -/
def w1 (a : Int) (q p : Nat) : Bool :=
  md a p != 0 && leg (a * a - 4 * q) p == -1
/-- `q2`: `a_q ≠ 0` and `a_q^2 - 4q` a nonzero square mod `p`. -/
def w2 (a : Int) (q p : Nat) : Bool :=
  md a p != 0 && leg (a * a - 4 * q) p == 1
/-- `q3`: `u = a_q^2/q ∉ {0,1,2,4}` and `u^2 - 3u + 1 ≠ 0` mod `p`. -/
def w3 (a : Int) (q p : Nat) : Bool :=
  let u := md (a * a) p * powMod (q % p) (p - 2) p % p
  u != 0 && u != 1 && u != 2 && u != 4 && (u * u + 1 + 3 * (p - 1) * u) % p != 0

/-- Full certificate for one prime `p`: `p ≥ 5` prime of good ordinary reduction, and three
primes of good reduction `q_i ≠ p` that are the Frobenius witnesses of surjectivity. -/
def certP (a1 a2 a3 a4 a6 : Int) (p q1 q2 q3 : Nat) : Bool :=
  let D := disc a1 a2 a3 a4 a6
  let good (q : Nat) := isPrime q && md D q != 0
  p ≥ 5 && good p && md (ap a1 a2 a3 a4 a6 p) p != 0 &&
  good q1 && good q2 && good q3 && q1 != p && q2 != p && q3 != p &&
  w1 (ap a1 a2 a3 a4 a6 q1) q1 p && w2 (ap a1 a2 a3 a4 a6 q2) q2 p &&
  w3 (ap a1 a2 a3 a4 a6 q3) q3 p

/-- A projective point `[x : y : z]` with `z ≠ 0`, in the integral form `(x/z, y/z)`, lies on the curve
(cleared of denominators; generators in Cremona's tables have `z` a cube). -/
def onCurve (a1 a2 a3 a4 a6 x y z : Int) : Bool :=
  z != 0 &&
  y ^ 2 * z + a1 * x * y * z + a3 * y * z ^ 2 == x ^ 3 + a2 * x ^ 2 * z + a4 * x * z ^ 2 + a6 * z ^ 3

/-- Certificate at a supersingular prime `p ≥ 5`: good reduction, `a_p = 0`, and the three witnesses. -/
def certSS (a1 a2 a3 a4 a6 : Int) (p q1 q2 q3 : Nat) : Bool :=
  let D := disc a1 a2 a3 a4 a6
  let good (q : Nat) := isPrime q && md D q != 0
  p ≥ 5 && good p && ap a1 a2 a3 a4 a6 p == 0 &&
  good q1 && good q2 && good q3 && q1 != p && q2 != p && q3 != p &&
  w1 (ap a1 a2 a3 a4 a6 q1) q1 p && w2 (ap a1 a2 a3 a4 a6 q2) q2 p &&
  w3 (ap a1 a2 a3 a4 a6 q3) q3 p

/-- All certificates of one curve: a list of `(p, q1, q2, q3)`. -/
def certAll (a1 a2 a3 a4 a6 : Int) (l : List (Nat × Nat × Nat × Nat)) : Bool :=
  l.all (fun ⟨p, q1, q2, q3⟩ => certP a1 a2 a3 a4 a6 p q1 q2 q3)

/-- All points `[x : y : z]` lie on the curve. -/
def allOn (a1 a2 a3 a4 a6 : Int) (l : List (Int × Int × Int)) : Bool :=
  l.all (fun ⟨x, y, z⟩ => onCurve a1 a2 a3 a4 a6 x y z)

end BSDCert

open BSDCert

-- 30064c1: 23 primes
set_option maxHeartbeats 0 in
theorem c30064c1_cert0 : certAll 0 1 0 (-152) 676 [(5, 3, 7, 3), (7, 3, 17, 3), (11, 13, 3, 7), (13, 3, 19, 3), (17, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 13, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c30064c1_cert1 : certAll 0 1 0 (-152) 676 [(47, 3, 5, 3), (53, 3, 5, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 7, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 17, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c30064c1_gens : allOn 0 1 0 (-152) 676 [(6, 4, 1), (8, 6, 1), (7, 2, 1)] = true := by decide +kernel

-- 30148b1: 22 primes
set_option maxHeartbeats 0 in
theorem c30148b1_cert0 : certAll 0 0 0 (-37) 85 [(5, 3, 17, 3), (7, 5, 3, 3), (11, 3, 19, 3), (13, 23, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 29, 3, 3), (43, 5, 3, 3), (47, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c30148b1_cert1 : certAll 0 0 0 (-37) 85 [(53, 3, 5, 3), (59, 3, 11, 3), (61, 11, 3, 3), (67, 5, 3, 3), (71, 3, 23, 3), (73, 11, 3, 3), (79, 5, 3, 3), (83, 3, 23, 3), (89, 3, 5, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c30148b1_gens : allOn 0 0 0 (-37) 85 [(3, 1, 1), (5, 5, 1), (4, 1, 1)] = true := by decide +kernel

-- 30376a1: 21 primes
set_option maxHeartbeats 0 in
theorem c30376a1_cert0 : certAll 0 1 0 (-25) (-21) [(5, 3, 7, 3), (7, 3, 29, 3), (11, 5, 3, 7), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 13, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c30376a1_cert1 : certAll 0 1 0 (-25) (-21) [(53, 3, 5, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 13, 3), (73, 13, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 13, 3, 3)] = true := by decide +kernel
theorem c30376a1_gens : allOn 0 1 0 (-25) (-21) [((-1), 2, 1), ((-5), 2, 1), ((-3), 6, 1)] = true := by decide +kernel

-- 30446a1: 21 primes
set_option maxHeartbeats 0 in
theorem c30446a1_cert0 : certAll 1 1 0 (-39) (-59) [(5, 17, 3, 17), (7, 3, 19, 3), (11, 7, 17, 17), (17, 3, 11, 3), (19, 3, 7, 3), (23, 7, 3, 3), (29, 3, 11, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 17, 3), (43, 3, 7, 3), (47, 7, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c30446a1_cert1 : certAll 1 1 0 (-39) (-59) [(53, 7, 3, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 11, 3, 3), (71, 7, 3, 3), (73, 3, 7, 3), (83, 3, 11, 3), (89, 7, 3, 3), (97, 31, 3, 3)] = true := by decide +kernel
theorem c30446a1_gens : allOn 1 1 0 (-39) (-59) [((-3), 8, 1), (10, 21, 1), ((-5), 9, 1)] = true := by decide +kernel

-- 30487a1: 19 primes
set_option maxHeartbeats 0 in
theorem c30487a1_cert0 : certAll 0 0 1 (-28) (-15) [(5, 3, 13, 3), (7, 11, 3, 3), (11, 3, 5, 3), (13, 5, 3, 3), (17, 3, 5, 3), (19, 11, 3, 3), (23, 3, 5, 3), (29, 3, 13, 3), (31, 5, 3, 3), (41, 3, 11, 3), (47, 3, 5, 3), (53, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c30487a1_cert1 : certAll 0 0 1 (-28) (-15) [(61, 11, 3, 3), (67, 5, 3, 3), (71, 3, 23, 3), (79, 5, 3, 3), (83, 3, 5, 3), (89, 3, 13, 3), (97, 5, 3, 3)] = true := by decide +kernel
theorem c30487a1_gens : allOn 0 0 1 (-28) (-15) [(9, 21, 1), ((-14), 39, 8), ((-3), 6, 1)] = true := by decide +kernel

-- 30767d1: 20 primes
set_option maxHeartbeats 0 in
theorem c30767d1_cert0 : certAll 0 0 1 (-31) 60 [(5, 3, 2, 3), (7, 2, 3, 3), (13, 7, 2, 3), (17, 3, 2, 3), (19, 2, 3, 3), (23, 2, 7, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 7, 2, 3), (41, 3, 2, 3), (47, 2, 7, 3), (53, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c30767d1_cert1 : certAll 0 0 1 (-31) 60 [(59, 2, 17, 3), (61, 17, 2, 3), (67, 2, 3, 3), (71, 2, 23, 3), (73, 17, 2, 3), (83, 2, 7, 3), (89, 3, 2, 3), (97, 7, 2, 3)] = true := by decide +kernel
theorem c30767d1_gens : allOn 0 0 1 (-31) 60 [(5, 5, 1), ((-6), 5, 1), (4, 0, 1)] = true := by decide +kernel

-- 30815a1: 21 primes
set_option maxHeartbeats 0 in
theorem c30815a1_cert0 : certAll 0 1 1 (-16) 26 [(7, 2, 19, 3), (11, 2, 3, 7), (13, 3, 2, 3), (17, 7, 2, 3), (19, 2, 3, 3), (23, 2, 11, 3), (29, 3, 2, 3), (31, 2, 7, 3), (37, 3, 2, 3), (43, 2, 3, 3), (47, 2, 17, 3), (53, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c30815a1_cert1 : certAll 0 1 1 (-16) 26 [(59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 11, 3), (73, 11, 2, 3), (79, 2, 7, 3), (83, 2, 3, 3), (89, 7, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c30815a1_gens : allOn 0 1 1 (-16) 26 [(2, 2, 1), ((-3), 7, 1), (7, 17, 1)] = true := by decide +kernel

-- 31478b1: 22 primes
set_option maxHeartbeats 0 in
theorem c31478b1_cert0 : certAll 1 0 1 (-5) 12 [(5, 3, 13, 3), (7, 3, 11, 3), (11, 7, 3, 7), (13, 3, 7, 3), (17, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 13, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (47, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c31478b1_cert1 : certAll 1 0 1 (-5) 12 [(53, 3, 5, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 11, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c31478b1_gens : allOn 1 0 1 (-5) 12 [(1, 2, 1), ((-1), 4, 1), ((-3), 2, 1)] = true := by decide +kernel

-- 31737a1: 22 primes
set_option maxHeartbeats 0 in
theorem c31737a1_cert0 : certAll 0 (-1) 1 (-34) 90 [(5, 7, 2, 7), (7, 2, 11, 5), (11, 2, 29, 5), (13, 11, 2, 5), (17, 7, 2, 5), (19, 2, 7, 7), (23, 2, 11, 5), (29, 7, 2, 5), (31, 2, 7, 5), (37, 11, 2, 5), (41, 7, 2, 5), (43, 2, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c31737a1_cert1 : certAll 0 (-1) 1 (-34) 90 [(47, 2, 11, 5), (53, 7, 2, 5), (59, 2, 23, 5), (61, 23, 2, 5), (67, 2, 7, 5), (73, 19, 2, 5), (79, 2, 7, 5), (83, 2, 11, 5), (89, 7, 2, 5), (97, 11, 2, 5)] = true := by decide +kernel
theorem c31737a1_gens : allOn 0 (-1) 1 (-34) 90 [(4, 1, 1), (1, 7, 1), (3, 2, 1)] = true := by decide +kernel

-- 31814a1: 21 primes
set_option maxHeartbeats 0 in
theorem c31814a1_cert0 : certAll 1 0 1 2 12 [(5, 3, 13, 3), (7, 3, 11, 3), (11, 5, 3, 7), (13, 3, 5, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c31814a1_cert1 : certAll 1 0 1 2 12 [(53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 23, 3), (73, 11, 3, 3), (79, 3, 7, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c31814a1_gens : allOn 1 0 1 2 12 [((-1), 3, 1), (1, 3, 1), (3, 5, 1)] = true := by decide +kernel

-- 32192e1: 23 primes
set_option maxHeartbeats 0 in
theorem c32192e1_cert0 : certAll 0 0 0 (-52) 160 [(5, 3, 7, 3), (7, 5, 3, 3), (11, 3, 7, 3), (13, 7, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 7, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 7, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c32192e1_cert1 : certAll 0 0 0 (-52) 160 [(47, 3, 7, 3), (53, 3, 5, 3), (59, 3, 19, 3), (61, 11, 3, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 23, 3, 3), (79, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c32192e1_gens : allOn 0 0 0 (-52) 160 [(2, 8, 1), (6, 8, 1), (4, 4, 1)] = true := by decide +kernel

-- 32244c1: 23 primes
set_option maxHeartbeats 0 in
theorem c32244c1_cert0 : certAll 0 (-1) 0 (-30) 81 [(5, 11, 37, 13), (7, 5, 23, 5), (11, 5, 17, 13), (13, 11, 5, 5), (17, 7, 5, 5), (19, 5, 7, 5), (23, 5, 11, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 17, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c32244c1_cert1 : certAll 0 (-1) 0 (-30) 81 [(47, 5, 19, 5), (53, 7, 5, 5), (59, 5, 17, 5), (61, 11, 5, 5), (67, 5, 7, 5), (71, 5, 11, 5), (73, 11, 5, 5), (79, 5, 7, 5), (83, 5, 17, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c32244c1_gens : allOn 0 (-1) 0 (-30) 81 [(0, 9, 1), (6, 9, 1), (3, 3, 1)] = true := by decide +kernel

-- 32276b1: 22 primes
set_option maxHeartbeats 0 in
theorem c32276b1_cert0 : certAll 0 1 0 (-17) 16 [(5, 3, 17, 3), (7, 3, 13, 3), (11, 7, 3, 7), (13, 3, 7, 3), (17, 5, 3, 3), (23, 3, 5, 3), (29, 3, 17, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3), (47, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c32276b1_cert1 : certAll 0 1 0 (-17) 16 [(53, 3, 5, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 17, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 23, 3, 3)] = true := by decide +kernel
theorem c32276b1_gens : allOn 0 1 0 (-17) 16 [(1, 1, 1), (3, 1, 1), ((-3), 7, 1)] = true := by decide +kernel

-- 32336b1: 21 primes
set_option maxHeartbeats 0 in
theorem c32336b1_cert0 : certAll 0 1 0 (-32) 4 [(5, 3, 13, 3), (7, 3, 11, 3), (11, 7, 3, 7), (13, 3, 7, 3), (17, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 13, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c32336b1_cert1 : certAll 0 1 0 (-32) 4 [(59, 7, 3, 3), (61, 3, 7, 3), (67, 11, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c32336b1_gens : allOn 0 1 0 (-32) 4 [((-2), 8, 1), (0, 2, 1), ((-6), 4, 1)] = true := by decide +kernel

-- 33424o1: 23 primes
set_option maxHeartbeats 0 in
theorem c33424o1_cert0 : certAll 0 (-1) 0 (-312) 2224 [(5, 7, 3, 7), (7, 3, 13, 3), (11, 7, 19, 7), (13, 3, 7, 3), (17, 3, 11, 3), (19, 3, 7, 3), (23, 7, 3, 3), (29, 3, 17, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 11, 3), (43, 3, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c33424o1_cert1 : certAll 0 (-1) 0 (-312) 2224 [(47, 7, 3, 3), (53, 7, 3, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 17, 3, 3), (71, 7, 3, 3), (73, 3, 7, 3), (79, 3, 7, 3), (83, 3, 11, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c33424o1_gens : allOn 0 (-1) 0 (-312) 2224 [(12, 8, 1), (10, 2, 1), (9, 8, 1)] = true := by decide +kernel

-- 33428a1: 21 primes
set_option maxHeartbeats 0 in
theorem c33428a1_cert0 : certAll 0 1 0 (-45) 79 [(5, 3, 13, 3), (7, 3, 11, 3), (11, 5, 3, 7), (13, 3, 5, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c33428a1_cert1 : certAll 0 1 0 (-45) 79 [(53, 3, 5, 3), (59, 5, 3, 3), (67, 5, 3, 3), (71, 3, 19, 3), (73, 11, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c33428a1_gens : allOn 0 1 0 (-45) 79 [(1, 6, 1), (5, 2, 1), (9, 22, 1)] = true := by decide +kernel

-- 33509a1: 21 primes
set_option maxHeartbeats 0 in
theorem c33509a1_cert0 : certAll 0 1 1 (-22) 32 [(5, 3, 2, 3), (11, 2, 3, 13), (13, 3, 2, 3), (17, 5, 2, 3), (19, 2, 3, 3), (23, 2, 5, 3), (31, 2, 5, 3), (37, 3, 2, 3), (41, 5, 2, 3), (43, 2, 3, 3), (47, 2, 5, 3), (53, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c33509a1_cert1 : certAll 0 1 1 (-22) 32 [(59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 5, 3), (73, 5, 2, 3), (79, 2, 23, 3), (83, 2, 3, 3), (89, 11, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c33509a1_gens : allOn 0 1 1 (-22) 32 [(2, 0, 1), (3, 1, 1), (1, 3, 1)] = true := by decide +kernel

-- 33609a1: 20 primes
set_option maxHeartbeats 0 in
theorem c33609a1_cert0 : certAll 1 1 1 (-232) 1262 [(5, 2, 47, 2), (7, 5, 13, 5), (11, 7, 2, 2), (13, 2, 7, 2), (23, 7, 2, 2), (29, 5, 2, 2), (31, 2, 5, 2), (37, 41, 2, 2), (41, 2, 47, 2), (43, 5, 2, 2), (47, 2, 5, 2), (53, 7, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c33609a1_cert1 : certAll 1 1 1 (-232) 1262 [(59, 2, 5, 2), (61, 2, 7, 2), (67, 53, 2, 2), (71, 7, 2, 2), (73, 2, 7, 2), (79, 5, 2, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c33609a1_gens : allOn 1 1 1 (-232) 1262 [(10, 3, 1), (8, (-3), 1), (44, 258, 1)] = true := by decide +kernel

-- 33709a1: 21 primes
set_option maxHeartbeats 0 in
theorem c33709a1_cert0 : certAll 1 (-1) 1 (-48) (-42) [(5, 2, 17, 2), (7, 17, 3, 3), (11, 3, 2, 2), (17, 2, 5, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 5, 2, 2), (41, 2, 17, 2), (43, 17, 2, 2), (53, 3, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c33709a1_cert1 : certAll 1 (-1) 1 (-48) (-42) [(59, 2, 23, 2), (61, 2, 3, 2), (67, 5, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 5, 2, 2), (83, 2, 5, 2), (89, 2, 17, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c33709a1_gens : allOn 1 (-1) 1 (-48) (-42) [((-2), 7, 1), (24, 98, 1), ((-4), 10, 1)] = true := by decide +kernel

-- 33914a1: 22 primes
set_option maxHeartbeats 0 in
theorem c33914a1_cert0 : certAll 1 0 1 (-28) 282 [(5, 3, 7, 3), (7, 3, 11, 3), (11, 5, 3, 7), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c33914a1_cert1 : certAll 1 0 1 (-28) 282 [(53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 23, 3), (73, 13, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c33914a1_gens : allOn 1 0 1 (-28) 282 [(25, 111, 1), ((-6), 18, 1), (9, 23, 1)] = true := by decide +kernel

-- 34415a1: 21 primes
set_option maxHeartbeats 0 in
theorem c34415a1_cert0 : certAll 1 0 0 9 100 [(7, 3, 11, 3), (11, 7, 2, 2), (13, 2, 7, 2), (17, 2, 3, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 7, 2), (37, 3, 2, 2), (41, 2, 3, 2), (43, 13, 2, 2), (47, 2, 11, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c34415a1_cert1 : certAll 1 0 0 9 100 [(53, 3, 2, 2), (59, 2, 3, 2), (67, 11, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (83, 2, 3, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c34415a1_gens : allOn 1 0 0 9 100 [(3, 11, 1), ((-26), 63, 8), (28, 136, 1)] = true := by decide +kernel

-- 34862a1: 22 primes
set_option maxHeartbeats 0 in
theorem c34862a1_cert0 : certAll 1 (-1) 1 (-57) 345 [(5, 3, 13, 3), (7, 5, 3, 3), (11, 3, 17, 3), (13, 11, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 17, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c34862a1_cert1 : certAll 1 (-1) 1 (-57) 345 [(47, 3, 23, 3), (53, 3, 5, 3), (59, 3, 17, 3), (61, 11, 3, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 5, 3, 3), (83, 3, 17, 3), (89, 3, 5, 3)] = true := by decide +kernel
theorem c34862a1_gens : allOn 1 (-1) 1 (-57) 345 [(7, 12, 1), ((-1), 20, 1), ((-9), 12, 1)] = true := by decide +kernel

-- 35003a1: 19 primes
set_option maxHeartbeats 0 in
theorem c35003a1_cert0 : certAll 0 1 1 18 (-18) [(5, 3, 2, 3), (7, 2, 19, 3), (11, 2, 3, 7), (13, 3, 2, 3), (19, 2, 3, 3), (23, 2, 5, 3), (31, 2, 5, 3), (37, 3, 2, 3), (41, 5, 2, 3), (43, 2, 3, 3), (47, 2, 5, 3), (59, 2, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c35003a1_cert1 : certAll 0 1 1 18 (-18) [(61, 3, 2, 3), (67, 2, 3, 3), (73, 5, 2, 3), (79, 2, 7, 3), (83, 2, 3, 3), (89, 7, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c35003a1_gens : allOn 0 1 1 18 (-18) [(3, 8, 1), (1, 1, 1), (6, 18, 1)] = true := by decide +kernel

-- 35083c1: 22 primes
set_option maxHeartbeats 0 in
theorem c35083c1_cert0 : certAll 0 1 1 (-4) 8 [(5, 3, 2, 3), (11, 2, 3, 5), (13, 3, 2, 3), (17, 13, 2, 3), (19, 2, 3, 3), (23, 2, 19, 3), (29, 3, 2, 3), (31, 2, 13, 3), (37, 3, 2, 3), (41, 13, 2, 3), (43, 2, 3, 3), (47, 2, 19, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c35083c1_cert1 : certAll 0 1 1 (-4) 8 [(53, 3, 2, 3), (59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 23, 3), (73, 19, 2, 3), (79, 2, 13, 3), (83, 2, 3, 3), (89, 13, 2, 3), (97, 19, 2, 3)] = true := by decide +kernel
theorem c35083c1_gens : allOn 0 1 1 (-4) 8 [(1, 2, 1), ((-1), 3, 1), (2, 3, 1)] = true := by decide +kernel

-- 35234a1: 21 primes
set_option maxHeartbeats 0 in
theorem c35234a1_cert0 : certAll 1 1 0 (-181) 749 [(5, 7, 3, 7), (7, 3, 11, 3), (11, 5, 17, 5), (13, 3, 5, 3), (17, 3, 5, 3), (19, 3, 7, 3), (23, 5, 3, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 11, 3, 3), (41, 3, 5, 3), (43, 3, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c35234a1_cert1 : certAll 1 1 0 (-181) 749 [(47, 5, 3, 3), (53, 7, 3, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (73, 3, 5, 3), (83, 3, 11, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c35234a1_gens : allOn 1 1 0 (-181) 749 [((-5), 42, 1), (74, 595, 1), (102, 265, 27)] = true := by decide +kernel

-- 35243b1: 22 primes
set_option maxHeartbeats 0 in
theorem c35243b1_cert0 : certAll 1 0 0 (-22) 21 [(5, 2, 47, 2), (7, 3, 11, 3), (11, 7, 2, 2), (17, 2, 3, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 5, 2), (37, 3, 2, 2), (41, 2, 3, 2), (43, 5, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c35243b1_cert1 : certAll 1 0 0 (-22) 21 [(53, 3, 2, 2), (59, 2, 3, 2), (61, 2, 7, 2), (67, 11, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (83, 2, 3, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c35243b1_gens : allOn 1 0 0 (-22) 21 [((-1), 7, 1), (12, 33, 1), (5, 4, 1)] = true := by decide +kernel

-- 35882b1: 21 primes
set_option maxHeartbeats 0 in
theorem c35882b1_cert0 : certAll 1 (-1) 0 (-64) 244 [(5, 3, 23, 3), (13, 17, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 19, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 17, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3), (47, 3, 19, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c35882b1_cert1 : certAll 1 (-1) 0 (-64) 244 [(59, 3, 17, 3), (61, 17, 3, 3), (67, 5, 3, 3), (71, 3, 23, 3), (73, 19, 3, 3), (79, 5, 3, 3), (83, 3, 17, 3), (89, 3, 5, 3), (97, 19, 3, 3)] = true := by decide +kernel
theorem c35882b1_gens : allOn 1 (-1) 0 (-64) 244 [(13, 32, 1), (2, 10, 1), ((-1), 18, 1)] = true := by decide +kernel

-- 36094c1: 23 primes
set_option maxHeartbeats 0 in
theorem c36094c1_cert0 : certAll 1 (-1) 1 (-162) 1185 [(5, 3, 17, 3), (7, 5, 3, 3), (11, 3, 19, 3), (13, 11, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 31, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c36094c1_cert1 : certAll 1 (-1) 1 (-162) 1185 [(47, 3, 19, 3), (53, 3, 5, 3), (59, 3, 19, 3), (61, 11, 3, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 5, 3, 3), (83, 3, 29, 3), (89, 3, 5, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c36094c1_gens : allOn 1 (-1) 1 (-162) 1185 [(1, 31, 1), (9, 15, 1), (17, 47, 1)] = true := by decide +kernel

-- 36739a1: 21 primes
set_option maxHeartbeats 0 in
theorem c36739a1_cert0 : certAll 1 1 1 (-14) (-24) [(5, 2, 3, 2), (7, 3, 17, 3), (11, 5, 2, 2), (13, 2, 5, 2), (17, 2, 5, 2), (19, 2, 11, 2), (23, 5, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 7, 2, 2), (41, 2, 5, 2), (43, 3, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c36739a1_cert1 : certAll 1 1 1 (-14) (-24) [(53, 11, 2, 2), (59, 2, 3, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 5, 2, 2), (73, 2, 5, 2), (79, 3, 2, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c36739a1_gens : allOn 1 1 1 (-14) (-24) [((-2), 1, 1), ((-3), 2, 1), ((-18), 15, 8)] = true := by decide +kernel

-- 37229a1: 22 primes
set_option maxHeartbeats 0 in
theorem c37229a1_cert0 : certAll 1 0 0 (-9) 4 [(5, 2, 13, 2), (7, 3, 19, 3), (11, 5, 2, 2), (13, 2, 5, 2), (17, 2, 3, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 7, 2), (37, 3, 2, 2), (41, 2, 3, 2), (43, 5, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c37229a1_cert1 : certAll 1 0 0 (-9) 4 [(47, 2, 11, 2), (53, 3, 2, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (83, 2, 3, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c37229a1_gens : allOn 1 0 0 (-9) 4 [(0, 2, 1), ((-1), 4, 1), ((-3), 4, 1)] = true := by decide +kernel

-- 37544c1: 19 primes
set_option maxHeartbeats 0 in
theorem c37544c1_cert0 : certAll 0 1 0 (-177) 1171 [(5, 3, 17, 3), (7, 3, 11, 3), (11, 7, 3, 17), (17, 5, 3, 3), (29, 3, 31, 3), (31, 3, 5, 3), (37, 3, 5, 3), (43, 5, 3, 3), (47, 3, 5, 3), (53, 3, 5, 3), (59, 7, 3, 3), (61, 3, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c37544c1_cert1 : certAll 0 1 0 (-177) 1171 [(67, 11, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c37544c1_gens : allOn 0 1 0 (-177) 1171 [(11, 26, 1), (63, 494, 1), ((-13), 38, 1)] = true := by decide +kernel

-- 38439b1: 21 primes
set_option maxHeartbeats 0 in
theorem c38439b1_cert0 : certAll 0 0 1 (-57) 76 [(5, 7, 2, 7), (7, 2, 17, 5), (11, 2, 17, 7), (13, 23, 2, 5), (17, 7, 2, 5), (19, 2, 7, 5), (23, 2, 41, 5), (29, 7, 2, 5), (31, 2, 7, 5), (37, 11, 2, 5), (41, 7, 2, 7), (43, 2, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c38439b1_cert1 : certAll 0 0 1 (-57) 76 [(53, 7, 2, 5), (59, 2, 17, 5), (61, 11, 2, 5), (67, 2, 7, 5), (73, 17, 2, 5), (79, 2, 7, 5), (83, 2, 11, 5), (89, 7, 2, 5), (97, 17, 2, 5)] = true := by decide +kernel
theorem c38439b1_gens : allOn 0 0 1 (-57) 76 [(1, 4, 1), ((-2), 13, 1), ((-8), 4, 1)] = true := by decide +kernel

-- 38600m1: 22 primes
set_option maxHeartbeats 0 in
theorem c38600m1_cert0 : certAll 0 0 0 (-175) 850 [(7, 11, 3, 3), (11, 3, 23, 3), (13, 11, 3, 3), (17, 3, 11, 3), (19, 13, 3, 3), (23, 3, 19, 3), (29, 3, 13, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 11, 3), (43, 13, 3, 3), (47, 3, 19, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c38600m1_cert1 : certAll 0 0 0 (-175) 850 [(53, 3, 13, 3), (59, 3, 11, 3), (61, 11, 3, 3), (67, 13, 3, 3), (71, 3, 31, 3), (73, 19, 3, 3), (79, 11, 3, 3), (83, 3, 11, 3), (89, 3, 11, 3), (97, 19, 3, 3)] = true := by decide +kernel
theorem c38600m1_gens : allOn 0 0 0 (-175) 850 [(5, 10, 1), ((-5), 40, 1), (10, 10, 1)] = true := by decide +kernel

-- 38601a1: 22 primes
set_option maxHeartbeats 0 in
theorem c38601a1_cert0 : certAll 0 0 1 3 16 [(5, 11, 2, 43), (7, 2, 31, 5), (11, 2, 7, 7), (13, 7, 2, 5), (17, 7, 2, 5), (19, 2, 41, 5), (23, 2, 11, 5), (29, 17, 2, 5), (31, 2, 7, 5), (37, 7, 2, 5), (41, 7, 2, 7), (43, 2, 11, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c38601a1_cert1 : certAll 0 0 1 3 16 [(47, 2, 17, 5), (53, 29, 2, 5), (59, 2, 7, 5), (61, 7, 2, 5), (67, 2, 11, 5), (71, 2, 11, 5), (73, 11, 2, 5), (79, 2, 7, 5), (83, 2, 7, 5), (97, 11, 2, 5)] = true := by decide +kernel
theorem c38601a1_gens : allOn 0 0 1 3 16 [((-2), 1, 1), (1, 4, 1), ((-1), 3, 1)] = true := by decide +kernel

-- 39023a1: 22 primes
set_option maxHeartbeats 0 in
theorem c39023a1_cert0 : certAll 1 (-1) 1 (-6) 12 [(5, 2, 17, 2), (7, 5, 3, 3), (11, 3, 2, 2), (13, 2, 3, 2), (17, 2, 5, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 11, 2, 2), (41, 2, 5, 2), (43, 5, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c39023a1_cert1 : certAll 1 (-1) 1 (-6) 12 [(47, 2, 11, 2), (53, 3, 2, 2), (59, 2, 19, 2), (61, 2, 3, 2), (67, 5, 2, 2), (73, 2, 3, 2), (79, 5, 2, 2), (83, 2, 11, 2), (89, 2, 5, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c39023a1_gens : allOn 1 (-1) 1 (-6) 12 [(2, 1, 1), (0, 3, 1), (3, 2, 1)] = true := by decide +kernel

-- 39077c1: 22 primes
set_option maxHeartbeats 0 in
theorem c39077c1_cert0 : certAll 0 1 1 (-90) 300 [(5, 3, 2, 3), (7, 2, 19, 3), (11, 2, 3, 7), (13, 3, 2, 3), (17, 7, 2, 3), (19, 2, 3, 3), (29, 3, 2, 3), (31, 2, 7, 3), (37, 3, 2, 3), (41, 7, 2, 3), (43, 2, 3, 3), (47, 2, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c39077c1_cert1 : certAll 0 1 1 (-90) 300 [(53, 3, 2, 3), (59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 37, 3), (73, 11, 2, 3), (79, 2, 7, 3), (83, 2, 3, 3), (89, 7, 2, 3), (97, 31, 2, 3)] = true := by decide +kernel
theorem c39077c1_gens : allOn 0 1 1 (-90) 300 [(5, 0, 1), (6, 3, 1), (2, 11, 1)] = true := by decide +kernel

-- 39289a1: 23 primes
set_option maxHeartbeats 0 in
theorem c39289a1_cert0 : certAll 0 1 1 (-257) 1500 [(5, 3, 7, 3), (7, 3, 31, 3), (11, 19, 3, 7), (13, 3, 23, 3), (17, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 11, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c39289a1_cert1 : certAll 0 1 1 (-257) 1500 [(47, 3, 5, 3), (53, 3, 5, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 7, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 11, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c39289a1_gens : allOn 0 1 1 (-257) 1500 [((-14), 50, 1), (90, 97, 8), (228, 37, 27)] = true := by decide +kernel

-- 39883a1: 23 primes
set_option maxHeartbeats 0 in
theorem c39883a1_cert0 : certAll 0 1 1 (-14) 18 [(5, 3, 2, 3), (7, 2, 19, 3), (11, 2, 3, 5), (13, 3, 2, 3), (17, 7, 2, 3), (19, 2, 3, 3), (23, 2, 11, 3), (29, 3, 2, 3), (31, 2, 7, 3), (37, 3, 2, 3), (41, 7, 2, 3), (43, 2, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c39883a1_cert1 : certAll 0 1 1 (-14) 18 [(47, 2, 11, 3), (53, 3, 2, 3), (59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 23, 3), (73, 11, 2, 3), (79, 2, 7, 3), (83, 2, 3, 3), (89, 7, 2, 3), (97, 23, 2, 3)] = true := by decide +kernel
theorem c39883a1_gens : allOn 0 1 1 (-14) 18 [(2, 1, 1), (1, 2, 1), (3, 3, 1)] = true := by decide +kernel

-- 40331c1: 19 primes
set_option maxHeartbeats 0 in
theorem c40331c1_cert0 : certAll 0 (-1) 1 8 (-8) [(5, 7, 2, 7), (7, 2, 43, 3), (11, 2, 29, 7), (19, 2, 7, 3), (29, 3, 2, 3), (37, 11, 2, 3), (41, 3, 2, 3), (43, 2, 7, 3), (47, 2, 3, 3), (53, 7, 2, 3), (59, 2, 3, 3), (61, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c40331c1_cert1 : certAll 0 (-1) 1 8 (-8) [(67, 2, 3, 3), (71, 2, 3, 3), (73, 3, 2, 3), (79, 2, 7, 3), (83, 2, 11, 3), (89, 7, 2, 3), (97, 29, 2, 3)] = true := by decide +kernel
theorem c40331c1_gens : allOn 0 (-1) 1 8 (-8) [(1, 0, 1), (2, 3, 1), (4, 8, 1)] = true := by decide +kernel

-- 40929a1: 20 primes
set_option maxHeartbeats 0 in
theorem c40929a1_cert0 : certAll 0 (-1) 1 (-42) 110 [(5, 11, 2, 23), (11, 2, 29, 13), (13, 5, 2, 5), (17, 5, 2, 5), (19, 2, 11, 5), (23, 2, 5, 5), (29, 5, 2, 11), (31, 2, 5, 5), (37, 11, 2, 5), (43, 2, 11, 5), (53, 11, 2, 5), (59, 2, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c40929a1_cert1 : certAll 0 (-1) 1 (-42) 110 [(61, 5, 2, 5), (67, 2, 5, 5), (71, 2, 5, 5), (73, 5, 2, 5), (79, 2, 19, 5), (83, 2, 11, 5), (89, 19, 2, 5), (97, 29, 2, 5)] = true := by decide +kernel
theorem c40929a1_gens : allOn 0 (-1) 1 (-42) 110 [(0, 10, 1), (3, 1, 1), ((-7), 3, 1)] = true := by decide +kernel

-- 41001a1: 22 primes
set_option maxHeartbeats 0 in
theorem c41001a1_cert0 : certAll 0 (-1) 1 (-134) 644 [(5, 11, 2, 13), (7, 2, 13, 5), (11, 2, 7, 5), (13, 7, 2, 5), (17, 13, 2, 5), (19, 2, 11, 11), (23, 2, 7, 5), (29, 7, 2, 5), (31, 2, 13, 5), (37, 7, 2, 5), (41, 7, 2, 5), (43, 2, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c41001a1_cert1 : certAll 0 (-1) 1 (-134) 644 [(47, 2, 7, 5), (53, 7, 2, 5), (59, 2, 11, 5), (61, 11, 2, 5), (67, 2, 11, 5), (71, 2, 23, 5), (73, 23, 2, 5), (83, 2, 7, 5), (89, 7, 2, 5), (97, 7, 2, 5)] = true := by decide +kernel
theorem c41001a1_gens : allOn 0 (-1) 1 (-134) 644 [(7, 0, 1), (8, 4, 1), (6, 4, 1)] = true := by decide +kernel

-- 41107a1: 20 primes
set_option maxHeartbeats 0 in
theorem c41107a1_cert0 : certAll 0 1 1 (-82) 182 [(5, 3, 2, 3), (7, 2, 19, 3), (13, 3, 2, 3), (17, 5, 2, 3), (19, 2, 3, 3), (23, 2, 5, 3), (29, 3, 2, 3), (31, 2, 5, 3), (41, 5, 2, 3), (43, 2, 3, 3), (47, 2, 5, 3), (53, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c41107a1_cert1 : certAll 0 1 1 (-82) 182 [(59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 5, 3), (73, 5, 2, 3), (79, 2, 7, 3), (83, 2, 3, 3), (97, 29, 2, 3)] = true := by decide +kernel
theorem c41107a1_gens : allOn 0 1 1 (-82) 182 [((-2), 18, 1), (35, 203, 1), (13, 38, 1)] = true := by decide +kernel

-- 41406b1: 20 primes
set_option maxHeartbeats 0 in
theorem c41406b1_cert0 : certAll 1 1 0 (-69) 189 [(5, 7, 17, 7), (7, 5, 11, 5), (11, 7, 17, 7), (13, 5, 7, 5), (17, 5, 11, 5), (19, 5, 7, 5), (23, 7, 5, 5), (29, 5, 31, 7), (31, 11, 5, 5), (37, 11, 5, 5), (41, 5, 23, 5), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c41406b1_cert1 : certAll 1 1 0 (-69) 189 [(53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (73, 5, 7, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c41406b1_gens : allOn 1 1 0 (-69) 189 [(6, 3, 1), (3, 3, 1), (5, (-3), 1)] = true := by decide +kernel

-- 41775k1: 22 primes
set_option maxHeartbeats 0 in
theorem c41775k1_cert0 : certAll 0 (-1) 1 (-58) 168 [(7, 2, 29, 13), (11, 2, 17, 7), (13, 11, 2, 7), (17, 7, 2, 7), (19, 2, 7, 7), (23, 2, 17, 7), (29, 7, 2, 7), (31, 2, 7, 11), (37, 11, 2, 7), (41, 7, 2, 7), (43, 2, 7, 7), (47, 2, 17, 7)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c41775k1_cert1 : certAll 0 (-1) 1 (-58) 168 [(53, 7, 2, 7), (59, 2, 11, 7), (61, 11, 2, 7), (67, 2, 7, 7), (71, 2, 19, 7), (73, 19, 2, 7), (79, 2, 7, 7), (83, 2, 11, 7), (89, 7, 2, 7), (97, 17, 2, 7)] = true := by decide +kernel
theorem c41775k1_gens : allOn 0 (-1) 1 (-58) 168 [(7, 7, 1), (2, 7, 1), ((-3), 17, 1)] = true := by decide +kernel

-- 41785a1: 20 primes
set_option maxHeartbeats 0 in
theorem c41785a1_cert0 : certAll 0 1 1 (-286) 1766 [(7, 2, 13, 3), (11, 2, 3, 7), (13, 3, 2, 3), (17, 7, 2, 3), (19, 2, 3, 3), (23, 2, 11, 3), (29, 3, 2, 3), (31, 2, 7, 3), (37, 3, 2, 3), (41, 7, 2, 3), (43, 2, 3, 3), (47, 2, 23, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c41785a1_cert1 : certAll 0 1 1 (-286) 1766 [(53, 3, 2, 3), (59, 2, 3, 3), (67, 2, 3, 3), (71, 2, 11, 3), (73, 11, 2, 3), (79, 2, 7, 3), (83, 2, 3, 3), (89, 7, 2, 3)] = true := by decide +kernel
theorem c41785a1_gens : allOn 0 1 1 (-286) 1766 [(7, 12, 1), (9, 1, 1), ((-18), 37, 1)] = true := by decide +kernel

-- 41933a1: 20 primes
set_option maxHeartbeats 0 in
theorem c41933a1_cert0 : certAll 1 0 0 (-95) 346 [(5, 2, 7, 2), (7, 3, 29, 3), (11, 5, 2, 2), (13, 2, 5, 2), (29, 3, 2, 2), (31, 2, 29, 2), (37, 3, 2, 2), (41, 2, 3, 2), (43, 5, 2, 2), (47, 2, 7, 2), (53, 3, 2, 2), (59, 2, 3, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c41933a1_cert1 : certAll 1 0 0 (-95) 346 [(61, 2, 5, 2), (67, 5, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (83, 2, 3, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c41933a1_gens : allOn 1 0 0 (-95) 346 [(3, 8, 1), (5, (-4), 1), (138, (-50), 27)] = true := by decide +kernel

-- 42093a1: 22 primes
set_option maxHeartbeats 0 in
theorem c42093a1_cert0 : certAll 0 0 1 (-21) 22 [(5, 11, 2, 13), (7, 2, 13, 5), (11, 2, 17, 5), (13, 11, 2, 5), (17, 7, 2, 5), (19, 2, 7, 7), (23, 2, 17, 5), (29, 7, 2, 5), (31, 2, 7, 5), (41, 7, 2, 5), (43, 2, 7, 5), (47, 2, 17, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c42093a1_cert1 : certAll 0 0 1 (-21) 22 [(53, 7, 2, 5), (59, 2, 11, 5), (61, 11, 2, 5), (67, 2, 7, 5), (71, 2, 23, 5), (73, 23, 2, 5), (79, 2, 7, 5), (83, 2, 11, 5), (89, 7, 2, 5), (97, 17, 2, 5)] = true := by decide +kernel
theorem c42093a1_gens : allOn 0 0 1 (-21) 22 [(1, 1, 1), (4, 1, 1), ((-2), 7, 1)] = true := by decide +kernel

-- 42153a1: 22 primes
set_option maxHeartbeats 0 in
theorem c42153a1_cert0 : certAll 0 (-1) 1 (-6) 20 [(5, 7, 2, 7), (7, 2, 5, 5), (11, 2, 5, 7), (13, 5, 2, 5), (17, 7, 2, 5), (19, 2, 7, 7), (23, 2, 5, 5), (31, 2, 7, 5), (37, 5, 2, 5), (41, 5, 2, 5), (43, 2, 5, 5), (47, 2, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c42153a1_cert1 : certAll 0 (-1) 1 (-6) 20 [(53, 5, 2, 5), (59, 2, 11, 5), (61, 11, 2, 5), (67, 2, 7, 5), (71, 2, 47, 5), (73, 17, 2, 5), (79, 2, 7, 5), (83, 2, 5, 5), (89, 5, 2, 5), (97, 5, 2, 5)] = true := by decide +kernel
theorem c42153a1_gens : allOn 0 (-1) 1 (-6) 20 [(0, 4, 1), (3, 4, 1), ((-3), 1, 1)] = true := by decide +kernel

-- 42190a1: 20 primes
set_option maxHeartbeats 0 in
theorem c42190a1_cert0 : certAll 1 0 1 (-19) 42 [(7, 3, 11, 3), (11, 7, 3, 17), (13, 3, 7, 3), (17, 7, 3, 3), (19, 31, 3, 3), (23, 3, 11, 3), (29, 3, 23, 3), (31, 3, 7, 3), (37, 3, 7, 3), (41, 7, 3, 3), (43, 19, 3, 3), (53, 3, 19, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c42190a1_cert1 : certAll 1 0 1 (-19) 42 [(59, 7, 3, 3), (67, 11, 3, 3), (71, 3, 23, 3), (73, 19, 3, 3), (79, 3, 7, 3), (83, 7, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c42190a1_gens : allOn 1 0 1 (-19) 42 [(1, 4, 1), ((-4), 9, 1), (6, 9, 1)] = true := by decide +kernel

-- 42264a1: 22 primes
set_option maxHeartbeats 0 in
theorem c42264a1_cert0 : certAll 0 0 0 (-252) 1620 [(5, 11, 13, 23), (7, 5, 19, 5), (11, 5, 17, 13), (13, 11, 5, 5), (17, 7, 5, 5), (19, 5, 7, 5), (23, 5, 17, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 11, 5, 5), (43, 5, 7, 5), (47, 5, 17, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c42264a1_cert1 : certAll 0 0 0 (-252) 1620 [(53, 7, 5, 5), (59, 5, 11, 5), (61, 11, 5, 5), (67, 5, 7, 5), (71, 5, 23, 5), (73, 17, 5, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 19, 5, 5)] = true := by decide +kernel
theorem c42264a1_gens : allOn 0 0 0 (-252) 1620 [(6, 18, 1), (12, 18, 1), ((-6), 54, 1)] = true := by decide +kernel

-- 42384a1: 23 primes
set_option maxHeartbeats 0 in
theorem c42384a1_cert0 : certAll 0 (-1) 0 (-80) 336 [(5, 7, 17, 7), (7, 5, 47, 5), (11, 5, 13, 7), (13, 11, 5, 5), (17, 7, 5, 5), (19, 5, 7, 5), (23, 5, 13, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 11, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c42384a1_cert1 : certAll 0 (-1) 0 (-80) 336 [(47, 5, 13, 5), (53, 7, 5, 5), (59, 5, 11, 5), (61, 11, 5, 5), (67, 5, 7, 5), (71, 5, 23, 5), (73, 13, 5, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 17, 5, 5)] = true := by decide +kernel
theorem c42384a1_gens : allOn 0 (-1) 0 (-80) 336 [(8, 12, 1), ((-4), 24, 1), (4, 8, 1)] = true := by decide +kernel

-- 42526b1: 22 primes
set_option maxHeartbeats 0 in
theorem c42526b1_cert0 : certAll 1 0 1 (-78) 272 [(5, 3, 7, 3), (7, 3, 13, 3), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 19, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 31, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c42526b1_cert1 : certAll 1 0 1 (-78) 272 [(53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 19, 3), (73, 19, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 19, 3, 3)] = true := by decide +kernel
theorem c42526b1_gens : allOn 1 0 1 (-78) 272 [(4, 3, 1), ((-7), 25, 1), (1, 13, 1)] = true := by decide +kernel

-- 42528c1: 23 primes
set_option maxHeartbeats 0 in
theorem c42528c1_cert0 : certAll 0 (-1) 0 (-65) 81 [(5, 23, 17, 23), (7, 5, 11, 5), (11, 5, 23, 13), (13, 11, 5, 5), (17, 7, 5, 5), (19, 5, 7, 5), (23, 5, 11, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 11, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c42528c1_cert1 : certAll 0 (-1) 0 (-65) 81 [(47, 5, 11, 5), (53, 7, 5, 5), (59, 5, 23, 5), (61, 17, 5, 5), (67, 5, 7, 5), (71, 5, 17, 5), (73, 17, 5, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c42528c1_gens : allOn 0 (-1) 0 (-65) 81 [((-7), 12, 1), (1, 4, 1), ((-1), 12, 1)] = true := by decide +kernel

-- 42584c1: 20 primes
set_option maxHeartbeats 0 in
theorem c42584c1_cert0 : certAll 0 1 0 (-44) 112 [(5, 3, 17, 3), (7, 3, 11, 3), (11, 5, 3, 5), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c42584c1_cert1 : certAll 0 1 0 (-44) 112 [(61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 37, 3), (73, 37, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c42584c1_gens : allOn 0 1 0 (-44) 112 [(2, 6, 1), (4, 4, 1), (6, 10, 1)] = true := by decide +kernel

-- 43556b1: 22 primes
set_option maxHeartbeats 0 in
theorem c43556b1_cert0 : certAll 0 1 0 (-14) 1 [(5, 3, 7, 3), (7, 3, 17, 3), (11, 5, 3, 5), (13, 3, 5, 3), (17, 19, 3, 3), (19, 5, 3, 3), (23, 3, 7, 3), (29, 3, 5, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c43556b1_cert1 : certAll 0 1 0 (-14) 1 [(53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 17, 3), (73, 17, 3, 3), (79, 3, 17, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c43556b1_gens : allOn 0 1 0 (-14) 1 [(0, 1, 1), ((-2), 5, 1), ((-4), 3, 1)] = true := by decide +kernel

-- 43669a1: 19 primes
set_option maxHeartbeats 0 in
theorem c43669a1_cert0 : certAll 0 0 1 (-19) 30 [(5, 3, 2, 3), (7, 2, 3, 3), (13, 5, 2, 3), (17, 3, 2, 3), (19, 2, 3, 3), (23, 2, 5, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 7, 2, 3), (41, 3, 2, 3), (43, 2, 3, 3), (47, 2, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c43669a1_cert1 : certAll 0 0 1 (-19) 30 [(53, 3, 2, 3), (59, 2, 5, 3), (61, 5, 2, 3), (67, 2, 3, 3), (73, 5, 2, 3), (83, 2, 7, 3), (97, 17, 2, 3)] = true := by decide +kernel
theorem c43669a1_gens : allOn 0 0 1 (-19) 30 [(2, 0, 1), (3, 0, 1), (1, 3, 1)] = true := by decide +kernel

-- 43730e1: 22 primes
set_option maxHeartbeats 0 in
theorem c43730e1_cert0 : certAll 1 (-1) 0 (-184) 940 [(7, 11, 3, 3), (11, 3, 17, 3), (13, 11, 3, 3), (17, 3, 11, 3), (19, 37, 3, 3), (23, 3, 29, 3), (29, 3, 37, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 11, 3), (43, 23, 3, 3), (47, 3, 29, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c43730e1_cert1 : certAll 1 (-1) 0 (-184) 940 [(53, 3, 29, 3), (59, 3, 11, 3), (61, 11, 3, 3), (67, 23, 3, 3), (71, 3, 23, 3), (73, 23, 3, 3), (79, 11, 3, 3), (83, 3, 11, 3), (89, 3, 11, 3), (97, 23, 3, 3)] = true := by decide +kernel
theorem c43730e1_gens : allOn 1 (-1) 0 (-184) 940 [(11, 7, 1), (6, 2, 1), (1, 27, 1)] = true := by decide +kernel

-- 43976f1: 22 primes
set_option maxHeartbeats 0 in
theorem c43976f1_cert0 : certAll 0 0 0 (-31) 34 [(5, 3, 7, 3), (7, 5, 3, 3), (11, 3, 7, 3), (13, 7, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 7, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3), (47, 3, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c43976f1_cert1 : certAll 0 0 0 (-31) 34 [(53, 3, 5, 3), (59, 3, 41, 3), (61, 11, 3, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c43976f1_gens : allOn 0 0 0 (-31) 34 [(1, 2, 1), (5, 2, 1), ((-3), 10, 1)] = true := by decide +kernel

-- 44012b1: 23 primes
set_option maxHeartbeats 0 in
theorem c44012b1_cert0 : certAll 0 (-1) 0 (-65) 226 [(5, 7, 3, 7), (7, 3, 13, 3), (11, 5, 19, 7), (13, 3, 5, 3), (17, 3, 5, 3), (19, 3, 7, 3), (23, 5, 3, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 19, 3, 3), (41, 3, 5, 3), (43, 3, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c44012b1_cert1 : certAll 0 (-1) 0 (-65) 226 [(47, 5, 3, 3), (53, 7, 3, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 7, 3), (83, 3, 23, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c44012b1_gens : allOn 0 (-1) 0 (-65) 226 [(5, 1, 1), (3, 7, 1), (6, 4, 1)] = true := by decide +kernel

-- 44233a1: 18 primes
set_option maxHeartbeats 0 in
theorem c44233a1_cert0 : certAll 1 1 1 (-137) 600 [(5, 2, 3, 2), (11, 29, 2, 2), (17, 2, 11, 2), (19, 2, 11, 2), (23, 11, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 11, 2, 2), (41, 2, 11, 2), (43, 3, 2, 2), (47, 2, 3, 2), (53, 11, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c44233a1_cert1 : certAll 1 1 1 (-137) 600 [(59, 2, 3, 2), (61, 2, 29, 2), (67, 37, 2, 2), (73, 2, 11, 2), (79, 3, 2, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c44233a1_gens : allOn 1 1 1 (-137) 600 [((-8), 39, 1), (63, 465, 1), (7, 3, 1)] = true := by decide +kernel

-- 44409b1: 23 primes
set_option maxHeartbeats 0 in
theorem c44409b1_cert0 : certAll 1 1 1 (-45) 96 [(5, 2, 13, 2), (7, 5, 17, 5), (11, 5, 2, 2), (13, 2, 5, 2), (17, 2, 5, 2), (19, 2, 7, 2), (23, 5, 2, 2), (29, 7, 2, 2), (31, 2, 7, 2), (37, 13, 2, 2), (41, 2, 5, 2), (43, 5, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c44409b1_cert1 : certAll 1 1 1 (-45) 96 [(47, 2, 19, 2), (53, 7, 2, 2), (59, 2, 19, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 5, 2, 2), (73, 2, 5, 2), (79, 5, 2, 2), (83, 2, 23, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c44409b1_gens : allOn 1 1 1 (-45) 96 [(4, (-1), 1), (3, (-3), 1), (2, 3, 1)] = true := by decide +kernel

-- 44755a1: 22 primes
set_option maxHeartbeats 0 in
theorem c44755a1_cert0 : certAll 0 1 1 9 0 [(7, 3, 23, 3), (11, 13, 3, 7), (13, 3, 17, 3), (17, 7, 3, 3), (19, 7, 3, 3), (23, 3, 11, 3), (29, 3, 7, 3), (31, 3, 7, 3), (37, 3, 11, 3), (41, 7, 3, 3), (43, 7, 3, 3), (47, 3, 23, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c44755a1_cert1 : certAll 0 1 1 9 0 [(53, 3, 7, 3), (59, 11, 3, 3), (61, 3, 13, 3), (67, 7, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 3, 7, 3), (83, 11, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c44755a1_gens : allOn 0 1 1 9 0 [(0, 0, 1), (2, 5, 1), (10, 34, 1)] = true := by decide +kernel

-- 44755b1: 21 primes
set_option maxHeartbeats 0 in
theorem c44755b1_cert0 : certAll 0 1 1 (-410) 3306 [(7, 2, 13, 3), (11, 2, 3, 7), (13, 3, 2, 3), (17, 7, 2, 3), (19, 2, 3, 3), (23, 2, 11, 3), (31, 2, 7, 3), (37, 3, 2, 3), (41, 7, 2, 3), (43, 2, 3, 3), (47, 2, 17, 3), (53, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c44755b1_cert1 : certAll 0 1 1 (-410) 3306 [(59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 11, 3), (73, 11, 2, 3), (79, 2, 7, 3), (83, 2, 3, 3), (89, 7, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c44755b1_gens : allOn 0 1 1 (-410) 3306 [(5, 37, 1), ((-20), 62, 1), (90, 121, 8)] = true := by decide +kernel

-- 44794c1: 21 primes
set_option maxHeartbeats 0 in
theorem c44794c1_cert0 : certAll 1 0 0 (-155) 721 [(5, 3, 13, 3), (7, 3, 11, 3), (11, 5, 3, 7), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (37, 3, 5, 3), (43, 5, 3, 3), (47, 3, 11, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c44794c1_cert1 : certAll 1 0 0 (-155) 721 [(59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 29, 3), (73, 19, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c44794c1_gens : allOn 1 0 0 (-155) 721 [(6, 1, 1), (10, 9, 1), (8, (-7), 1)] = true := by decide +kernel

-- 44860b1: 21 primes
set_option maxHeartbeats 0 in
theorem c44860b1_cert0 : certAll 0 0 0 (-28) 73 [(7, 13, 3, 3), (11, 3, 19, 3), (13, 11, 3, 3), (17, 3, 13, 3), (19, 11, 3, 3), (23, 3, 11, 3), (29, 3, 11, 3), (31, 11, 3, 3), (37, 17, 3, 3), (43, 13, 3, 3), (47, 3, 19, 3), (53, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c44860b1_cert1 : certAll 0 0 0 (-28) 73 [(59, 3, 19, 3), (61, 11, 3, 3), (67, 13, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 13, 3, 3), (83, 3, 23, 3), (89, 3, 13, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c44860b1_gens : allOn 0 0 0 (-28) 73 [(4, 5, 1), ((-6), 5, 1), ((-1), 10, 1)] = true := by decide +kernel

-- 44869b1: 20 primes
set_option maxHeartbeats 0 in
theorem c44869b1_cert0 : certAll 1 1 1 (-222) (-410) [(5, 2, 3, 2), (7, 3, 19, 3), (17, 2, 29, 2), (19, 2, 7, 2), (23, 7, 2, 2), (29, 3, 2, 2), (37, 23, 2, 2), (41, 2, 17, 2), (43, 3, 2, 2), (47, 2, 3, 2), (53, 7, 2, 2), (59, 2, 3, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c44869b1_cert1 : certAll 1 1 1 (-222) (-410) [(61, 2, 7, 2), (67, 17, 2, 2), (71, 7, 2, 2), (73, 2, 7, 2), (79, 3, 2, 2), (83, 2, 23, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c44869b1_gens : allOn 1 1 1 (-222) (-410) [(20, 50, 1), ((-2), 6, 1), ((-172), 901, 64)] = true := by decide +kernel

-- 45123h1: 20 primes
set_option maxHeartbeats 0 in
theorem c45123h1_cert0 : certAll 0 (-1) 1 (-30) 2 [(5, 23, 2, 23), (7, 2, 11, 5), (11, 2, 19, 17), (17, 7, 2, 5), (19, 2, 7, 5), (23, 2, 11, 5), (29, 7, 2, 5), (31, 2, 7, 5), (37, 17, 2, 5), (41, 7, 2, 7), (47, 2, 11, 5), (53, 7, 2, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c45123h1_cert1 : certAll 0 (-1) 1 (-30) 2 [(59, 2, 11, 5), (61, 11, 2, 5), (67, 2, 7, 5), (71, 2, 17, 5), (73, 11, 2, 5), (79, 2, 7, 5), (83, 2, 23, 5), (97, 11, 2, 5)] = true := by decide +kernel
theorem c45123h1_gens : allOn 0 (-1) 1 (-30) 2 [(9, 19, 1), ((-4), 6, 1), ((-6), 35, 8)] = true := by decide +kernel

-- 45352a1: 22 primes
set_option maxHeartbeats 0 in
theorem c45352a1_cert0 : certAll 0 1 0 (-137) 571 [(5, 3, 17, 3), (7, 3, 11, 3), (11, 7, 3, 7), (13, 3, 7, 3), (17, 5, 3, 3), (19, 5, 3, 3), (29, 3, 17, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3), (47, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c45352a1_cert1 : certAll 0 1 0 (-137) 571 [(53, 3, 5, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 11, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c45352a1_gens : allOn 0 1 0 (-137) 571 [(7, 2, 1), (5, 6, 1), (6, 1, 1)] = true := by decide +kernel

-- 45985a1: 21 primes
set_option maxHeartbeats 0 in
theorem c45985a1_cert0 : certAll 0 1 1 (-76) 230 [(7, 2, 47, 3), (11, 2, 3, 7), (13, 3, 2, 3), (19, 2, 3, 3), (23, 2, 19, 3), (29, 3, 2, 3), (31, 2, 7, 3), (37, 3, 2, 3), (41, 7, 2, 3), (43, 2, 3, 3), (47, 2, 11, 3), (53, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c45985a1_cert1 : certAll 0 1 1 (-76) 230 [(59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 11, 3), (73, 19, 2, 3), (79, 2, 7, 3), (83, 2, 3, 3), (89, 7, 2, 3), (97, 19, 2, 3)] = true := by decide +kernel
theorem c45985a1_gens : allOn 0 1 1 (-76) 230 [(4, 2, 1), (5, 0, 1), (2, 9, 1)] = true := by decide +kernel

-- 46024a1: 22 primes
set_option maxHeartbeats 0 in
theorem c46024a1_cert0 : certAll 0 1 0 (-65) 259 [(5, 3, 17, 3), (7, 3, 13, 3), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 47, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 23, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c46024a1_cert1 : certAll 0 1 0 (-65) 259 [(53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 17, 3), (73, 17, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c46024a1_gens : allOn 0 1 0 (-65) 259 [((-5), 22, 1), (6, 11, 1), (17, 66, 1)] = true := by decide +kernel

-- 46222a1: 20 primes
set_option maxHeartbeats 0 in
theorem c46222a1_cert0 : certAll 1 (-1) 0 (-61) 193 [(5, 3, 7, 3), (7, 5, 3, 3), (13, 5, 3, 3), (17, 3, 7, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 13, 3), (31, 7, 3, 3), (37, 7, 3, 3), (41, 3, 13, 3), (43, 5, 3, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c46222a1_cert1 : certAll 1 (-1) 0 (-61) 193 [(59, 3, 5, 3), (61, 5, 3, 3), (67, 7, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 5, 3, 3), (83, 3, 7, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c46222a1_gens : allOn 1 (-1) 0 (-61) 193 [(3, 4, 1), ((-8), (-7), 1), (14, 37, 1)] = true := by decide +kernel

-- 46307a1: 22 primes
set_option maxHeartbeats 0 in
theorem c46307a1_cert0 : certAll 1 0 0 (-9) (-2) [(5, 2, 13, 2), (7, 3, 23, 3), (11, 5, 2, 2), (13, 2, 5, 2), (17, 2, 3, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 7, 2), (37, 3, 2, 2), (41, 2, 3, 2), (43, 5, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c46307a1_cert1 : certAll 1 0 0 (-9) (-2) [(47, 2, 17, 2), (53, 3, 2, 2), (59, 2, 3, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c46307a1_gens : allOn 1 0 0 (-9) (-2) [((-1), 3, 1), ((-2), 4, 1), ((-3), 2, 1)] = true := by decide +kernel

-- 46462d1: 20 primes
set_option maxHeartbeats 0 in
theorem c46462d1_cert0 : certAll 1 0 1 (-53) 132 [(5, 3, 7, 3), (7, 3, 23, 3), (11, 5, 3, 7), (17, 29, 3, 3), (19, 5, 3, 3), (23, 3, 7, 3), (29, 3, 5, 3), (37, 3, 5, 3), (43, 5, 3, 3), (47, 3, 7, 3), (53, 3, 5, 3), (59, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c46462d1_cert1 : certAll 1 0 1 (-53) 132 [(61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 29, 3, 3), (79, 3, 11, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c46462d1_gens : allOn 1 0 1 (-53) 132 [(6, 3, 1), ((-7), 16, 1), (5, (-2), 1)] = true := by decide +kernel

-- 46672g1: 19 primes
set_option maxHeartbeats 0 in
theorem c46672g1_cert0 : certAll 0 0 0 (-67) 130 [(5, 3, 7, 3), (7, 5, 3, 3), (11, 3, 7, 3), (13, 7, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 5, 3, 3), (43, 5, 3, 3), (47, 3, 29, 3), (59, 3, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c46672g1_cert1 : certAll 0 0 0 (-67) 130 [(67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c46672g1_gens : allOn 0 0 0 (-67) 130 [(1, 8, 1), (9, 16, 1), ((-7), 16, 1)] = true := by decide +kernel

-- 46896d1: 22 primes
set_option maxHeartbeats 0 in
theorem c46896d1_cert0 : certAll 0 (-1) 0 (-72) 144 [(5, 11, 17, 67), (7, 5, 13, 5), (11, 7, 19, 13), (13, 5, 7, 5), (17, 5, 11, 5), (19, 5, 7, 5), (23, 7, 5, 5), (29, 5, 17, 7), (31, 11, 5, 5), (37, 11, 5, 5), (41, 5, 11, 5), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c46896d1_cert1 : certAll 0 (-1) 0 (-72) 144 [(47, 7, 5, 5), (53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (67, 17, 5, 5), (73, 5, 7, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 17, 5, 5)] = true := by decide +kernel
theorem c46896d1_gens : allOn 0 (-1) 0 (-72) 144 [(0, 12, 1), (8, 4, 1), ((-8), 12, 1)] = true := by decide +kernel

-- 47087a1: 23 primes
set_option maxHeartbeats 0 in
theorem c47087a1_cert0 : certAll 1 (-1) 1 (-31) 72 [(5, 2, 7, 2), (7, 5, 17, 5), (11, 5, 2, 2), (13, 2, 5, 2), (17, 2, 5, 2), (19, 2, 11, 2), (23, 5, 2, 2), (29, 11, 2, 2), (31, 2, 7, 2), (37, 7, 2, 2), (41, 2, 5, 2), (43, 5, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c47087a1_cert1 : certAll 1 (-1) 1 (-31) 72 [(47, 2, 17, 2), (53, 11, 2, 2), (59, 2, 7, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 5, 2, 2), (73, 2, 5, 2), (79, 5, 2, 2), (83, 2, 7, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c47087a1_gens : allOn 1 (-1) 1 (-31) 72 [(3, (-3), 1), (4, (-1), 1), ((-5), 11, 1)] = true := by decide +kernel

-- 47440a1: 22 primes
set_option maxHeartbeats 0 in
theorem c47440a1_cert0 : certAll 0 1 0 (-576) 5140 [(7, 3, 11, 3), (11, 7, 3, 13), (13, 3, 7, 3), (17, 7, 3, 3), (19, 31, 3, 3), (23, 3, 11, 3), (29, 3, 31, 3), (31, 3, 7, 3), (37, 3, 7, 3), (41, 7, 3, 3), (43, 11, 3, 3), (47, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c47440a1_cert1 : certAll 0 1 0 (-576) 5140 [(53, 3, 11, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 11, 3, 3), (71, 3, 23, 3), (73, 11, 3, 3), (79, 3, 7, 3), (83, 7, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c47440a1_gens : allOn 0 1 0 (-576) 5140 [(12, 10, 1), (14, 4, 1), (6, 44, 1)] = true := by decide +kernel

-- 47453a1: 20 primes
set_option maxHeartbeats 0 in
theorem c47453a1_cert0 : certAll 0 0 1 (-19) 42 [(5, 3, 2, 3), (11, 2, 17, 3), (13, 5, 2, 3), (17, 3, 2, 3), (19, 2, 3, 3), (23, 2, 5, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 11, 2, 3), (41, 3, 2, 3), (43, 2, 3, 3), (47, 2, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c47453a1_cert1 : certAll 0 0 1 (-19) 42 [(53, 3, 2, 3), (59, 2, 5, 3), (61, 5, 2, 3), (67, 2, 3, 3), (71, 2, 5, 3), (73, 5, 2, 3), (79, 2, 3, 3), (97, 23, 2, 3)] = true := by decide +kernel
theorem c47453a1_gens : allOn 0 0 1 (-19) 42 [(2, 3, 1), ((-5), 3, 1), (9, 24, 1)] = true := by decide +kernel

-- 47696h1: 22 primes
set_option maxHeartbeats 0 in
theorem c47696h1_cert0 : certAll 0 1 0 (-472) 3684 [(5, 3, 43, 3), (7, 3, 17, 3), (13, 3, 7, 3), (17, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 17, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3), (47, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c47696h1_cert1 : certAll 0 1 0 (-472) 3684 [(53, 3, 5, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 29, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c47696h1_gens : allOn 0 1 0 (-472) 3684 [(8, 22, 1), (30, 132, 1), (74, 616, 1)] = true := by decide +kernel

-- 47976d1: 22 primes
set_option maxHeartbeats 0 in
theorem c47976d1_cert0 : certAll 0 (-1) 0 (-52) 196 [(5, 7, 23, 7), (7, 5, 11, 5), (11, 7, 17, 7), (13, 5, 7, 5), (17, 5, 11, 5), (19, 5, 7, 5), (23, 7, 5, 5), (29, 5, 37, 7), (31, 11, 5, 5), (37, 11, 5, 5), (41, 5, 17, 5), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c47976d1_cert1 : certAll 0 (-1) 0 (-52) 196 [(47, 7, 5, 5), (53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (67, 11, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 7, 5), (83, 5, 11, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c47976d1_gens : allOn 0 (-1) 0 (-52) 196 [(4, 6, 1), ((-8), 6, 1), (10, 24, 1)] = true := by decide +kernel

-- 48272b1: 22 primes
set_option maxHeartbeats 0 in
theorem c48272b1_cert0 : certAll 0 0 0 (-19) 226 [(5, 3, 13, 3), (11, 3, 17, 3), (13, 5, 3, 3), (17, 3, 11, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 11, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 13, 3), (43, 5, 3, 3), (47, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c48272b1_cert1 : certAll 0 0 0 (-19) 226 [(53, 3, 5, 3), (59, 3, 5, 3), (61, 5, 3, 3), (67, 11, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 5, 3, 3), (83, 3, 11, 3), (89, 3, 5, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c48272b1_gens : allOn 0 0 0 (-19) 226 [(9, 28, 1), ((-5), 14, 1), (2, 14, 1)] = true := by decide +kernel

-- 48434c1: 21 primes
set_option maxHeartbeats 0 in
theorem c48434c1_cert0 : certAll 1 0 1 (-227) 1374 [(5, 3, 7, 3), (7, 3, 19, 3), (11, 5, 3, 5), (13, 3, 5, 3), (17, 11, 3, 3), (19, 5, 3, 3), (23, 3, 7, 3), (29, 3, 5, 3), (31, 3, 19, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c48434c1_cert1 : certAll 1 0 1 (-227) 1374 [(47, 3, 7, 3), (53, 3, 5, 3), (59, 5, 3, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 3, 11, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c48434c1_gens : allOn 1 0 1 (-227) 1374 [(2, 29, 1), (63, 456, 1), (237, 112, 27)] = true := by decide +kernel

-- 48444a1: 22 primes
set_option maxHeartbeats 0 in
theorem c48444a1_cert0 : certAll 0 (-1) 0 (-170) 921 [(5, 17, 13, 17), (7, 5, 17, 5), (13, 23, 5, 5), (17, 7, 5, 5), (19, 5, 7, 5), (23, 5, 31, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 17, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5), (47, 5, 17, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c48444a1_cert1 : certAll 0 (-1) 0 (-170) 921 [(53, 7, 5, 5), (59, 5, 17, 5), (61, 41, 5, 5), (67, 5, 7, 5), (71, 5, 17, 5), (73, 17, 5, 5), (79, 5, 7, 5), (83, 5, 17, 5), (89, 7, 5, 5), (97, 17, 5, 5)] = true := by decide +kernel
theorem c48444a1_gens : allOn 0 (-1) 0 (-170) 921 [(10, 11, 1), (8, 3, 1), (58, 33, 8)] = true := by decide +kernel

-- 48734b1: 20 primes
set_option maxHeartbeats 0 in
theorem c48734b1_cert0 : certAll 1 0 1 45 110 [(5, 3, 23, 3), (11, 13, 3, 13), (13, 3, 23, 3), (17, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 47, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3), (47, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c48734b1_cert1 : certAll 1 0 1 45 110 [(53, 3, 5, 3), (61, 3, 13, 3), (67, 19, 3, 3), (73, 5, 3, 3), (79, 3, 13, 3), (83, 5, 3, 3), (89, 13, 3, 3), (97, 19, 3, 3)] = true := by decide +kernel
theorem c48734b1_gens : allOn 1 0 1 45 110 [(7, 24, 1), ((-1), 8, 1), (63, 472, 1)] = true := by decide +kernel

-- 48746a1: 22 primes
set_option maxHeartbeats 0 in
theorem c48746a1_cert0 : certAll 1 0 0 (-15) 121 [(5, 3, 13, 3), (7, 3, 17, 3), (11, 5, 3, 13), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (47, 3, 17, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c48746a1_cert1 : certAll 1 0 0 (-15) 121 [(53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c48746a1_gens : allOn 1 0 0 (-15) 121 [((-2), 13, 1), (6, 13, 1), (2, 9, 1)] = true := by decide +kernel

-- 48856a1: 22 primes
set_option maxHeartbeats 0 in
theorem c48856a1_cert0 : certAll 0 1 0 (-1465) 21099 [(5, 3, 13, 3), (7, 3, 17, 3), (11, 5, 3, 7), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 19, 3), (29, 3, 5, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 17, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c48856a1_cert1 : certAll 0 1 0 (-1465) 21099 [(53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 17, 3), (73, 17, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c48856a1_gens : allOn 0 1 0 (-1465) 21099 [(29, 62, 1), (23, 10, 1), (21, 6, 1)] = true := by decide +kernel

-- 49183a1: 21 primes
set_option maxHeartbeats 0 in
theorem c49183a1_cert0 : certAll 1 0 0 (-1611) 24754 [(5, 2, 17, 2), (7, 3, 5, 3), (13, 2, 7, 2), (17, 2, 3, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 7, 2), (37, 3, 2, 2), (41, 2, 3, 2), (43, 17, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c49183a1_cert1 : certAll 1 0 0 (-1611) 24754 [(53, 3, 2, 2), (59, 2, 3, 2), (61, 2, 5, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (83, 2, 3, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c49183a1_gens : allOn 1 0 0 (-1611) 24754 [(38, 118, 1), (615, (-239), 27), (22, (-2), 1)] = true := by decide +kernel

-- 49259a1: 20 primes
set_option maxHeartbeats 0 in
theorem c49259a1_cert0 : certAll 1 (-1) 1 159 (-450) [(5, 2, 13, 2), (11, 3, 2, 2), (13, 2, 3, 2), (17, 2, 5, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (37, 11, 2, 2), (43, 5, 2, 2), (47, 2, 11, 2), (53, 3, 2, 2), (59, 2, 19, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c49259a1_cert1 : certAll 1 (-1) 1 159 (-450) [(61, 2, 3, 2), (67, 5, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 5, 2, 2), (83, 2, 11, 2), (89, 2, 5, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c49259a1_gens : allOn 1 (-1) 1 159 (-450) [(4, 13, 1), (66, 509, 1), (24, 117, 1)] = true := by decide +kernel

-- 49411a1: 22 primes
set_option maxHeartbeats 0 in
theorem c49411a1_cert0 : certAll 0 1 1 (-9) 12 [(5, 3, 23, 3), (7, 3, 13, 3), (11, 5, 3, 5), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c49411a1_cert1 : certAll 0 1 1 (-9) 12 [(47, 3, 11, 3), (53, 3, 5, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 23, 3), (73, 11, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 19, 3, 3)] = true := by decide +kernel
theorem c49411a1_gens : allOn 0 1 1 (-9) 12 [(2, 2, 1), (0, 3, 1), (4, 7, 1)] = true := by decide +kernel

-- 49626a1: 21 primes
set_option maxHeartbeats 0 in
theorem c49626a1_cert0 : certAll 1 (-1) 0 (-9) 49 [(5, 7, 13, 7), (7, 5, 11, 5), (11, 5, 17, 7), (13, 11, 5, 5), (17, 7, 5, 5), (19, 5, 7, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 11, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5), (47, 5, 11, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c49626a1_cert1 : certAll 1 (-1) 0 (-9) 49 [(53, 7, 5, 5), (59, 5, 17, 5), (61, 17, 5, 5), (71, 5, 31, 5), (73, 31, 5, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c49626a1_gens : allOn 1 (-1) 0 (-9) 49 [(2, 5, 1), ((-4), 5, 1), ((-1), 8, 1)] = true := by decide +kernel

-- 49648d1: 21 primes
set_option maxHeartbeats 0 in
theorem c49648d1_cert0 : certAll 0 0 0 (-2011) 34714 [(5, 3, 13, 3), (7, 5, 3, 3), (11, 3, 13, 3), (13, 23, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 13, 3), (31, 5, 3, 3), (37, 11, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3), (47, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c49648d1_cert1 : certAll 0 0 0 (-2011) 34714 [(53, 3, 5, 3), (59, 3, 23, 3), (61, 11, 3, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 13, 3, 3), (79, 5, 3, 3), (89, 3, 5, 3), (97, 13, 3, 3)] = true := by decide +kernel
theorem c49648d1_gens : allOn 0 0 0 (-2011) 34714 [(19, 58, 1), (25, 8, 1), (27, 10, 1)] = true := by decide +kernel

-- 49831a1: 23 primes
set_option maxHeartbeats 0 in
theorem c49831a1_cert0 : certAll 1 0 0 (-79) 264 [(5, 2, 13, 2), (7, 3, 23, 3), (11, 5, 2, 2), (13, 2, 5, 2), (17, 2, 3, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 7, 2), (37, 3, 2, 2), (41, 2, 3, 2), (43, 5, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c49831a1_cert1 : certAll 1 0 0 (-79) 264 [(47, 2, 17, 2), (53, 3, 2, 2), (59, 2, 3, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (83, 2, 3, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c49831a1_gens : allOn 1 0 0 (-79) 264 [(5, (-3), 1), (4, 2, 1), ((-1), 19, 1)] = true := by decide +kernel

-- 50029c1: 19 primes
set_option maxHeartbeats 0 in
theorem c50029c1_cert0 : certAll 0 1 1 (-30) 60 [(5, 3, 2, 3), (11, 2, 3, 13), (13, 3, 2, 3), (17, 13, 2, 3), (19, 2, 3, 3), (23, 2, 11, 3), (29, 3, 2, 3), (37, 3, 2, 3), (41, 11, 2, 3), (43, 2, 3, 3), (47, 2, 11, 3), (59, 2, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c50029c1_cert1 : certAll 0 1 1 (-30) 60 [(61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 17, 3), (79, 2, 13, 3), (83, 2, 3, 3), (89, 11, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c50029c1_gens : allOn 0 1 1 (-30) 60 [(2, 3, 1), ((-5), 10, 1), (9, 24, 1)] = true := by decide +kernel

-- 50121a1: 23 primes
set_option maxHeartbeats 0 in
theorem c50121a1_cert0 : certAll 0 0 1 (-147) 706 [(5, 7, 2, 7), (7, 2, 17, 5), (11, 2, 19, 7), (13, 11, 2, 5), (17, 7, 2, 5), (19, 2, 7, 5), (23, 2, 11, 5), (29, 7, 2, 5), (31, 2, 7, 5), (37, 17, 2, 5), (41, 7, 2, 7), (43, 2, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c50121a1_cert1 : certAll 0 0 1 (-147) 706 [(47, 2, 23, 5), (53, 7, 2, 5), (59, 2, 19, 5), (61, 11, 2, 5), (67, 2, 7, 5), (71, 2, 11, 5), (73, 11, 2, 5), (79, 2, 7, 5), (83, 2, 19, 5), (89, 7, 2, 5), (97, 11, 2, 5)] = true := by decide +kernel
theorem c50121a1_gens : allOn 0 0 1 (-147) 706 [(7, 4, 1), (4, 13, 1), (16, 49, 1)] = true := by decide +kernel

-- 50360a1: 21 primes
set_option maxHeartbeats 0 in
theorem c50360a1_cert0 : certAll 0 0 0 (-28) 148 [(7, 11, 3, 3), (11, 3, 23, 3), (13, 11, 3, 3), (17, 3, 11, 3), (19, 13, 3, 3), (23, 3, 19, 3), (29, 3, 13, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 11, 3), (43, 13, 3, 3), (47, 3, 19, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c50360a1_cert1 : certAll 0 0 0 (-28) 148 [(53, 3, 13, 3), (59, 3, 11, 3), (61, 11, 3, 3), (67, 13, 3, 3), (71, 3, 17, 3), (73, 17, 3, 3), (79, 11, 3, 3), (83, 3, 11, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c50360a1_gens : allOn 0 0 0 (-28) 148 [(4, 10, 1), ((-6), 10, 1), (14, 50, 1)] = true := by decide +kernel

-- 50382f1: 20 primes
set_option maxHeartbeats 0 in
theorem c50382f1_cert0 : certAll 1 (-1) 0 (-51) 161 [(5, 7, 17, 7), (7, 5, 19, 5), (11, 7, 23, 7), (13, 5, 7, 5), (17, 5, 23, 5), (19, 5, 7, 5), (23, 7, 5, 5), (37, 23, 5, 5), (43, 5, 7, 5), (47, 7, 5, 5), (53, 7, 5, 5), (59, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c50382f1_cert1 : certAll 1 (-1) 0 (-51) 161 [(61, 5, 7, 5), (67, 17, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 7, 5), (83, 5, 23, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c50382f1_gens : allOn 1 (-1) 0 (-51) 161 [(4, 1, 1), (1, 10, 1), (7, 7, 1)] = true := by decide +kernel

-- 50744c1: 21 primes
set_option maxHeartbeats 0 in
theorem c50744c1_cert0 : certAll 0 1 0 (-20) 64 [(5, 3, 17, 3), (7, 3, 13, 3), (11, 5, 3, 7), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c50744c1_cert1 : certAll 0 1 0 (-20) 64 [(53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 17, 3), (73, 11, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3)] = true := by decide +kernel
theorem c50744c1_gens : allOn 0 1 0 (-20) 64 [(2, 6, 1), ((-2), 10, 1), (4, 8, 1)] = true := by decide +kernel

-- 50862a1: 21 primes
set_option maxHeartbeats 0 in
theorem c50862a1_cert0 : certAll 1 1 0 (-172) 820 [(5, 13, 17, 13), (11, 5, 19, 13), (13, 11, 5, 5), (17, 13, 5, 5), (19, 5, 13, 5), (23, 5, 11, 5), (29, 11, 5, 5), (31, 5, 13, 5), (37, 11, 5, 5), (41, 11, 5, 11), (43, 5, 11, 5), (47, 5, 11, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c50862a1_cert1 : certAll 1 1 0 (-172) 820 [(59, 5, 23, 5), (61, 19, 5, 5), (67, 5, 13, 5), (71, 5, 19, 5), (73, 19, 5, 5), (79, 5, 13, 5), (83, 5, 11, 5), (89, 11, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c50862a1_gens : allOn 1 1 0 (-172) 820 [(6, 4, 1), ((-8), 46, 1), (34, 172, 1)] = true := by decide +kernel

-- 51034a1: 20 primes
set_option maxHeartbeats 0 in
theorem c51034a1_cert0 : certAll 1 (-1) 0 (-91) (-167) [(5, 3, 7, 3), (7, 5, 3, 3), (11, 3, 7, 3), (13, 5, 3, 3), (23, 3, 5, 3), (29, 3, 13, 3), (31, 7, 3, 3), (37, 7, 3, 3), (41, 3, 11, 3), (43, 5, 3, 3), (47, 3, 5, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c51034a1_cert1 : certAll 1 (-1) 0 (-91) (-167) [(59, 3, 5, 3), (61, 5, 3, 3), (67, 7, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c51034a1_gens : allOn 1 (-1) 0 (-91) (-167) [(31, 146, 1), ((-3), (-7), 1), (12, 13, 1)] = true := by decide +kernel

-- 51052a1: 22 primes
set_option maxHeartbeats 0 in
theorem c51052a1_cert0 : certAll 0 1 0 (-169) 792 [(5, 3, 7, 3), (7, 3, 13, 3), (11, 5, 3, 5), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 17, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c51052a1_cert1 : certAll 0 1 0 (-169) 792 [(47, 3, 17, 3), (53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 29, 3), (73, 17, 3, 3), (79, 3, 7, 3), (89, 7, 3, 3), (97, 23, 3, 3)] = true := by decide +kernel
theorem c51052a1_gens : allOn 0 1 0 (-169) 792 [(7, 1, 1), (9, 9, 1), (13, 31, 1)] = true := by decide +kernel

-- 51065c1: 20 primes
set_option maxHeartbeats 0 in
theorem c51065c1_cert0 : certAll 0 1 1 (-56) 156 [(11, 2, 3, 13), (13, 3, 2, 3), (17, 13, 2, 3), (19, 2, 3, 3), (23, 2, 11, 3), (29, 3, 2, 3), (31, 2, 13, 3), (37, 3, 2, 3), (41, 11, 2, 3), (43, 2, 3, 3), (47, 2, 11, 3), (53, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c51065c1_cert1 : certAll 0 1 1 (-56) 156 [(61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 37, 3), (73, 23, 2, 3), (79, 2, 13, 3), (83, 2, 3, 3), (89, 11, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c51065c1_gens : allOn 0 1 1 (-56) 156 [((-3), 17, 1), (4, 3, 1), (11, 31, 1)] = true := by decide +kernel

-- 51094a1: 20 primes
set_option maxHeartbeats 0 in
theorem c51094a1_cert0 : certAll 1 (-1) 0 (-1169) 15709 [(5, 13, 7, 13), (7, 5, 11, 5), (11, 5, 7, 7), (13, 7, 5, 5), (17, 11, 5, 5), (23, 5, 7, 5), (29, 7, 5, 5), (31, 5, 13, 5), (37, 7, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5), (47, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c51094a1_cert1 : certAll 1 (-1) 0 (-1169) 15709 [(53, 7, 5, 5), (61, 11, 5, 5), (67, 5, 13, 5), (71, 5, 17, 5), (79, 5, 13, 5), (83, 5, 7, 5), (89, 7, 5, 5), (97, 7, 5, 5)] = true := by decide +kernel
theorem c51094a1_gens : allOn 1 (-1) 0 (-1169) 15709 [(66, 439, 1), (18, 7, 1), (174, 31, 8)] = true := by decide +kernel

-- 51317a1: 21 primes
set_option maxHeartbeats 0 in
theorem c51317a1_cert0 : certAll 1 (-1) 1 (-9) 204 [(5, 2, 43, 2), (11, 3, 2, 2), (13, 2, 3, 2), (17, 2, 11, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 11, 2, 2), (41, 2, 11, 2), (43, 5, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c51317a1_cert1 : certAll 1 (-1) 1 (-9) 204 [(53, 3, 2, 2), (61, 2, 3, 2), (67, 19, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 5, 2, 2), (83, 2, 11, 2), (89, 2, 5, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c51317a1_gens : allOn 1 (-1) 1 (-9) 204 [(8, 20, 1), (1, 13, 1), ((-34), 111, 8)] = true := by decide +kernel

-- 51536b1: 23 primes
set_option maxHeartbeats 0 in
theorem c51536b1_cert0 : certAll 0 1 0 (-72) 196 [(5, 3, 17, 3), (7, 3, 13, 3), (11, 7, 3, 7), (13, 3, 7, 3), (17, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 11, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c51536b1_cert1 : certAll 0 1 0 (-72) 196 [(47, 3, 5, 3), (53, 3, 5, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 11, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c51536b1_gens : allOn 0 1 0 (-72) 196 [(6, 4, 1), (2, 8, 1), (10, 24, 1)] = true := by decide +kernel

-- 51822d1: 22 primes
set_option maxHeartbeats 0 in
theorem c51822d1_cert0 : certAll 1 (-1) 0 (-279) 1849 [(5, 7, 13, 7), (7, 5, 29, 5), (11, 5, 17, 7), (13, 11, 5, 5), (17, 7, 5, 5), (19, 5, 7, 5), (23, 5, 11, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 17, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c51822d1_cert1 : certAll 1 (-1) 0 (-279) 1849 [(47, 5, 17, 5), (53, 7, 5, 5), (61, 11, 5, 5), (67, 5, 7, 5), (71, 5, 11, 5), (73, 11, 5, 5), (79, 5, 7, 5), (83, 5, 17, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c51822d1_gens : allOn 1 (-1) 0 (-279) 1849 [(11, (-1), 1), (8, 5, 1), (20, 53, 1)] = true := by decide +kernel

-- 51962a1: 23 primes
set_option maxHeartbeats 0 in
theorem c51962a1_cert0 : certAll 1 (-1) 0 (-31) 73 [(5, 3, 23, 3), (7, 5, 3, 3), (11, 3, 17, 3), (13, 5, 3, 3), (17, 3, 19, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 11, 3), (31, 11, 3, 3), (37, 17, 3, 3), (41, 3, 17, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c51962a1_cert1 : certAll 1 (-1) 0 (-31) 73 [(47, 3, 5, 3), (53, 3, 5, 3), (59, 3, 5, 3), (61, 5, 3, 3), (67, 19, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 5, 3, 3), (83, 3, 17, 3), (89, 3, 5, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c51962a1_gens : allOn 1 (-1) 0 (-31) 73 [(4, (-1), 1), (2, 3, 1), (3, (-2), 1)] = true := by decide +kernel

-- 52013a1: 20 primes
set_option maxHeartbeats 0 in
theorem c52013a1_cert0 : certAll 1 (-1) 1 (-33) 90 [(5, 2, 7, 2), (7, 17, 3, 3), (11, 3, 2, 2), (17, 2, 5, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 5, 2, 2), (41, 2, 17, 2), (43, 7, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c52013a1_cert1 : certAll 1 (-1) 1 (-33) 90 [(53, 3, 2, 2), (59, 2, 7, 2), (61, 2, 3, 2), (67, 5, 2, 2), (73, 2, 3, 2), (79, 5, 2, 2), (89, 2, 17, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c52013a1_gens : allOn 1 (-1) 1 (-33) 90 [(7, 9, 1), ((-6), 9, 1), (4, 1, 1)] = true := by decide +kernel

-- 52158a1: 23 primes
set_option maxHeartbeats 0 in
theorem c52158a1_cert0 : certAll 1 1 0 (-7) 25 [(5, 17, 7, 17), (7, 5, 11, 5), (11, 5, 7, 7), (13, 7, 5, 5), (17, 11, 5, 5), (19, 5, 11, 5), (23, 5, 7, 5), (29, 7, 5, 5), (31, 5, 19, 5), (37, 7, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c52158a1_cert1 : certAll 1 1 0 (-7) 25 [(47, 5, 7, 5), (53, 7, 5, 5), (59, 5, 11, 5), (61, 11, 5, 5), (67, 5, 17, 5), (71, 5, 29, 5), (73, 11, 5, 5), (79, 5, 19, 5), (83, 5, 7, 5), (89, 7, 5, 5), (97, 7, 5, 5)] = true := by decide +kernel
theorem c52158a1_gens : allOn 1 1 0 (-7) 25 [((-2), 7, 1), (4, 7, 1), (1, 4, 1)] = true := by decide +kernel

-- 52277b1: 20 primes
set_option maxHeartbeats 0 in
theorem c52277b1_cert0 : certAll 0 1 1 (-15) 15 [(5, 3, 7, 3), (7, 3, 13, 3), (11, 5, 3, 7), (13, 3, 5, 3), (17, 11, 3, 3), (19, 5, 3, 3), (29, 3, 5, 3), (31, 3, 13, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c52277b1_cert1 : certAll 0 1 1 (-15) 15 [(59, 5, 3, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 3, 11, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c52277b1_gens : allOn 0 1 1 (-15) 15 [(1, 1, 1), (3, 2, 1), ((-3), 6, 1)] = true := by decide +kernel

-- 52396b1: 22 primes
set_option maxHeartbeats 0 in
theorem c52396b1_cert0 : certAll 0 (-1) 0 (-532) 4904 [(5, 11, 3, 97), (7, 3, 17, 3), (11, 13, 7, 7), (13, 3, 19, 3), (17, 3, 7, 3), (19, 3, 17, 3), (23, 13, 3, 3), (29, 3, 11, 3), (31, 7, 3, 3), (37, 7, 3, 3), (41, 3, 13, 3), (43, 3, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c52396b1_cert1 : certAll 0 (-1) 0 (-532) 4904 [(47, 11, 3, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 7, 3, 3), (71, 7, 3, 3), (73, 3, 7, 3), (79, 3, 11, 3), (83, 3, 7, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c52396b1_gens : allOn 0 (-1) 0 (-532) 4904 [(14, 2, 1), (10, 22, 1), (17, 22, 1)] = true := by decide +kernel

-- 53022b1: 18 primes
set_option maxHeartbeats 0 in
theorem c53022b1_cert0 : certAll 1 1 0 (-17) (-15) [(5, 19, 7, 43), (7, 5, 13, 5), (11, 5, 7, 7), (13, 7, 5, 5), (17, 7, 5, 5), (19, 5, 13, 5), (23, 5, 43, 5), (31, 5, 7, 5), (37, 7, 5, 5), (43, 5, 13, 5), (47, 5, 11, 5), (59, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c53022b1_cert1 : certAll 1 1 0 (-17) (-15) [(61, 7, 5, 5), (67, 5, 13, 5), (71, 5, 11, 5), (73, 23, 5, 5), (83, 5, 7, 5), (97, 23, 5, 5)] = true := by decide +kernel
theorem c53022b1_gens : allOn 1 1 0 (-17) (-15) [((-4), 5, 1), ((-1), 2, 1), ((-2), 5, 1)] = true := by decide +kernel

-- 53083a1: 22 primes
set_option maxHeartbeats 0 in
theorem c53083a1_cert0 : certAll 0 1 1 (-20) 30 [(5, 3, 2, 3), (7, 2, 13, 3), (11, 2, 3, 7), (13, 3, 2, 3), (17, 7, 2, 3), (19, 2, 3, 3), (23, 2, 11, 3), (29, 3, 2, 3), (31, 2, 7, 3), (37, 3, 2, 3), (41, 7, 2, 3), (43, 2, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c53083a1_cert1 : certAll 0 1 1 (-20) 30 [(53, 3, 2, 3), (59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 11, 3), (73, 11, 2, 3), (79, 2, 7, 3), (83, 2, 3, 3), (89, 7, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c53083a1_gens : allOn 0 1 1 (-20) 30 [(2, 1, 1), (3, 2, 1), (1, 3, 1)] = true := by decide +kernel

-- 53122a1: 22 primes
set_option maxHeartbeats 0 in
theorem c53122a1_cert0 : certAll 1 (-1) 0 47 (-35) [(5, 3, 13, 3), (7, 5, 3, 3), (11, 3, 43, 3), (13, 31, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 11, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3), (47, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c53122a1_cert1 : certAll 1 (-1) 0 47 (-35) [(53, 3, 5, 3), (59, 3, 11, 3), (61, 11, 3, 3), (67, 5, 3, 3), (71, 3, 47, 3), (73, 11, 3, 3), (79, 5, 3, 3), (83, 3, 11, 3), (89, 3, 5, 3), (97, 31, 3, 3)] = true := by decide +kernel
theorem c53122a1_gens : allOn 1 (-1) 0 47 (-35) [(2, 7, 1), (18, 71, 1), (34, 183, 1)] = true := by decide +kernel

-- 53237b1: 23 primes
set_option maxHeartbeats 0 in
theorem c53237b1_cert0 : certAll 0 1 1 (-10) (-10) [(5, 3, 2, 3), (7, 2, 11, 3), (11, 2, 3, 7), (13, 3, 2, 3), (17, 7, 2, 3), (19, 2, 3, 3), (23, 2, 11, 3), (29, 3, 2, 3), (31, 2, 7, 3), (37, 3, 2, 3), (41, 7, 2, 3), (43, 2, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c53237b1_cert1 : certAll 0 1 1 (-10) (-10) [(47, 2, 11, 3), (53, 3, 2, 3), (59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 29, 3), (73, 11, 2, 3), (79, 2, 7, 3), (83, 2, 3, 3), (89, 7, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c53237b1_gens : allOn 0 1 1 (-10) (-10) [((-1), 0, 1), ((-2), 2, 1), ((-3), 1, 1)] = true := by decide +kernel

-- 53238e1: 20 primes
set_option maxHeartbeats 0 in
theorem c53238e1_cert0 : certAll 1 1 0 (-22) 40 [(5, 7, 13, 7), (7, 5, 11, 5), (11, 5, 67, 7), (13, 11, 5, 5), (17, 7, 5, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 11, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5), (53, 7, 5, 5), (59, 5, 29, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c53238e1_cert1 : certAll 1 1 0 (-22) 40 [(61, 17, 5, 5), (67, 5, 7, 5), (71, 5, 17, 5), (73, 17, 5, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c53238e1_gens : allOn 1 1 0 (-22) 40 [(4, 4, 1), ((-2), (-8), 1), (1, 4, 1)] = true := by decide +kernel

-- 53461b1: 20 primes
set_option maxHeartbeats 0 in
theorem c53461b1_cert0 : certAll 0 (-1) 1 (-16) 28 [(5, 7, 2, 7), (7, 2, 5, 3), (11, 2, 5, 7), (17, 3, 2, 3), (19, 2, 7, 3), (23, 2, 3, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 5, 2, 3), (41, 3, 2, 3), (43, 2, 5, 3), (47, 2, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c53461b1_cert1 : certAll 0 (-1) 1 (-16) 28 [(53, 5, 2, 3), (59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 3, 3), (73, 3, 2, 3), (83, 2, 5, 3), (97, 5, 2, 3)] = true := by decide +kernel
theorem c53461b1_gens : allOn 0 (-1) 1 (-16) 28 [(2, 0, 1), (1, 3, 1), (4, 3, 1)] = true := by decide +kernel

-- 53486d1: 21 primes
set_option maxHeartbeats 0 in
theorem c53486d1_cert0 : certAll 1 (-1) 0 (-344) 2544 [(5, 19, 7, 43), (7, 5, 43, 5), (11, 5, 7, 7), (13, 7, 5, 5), (17, 29, 5, 5), (19, 5, 23, 5), (23, 5, 7, 5), (29, 7, 5, 5), (31, 5, 37, 5), (37, 7, 5, 5), (43, 5, 7, 5), (53, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c53486d1_cert1 : certAll 1 (-1) 0 (-344) 2544 [(59, 5, 19, 5), (61, 11, 5, 5), (67, 5, 29, 5), (71, 5, 11, 5), (73, 29, 5, 5), (79, 5, 11, 5), (83, 5, 7, 5), (89, 7, 5, 5), (97, 7, 5, 5)] = true := by decide +kernel
theorem c53486d1_gens : allOn 1 (-1) 0 (-344) 2544 [(12, 0, 1), (11, (-6), 1), ((-4), 64, 1)] = true := by decide +kernel

-- 53916a1: 21 primes
set_option maxHeartbeats 0 in
theorem c53916a1_cert0 : certAll 0 (-1) 0 (-45) 126 [(5, 7, 13, 7), (7, 5, 11, 5), (11, 5, 23, 7), (13, 11, 5, 5), (19, 5, 7, 5), (23, 5, 11, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 11, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5), (47, 5, 11, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c53916a1_cert1 : certAll 0 (-1) 0 (-45) 126 [(53, 7, 5, 5), (59, 5, 23, 5), (61, 29, 5, 5), (67, 5, 7, 5), (71, 5, 29, 5), (73, 23, 5, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c53916a1_gens : allOn 0 (-1) 0 (-45) 126 [(3, 3, 1), (5, 1, 1), (6, 6, 1)] = true := by decide +kernel

-- 53926e1: 20 primes
set_option maxHeartbeats 0 in
theorem c53926e1_cert0 : certAll 1 0 0 (-92) 784 [(5, 3, 13, 3), (7, 3, 19, 3), (11, 7, 3, 7), (13, 3, 7, 3), (17, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 13, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (47, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c53926e1_cert1 : certAll 1 0 0 (-92) 784 [(53, 3, 5, 3), (61, 3, 7, 3), (67, 13, 3, 3), (71, 3, 5, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c53926e1_gens : allOn 1 0 0 (-92) 784 [((-8), 36, 1), (8, 20, 1), (24, 100, 1)] = true := by decide +kernel

-- 53957b1: 20 primes
set_option maxHeartbeats 0 in
theorem c53957b1_cert0 : certAll 0 1 1 (-50) 120 [(5, 3, 2, 3), (7, 2, 53, 3), (13, 3, 2, 3), (17, 23, 2, 3), (19, 2, 3, 3), (23, 2, 7, 3), (29, 3, 2, 3), (31, 2, 41, 3), (37, 3, 2, 3), (41, 7, 2, 3), (43, 2, 3, 3), (53, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c53957b1_cert1 : certAll 0 1 1 (-50) 120 [(59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 19, 3), (73, 19, 2, 3), (83, 2, 3, 3), (89, 7, 2, 3), (97, 7, 2, 3)] = true := by decide +kernel
theorem c53957b1_gens : allOn 0 1 1 (-50) 120 [(4, 0, 1), (3, 2, 1), (5, 4, 1)] = true := by decide +kernel

-- 54489b1: 22 primes
set_option maxHeartbeats 0 in
theorem c54489b1_cert0 : certAll 1 1 1 (-205) 56 [(5, 2, 43, 2), (7, 5, 29, 5), (11, 5, 2, 2), (13, 2, 5, 2), (17, 2, 5, 2), (19, 2, 7, 2), (23, 5, 2, 2), (29, 7, 2, 2), (31, 2, 7, 2), (37, 11, 2, 2), (43, 5, 2, 2), (47, 2, 11, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c54489b1_cert1 : certAll 1 1 1 (-205) 56 [(53, 7, 2, 2), (59, 2, 11, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 5, 2, 2), (73, 2, 5, 2), (79, 5, 2, 2), (83, 2, 11, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c54489b1_gens : allOn 1 1 1 (-205) 56 [(68, 519, 1), ((-14), 27, 1), (14, 6, 1)] = true := by decide +kernel

-- 54512b1: 23 primes
set_option maxHeartbeats 0 in
theorem c54512b1_cert0 : certAll 0 0 0 (-91) 346 [(5, 3, 17, 3), (7, 5, 3, 3), (11, 3, 19, 3), (13, 23, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 19, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 11, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c54512b1_cert1 : certAll 0 0 0 (-91) 346 [(47, 3, 11, 3), (53, 3, 5, 3), (59, 3, 19, 3), (61, 11, 3, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 19, 3, 3), (79, 5, 3, 3), (83, 3, 11, 3), (89, 3, 5, 3), (97, 19, 3, 3)] = true := by decide +kernel
theorem c54512b1_gens : allOn 0 0 0 (-91) 346 [(5, 4, 1), (1, 16, 1), (9, 16, 1)] = true := by decide +kernel

-- 55064b1: 21 primes
set_option maxHeartbeats 0 in
theorem c55064b1_cert0 : certAll 0 1 0 (-19) 30 [(5, 3, 7, 3), (7, 3, 11, 3), (11, 5, 3, 5), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c55064b1_cert1 : certAll 0 1 0 (-19) 30 [(53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 31, 3), (73, 31, 3, 3), (79, 3, 7, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c55064b1_gens : allOn 0 1 0 (-19) 30 [(3, 3, 1), (2, 2, 1), ((-1), 7, 1)] = true := by decide +kernel

-- 55783e1: 18 primes
set_option maxHeartbeats 0 in
theorem c55783e1_cert0 : certAll 1 1 1 (-475) 3786 [(5, 2, 3, 2), (11, 5, 2, 2), (17, 2, 5, 2), (19, 2, 17, 2), (23, 5, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 17, 2, 2), (41, 2, 5, 2), (43, 3, 2, 2), (47, 2, 3, 2), (59, 2, 3, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c55783e1_cert1 : certAll 1 1 1 (-475) 3786 [(61, 2, 5, 2), (67, 5, 2, 2), (73, 2, 5, 2), (83, 2, 17, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c55783e1_gens : allOn 1 1 1 (-475) 3786 [(11, 1, 1), (18, 29, 1), (14, 4, 1)] = true := by decide +kernel

-- 55846a1: 21 primes
set_option maxHeartbeats 0 in
theorem c55846a1_cert0 : certAll 1 (-1) 0 (-154) 784 [(5, 3, 13, 3), (11, 3, 29, 3), (13, 11, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 23, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c55846a1_cert1 : certAll 1 (-1) 0 (-154) 784 [(59, 3, 17, 3), (61, 11, 3, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 5, 3, 3), (83, 3, 17, 3), (89, 3, 5, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c55846a1_gens : allOn 1 (-1) 0 (-154) 784 [(7, 0, 1), (0, 28, 1), (8, 0, 1)] = true := by decide +kernel

-- 55935g1: 20 primes
set_option maxHeartbeats 0 in
theorem c55935g1_cert0 : certAll 0 0 1 (-273) 2178 [(7, 2, 19, 19), (13, 17, 2, 7), (17, 7, 2, 7), (19, 2, 7, 7), (23, 2, 17, 7), (29, 7, 2, 7), (31, 2, 7, 7), (37, 17, 2, 7), (41, 7, 2, 7), (43, 2, 7, 7), (47, 2, 17, 7), (53, 7, 2, 7)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c55935g1_cert1 : certAll 0 0 1 (-273) 2178 [(59, 2, 19, 7), (61, 19, 2, 7), (67, 2, 7, 7), (73, 19, 2, 7), (79, 2, 7, 7), (83, 2, 17, 7), (89, 7, 2, 7), (97, 17, 2, 7)] = true := by decide +kernel
theorem c55935g1_gens : allOn 0 0 1 (-273) 2178 [(17, 49, 1), (6, 27, 1), (11, 22, 1)] = true := by decide +kernel

-- 56052g1: 22 primes
set_option maxHeartbeats 0 in
theorem c56052g1_cert0 : certAll 0 0 0 (-72) 225 [(5, 7, 37, 7), (7, 5, 19, 5), (11, 5, 13, 7), (13, 11, 5, 5), (17, 7, 5, 5), (19, 5, 7, 5), (23, 5, 13, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 11, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c56052g1_cert1 : certAll 0 0 0 (-72) 225 [(47, 5, 13, 5), (53, 7, 5, 5), (61, 11, 5, 5), (67, 5, 7, 5), (71, 5, 23, 5), (73, 13, 5, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 23, 5, 5)] = true := by decide +kernel
theorem c56052g1_gens : allOn 0 0 0 (-72) 225 [(6, 3, 1), (0, 15, 1), (4, 1, 1)] = true := by decide +kernel

-- 56441b1: 21 primes
set_option maxHeartbeats 0 in
theorem c56441b1_cert0 : certAll 1 1 1 (-55) (-144) [(5, 2, 3, 2), (13, 2, 5, 2), (17, 2, 5, 2), (19, 2, 17, 2), (23, 5, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 17, 2, 2), (41, 2, 5, 2), (43, 3, 2, 2), (47, 2, 3, 2), (53, 19, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c56441b1_cert1 : certAll 1 1 1 (-55) (-144) [(59, 2, 3, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 5, 2, 2), (73, 2, 5, 2), (79, 3, 2, 2), (83, 2, 29, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c56441b1_gens : allOn 1 1 1 (-55) (-144) [((-4), 7, 1), ((-6), 6, 1), (8, (-1), 1)] = true := by decide +kernel

-- 56982a1: 23 primes
set_option maxHeartbeats 0 in
theorem c56982a1_cert0 : certAll 1 1 0 (-11) 81 [(5, 11, 13, 23), (7, 5, 29, 5), (11, 5, 23, 5), (13, 11, 5, 5), (17, 7, 5, 5), (19, 5, 7, 7), (23, 5, 11, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 19, 5, 5), (41, 7, 5, 5), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c56982a1_cert1 : certAll 1 1 0 (-11) 81 [(47, 5, 19, 5), (53, 7, 5, 5), (59, 5, 29, 5), (61, 11, 5, 5), (67, 5, 7, 5), (71, 5, 11, 5), (73, 11, 5, 5), (79, 5, 7, 5), (83, 5, 19, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c56982a1_gens : allOn 1 1 0 (-11) 81 [((-4), 11, 1), (5, 11, 1), (14, 47, 1)] = true := by decide +kernel

-- 56982b1: 22 primes
set_option maxHeartbeats 0 in
theorem c56982b1_cert0 : certAll 1 1 0 (-382) 2740 [(5, 7, 13, 7), (7, 5, 19, 5), (11, 5, 23, 7), (13, 11, 5, 5), (17, 7, 5, 5), (19, 5, 7, 5), (23, 5, 31, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 11, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c56982b1_cert1 : certAll 1 1 0 (-382) 2740 [(47, 5, 23, 5), (53, 7, 5, 5), (59, 5, 11, 5), (61, 11, 5, 5), (67, 5, 7, 5), (73, 31, 5, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 23, 5, 5)] = true := by decide +kernel
theorem c56982b1_gens : allOn 1 1 0 (-382) 2740 [(4, 34, 1), (12, 2, 1), (20, 50, 1)] = true := by decide +kernel

-- 58397c1: 21 primes
set_option maxHeartbeats 0 in
theorem c58397c1_cert0 : certAll 1 0 0 (-35) 76 [(5, 2, 7, 2), (7, 3, 17, 3), (11, 5, 2, 2), (13, 2, 5, 2), (17, 2, 3, 2), (19, 2, 3, 2), (29, 3, 2, 2), (31, 2, 7, 2), (37, 3, 2, 2), (43, 5, 2, 2), (47, 2, 11, 2), (53, 3, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c58397c1_cert1 : certAll 1 0 0 (-35) 76 [(59, 2, 3, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (83, 2, 3, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c58397c1_gens : allOn 1 0 0 (-35) 76 [(3, (-2), 1), (4, 0, 1), (1, 6, 1)] = true := by decide +kernel

-- 58739a1: 22 primes
set_option maxHeartbeats 0 in
theorem c58739a1_cert0 : certAll 0 0 1 (-104) 382 [(5, 17, 7, 17), (7, 5, 13, 5), (13, 5, 19, 5), (17, 5, 7, 5), (19, 5, 13, 5), (23, 13, 5, 5), (29, 5, 31, 7), (31, 7, 5, 5), (37, 7, 5, 5), (41, 5, 17, 5), (43, 5, 7, 5), (47, 13, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c58739a1_cert1 : certAll 0 0 1 (-104) 382 [(53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (67, 7, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 13, 5), (83, 5, 7, 5), (89, 7, 5, 5), (97, 7, 5, 5)] = true := by decide +kernel
theorem c58739a1_gens : allOn 0 0 1 (-104) 382 [(38, 226, 1), (2, 147, 8), (120, 62, 27)] = true := by decide +kernel

-- 58774b1: 21 primes
set_option maxHeartbeats 0 in
theorem c58774b1_cert0 : certAll 1 (-1) 0 2 16 [(5, 3, 7, 3), (7, 5, 3, 3), (11, 3, 7, 3), (13, 7, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 11, 3), (37, 7, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3), (47, 3, 11, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c58774b1_cert1 : certAll 1 (-1) 0 2 16 [(59, 3, 7, 3), (61, 7, 3, 3), (67, 5, 3, 3), (71, 3, 37, 3), (73, 19, 3, 3), (79, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c58774b1_gens : allOn 1 (-1) 0 2 16 [(0, 4, 1), ((-2), 2, 1), (2, 4, 1)] = true := by decide +kernel

-- 58939a1: 21 primes
set_option maxHeartbeats 0 in
theorem c58939a1_cert0 : certAll 0 1 1 9 9 [(5, 3, 7, 3), (7, 3, 5, 3), (11, 13, 3, 7), (13, 3, 19, 3), (19, 47, 3, 3), (23, 3, 5, 3), (31, 3, 13, 3), (37, 3, 13, 3), (41, 5, 3, 3), (43, 19, 3, 3), (47, 3, 5, 3), (53, 3, 19, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c58939a1_cert1 : certAll 0 1 1 9 9 [(59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 31, 3), (73, 19, 3, 3), (79, 3, 13, 3), (83, 13, 3, 3), (89, 5, 3, 3), (97, 5, 3, 3)] = true := by decide +kernel
theorem c58939a1_gens : allOn 0 1 1 9 9 [((-1), 0, 1), (1, 4, 1), ((-6), 9, 8)] = true := by decide +kernel

-- 59111a1: 21 primes
set_option maxHeartbeats 0 in
theorem c59111a1_cert0 : certAll 0 (-1) 1 0 42 [(5, 11, 2, 37), (7, 2, 17, 3), (11, 2, 7, 7), (17, 3, 2, 3), (19, 2, 17, 3), (23, 2, 3, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 7, 2, 3), (41, 3, 2, 3), (43, 2, 11, 3), (47, 2, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c59111a1_cert1 : certAll 0 (-1) 1 0 42 [(53, 23, 2, 3), (59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 3, 3), (73, 3, 2, 3), (83, 2, 7, 3), (89, 7, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c59111a1_gens : allOn 0 (-1) 1 0 42 [(0, 6, 1), (13, 45, 1), ((-2), 5, 1)] = true := by decide +kernel

-- 59450i1: 19 primes
set_option maxHeartbeats 0 in
theorem c59450i1_cert0 : certAll 1 0 1 (-131) 558 [(7, 3, 53, 3), (11, 7, 3, 7), (13, 3, 7, 3), (17, 7, 3, 3), (19, 11, 3, 3), (23, 3, 11, 3), (31, 3, 7, 3), (37, 3, 7, 3), (43, 13, 3, 3), (47, 3, 19, 3), (53, 3, 11, 3), (59, 7, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c59450i1_cert1 : certAll 1 0 1 (-131) 558 [(61, 3, 7, 3), (67, 13, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (83, 7, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c59450i1_gens : allOn 1 0 1 (-131) 558 [(3, 12, 1), (6, (-4), 1), (8, 2, 1), (7, (-4), 1)] = true := by decide +kernel

-- 59614a1: 20 primes
set_option maxHeartbeats 0 in
theorem c59614a1_cert0 : certAll 1 0 1 (-28) 42 [(5, 3, 13, 3), (7, 3, 47, 3), (11, 5, 3, 7), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (47, 3, 29, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c59614a1_cert1 : certAll 1 0 1 (-28) 42 [(59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (73, 11, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c59614a1_gens : allOn 1 0 1 (-28) 42 [(1, 3, 1), (5, 3, 1), ((-3), 11, 1)] = true := by decide +kernel

-- 59704d1: 20 primes
set_option maxHeartbeats 0 in
theorem c59704d1_cert0 : certAll 0 (-1) 0 (-4) 68 [(5, 7, 3, 7), (7, 3, 37, 3), (11, 5, 19, 5), (13, 3, 5, 3), (19, 3, 7, 3), (23, 5, 3, 3), (29, 3, 5, 3), (37, 11, 3, 3), (41, 3, 5, 3), (43, 3, 7, 3), (53, 7, 3, 3), (59, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c59704d1_cert1 : certAll 0 (-1) 0 (-4) 68 [(61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 7, 3), (83, 3, 11, 3), (89, 7, 3, 3), (97, 19, 3, 3)] = true := by decide +kernel
theorem c59704d1_gens : allOn 0 (-1) 0 (-4) 68 [((-4), 2, 1), (4, 10, 1), ((-2), 8, 1)] = true := by decide +kernel

-- 59936b1: 22 primes
set_option maxHeartbeats 0 in
theorem c59936b1_cert0 : certAll 0 1 0 (-145) 639 [(5, 3, 7, 3), (7, 3, 17, 3), (11, 5, 3, 7), (13, 3, 5, 3), (17, 7, 3, 3), (23, 3, 13, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 13, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c59936b1_cert1 : certAll 0 1 0 (-145) 639 [(53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 17, 3), (73, 13, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c59936b1_gens : allOn 0 1 0 (-145) 639 [(7, 4, 1), (5, 8, 1), ((-1), 28, 1)] = true := by decide +kernel

-- 60055b1: 20 primes
set_option maxHeartbeats 0 in
theorem c60055b1_cert0 : certAll 0 (-1) 1 (-30) 3306 [(7, 2, 11, 3), (11, 2, 17, 13), (13, 3, 2, 3), (17, 3, 2, 3), (19, 2, 7, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 11, 2, 3), (41, 3, 2, 3), (43, 2, 7, 3), (47, 2, 3, 3), (53, 7, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c60055b1_cert1 : certAll 0 (-1) 1 (-30) 3306 [(59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 3, 3), (73, 3, 2, 3), (79, 2, 7, 3), (89, 7, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c60055b1_gens : allOn 0 (-1) 1 (-30) 3306 [(10, 62, 1), (135, 1562, 1), ((-5), 57, 1)] = true := by decide +kernel

-- 60128a1: 23 primes
set_option maxHeartbeats 0 in
theorem c60128a1_cert0 : certAll 0 1 0 (-2) 16 [(5, 3, 13, 3), (7, 3, 11, 3), (11, 7, 3, 13), (13, 3, 7, 3), (17, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 13, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c60128a1_cert1 : certAll 0 1 0 (-2) 16 [(47, 3, 5, 3), (53, 3, 5, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 11, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c60128a1_gens : allOn 0 1 0 (-2) 16 [(0, 4, 1), ((-2), 4, 1), ((-3), 2, 1)] = true := by decide +kernel

-- 60215b1: 21 primes
set_option maxHeartbeats 0 in
theorem c60215b1_cert0 : certAll 0 1 1 20 134 [(7, 2, 11, 3), (11, 2, 3, 7), (13, 3, 2, 3), (17, 11, 2, 3), (19, 2, 3, 3), (23, 2, 7, 3), (29, 3, 2, 3), (31, 2, 19, 3), (37, 3, 2, 3), (41, 7, 2, 3), (43, 2, 3, 3), (47, 2, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c60215b1_cert1 : certAll 0 1 1 20 134 [(53, 3, 2, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 23, 3), (73, 11, 2, 3), (79, 2, 19, 3), (83, 2, 3, 3), (89, 7, 2, 3), (97, 7, 2, 3)] = true := by decide +kernel
theorem c60215b1_gens : allOn 0 1 1 20 134 [(1, 12, 1), ((-4), 2, 1), (26, 137, 1)] = true := by decide +kernel

-- 60296a1: 23 primes
set_option maxHeartbeats 0 in
theorem c60296a1_cert0 : certAll 0 (-1) 0 (-24) (-35) [(5, 7, 3, 7), (7, 3, 13, 3), (11, 5, 17, 5), (13, 3, 5, 3), (17, 3, 5, 3), (19, 3, 7, 3), (23, 5, 3, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 11, 3, 3), (41, 3, 5, 3), (43, 3, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c60296a1_cert1 : certAll 0 (-1) 0 (-24) (-35) [(47, 5, 3, 3), (53, 7, 3, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 7, 3), (83, 3, 11, 3), (89, 7, 3, 3), (97, 19, 3, 3)] = true := by decide +kernel
theorem c60296a1_gens : allOn 0 (-1) 0 (-24) (-35) [((-2), 1, 1), ((-3), 1, 1), ((-22), 13, 8)] = true := by decide +kernel

-- 60803a1: 20 primes
set_option maxHeartbeats 0 in
theorem c60803a1_cert0 : certAll 0 1 1 (-65) 195 [(5, 3, 17, 3), (7, 3, 13, 3), (11, 5, 3, 7), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (47, 3, 37, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c60803a1_cert1 : certAll 0 1 1 (-65) 195 [(59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (73, 11, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c60803a1_gens : allOn 0 1 1 (-65) 195 [((-5), 20, 1), (42, 37, 8), (111, 89, 27)] = true := by decide +kernel

-- 60892b1: 21 primes
set_option maxHeartbeats 0 in
theorem c60892b1_cert0 : certAll 0 0 0 (-1039) 12886 [(5, 3, 7, 3), (7, 5, 3, 3), (11, 3, 7, 3), (17, 3, 7, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 17, 3), (31, 7, 3, 3), (37, 7, 3, 3), (41, 3, 17, 3), (43, 5, 3, 3), (47, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c60892b1_cert1 : certAll 0 0 0 (-1039) 12886 [(53, 3, 5, 3), (59, 3, 5, 3), (61, 5, 3, 3), (67, 7, 3, 3), (73, 5, 3, 3), (79, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c60892b1_gens : allOn 0 0 0 (-1039) 12886 [(15, 26, 1), (23, 34, 1), (18, 4, 1)] = true := by decide +kernel

-- 61025b1: 21 primes
set_option maxHeartbeats 0 in
theorem c61025b1_cert0 : certAll 0 0 1 (-175) (-594) [(7, 2, 3, 3), (11, 2, 23, 3), (13, 11, 2, 3), (17, 3, 2, 3), (23, 2, 29, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 11, 2, 3), (41, 3, 2, 3), (43, 2, 3, 3), (47, 2, 23, 3), (53, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c61025b1_cert1 : certAll 0 0 1 (-175) (-594) [(59, 2, 11, 3), (61, 11, 2, 3), (67, 2, 3, 3), (71, 2, 17, 3), (73, 17, 2, 3), (79, 2, 3, 3), (83, 2, 11, 3), (89, 3, 2, 3), (97, 17, 2, 3)] = true := by decide +kernel
theorem c61025b1_gens : allOn 0 0 1 (-175) (-594) [((-10), 12, 1), ((-5), 12, 1), (20, 62, 1)] = true := by decide +kernel

-- 61075a1: 20 primes
set_option maxHeartbeats 0 in
theorem c61075a1_cert0 : certAll 0 0 1 (-475) 3906 [(11, 2, 17, 3), (13, 11, 2, 3), (17, 3, 2, 3), (19, 2, 3, 3), (23, 2, 17, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 11, 2, 3), (41, 3, 2, 3), (43, 2, 3, 3), (47, 2, 17, 3), (53, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c61075a1_cert1 : certAll 0 0 1 (-475) 3906 [(59, 2, 11, 3), (61, 11, 2, 3), (67, 2, 3, 3), (71, 2, 23, 3), (73, 29, 2, 3), (79, 2, 3, 3), (83, 2, 11, 3), (97, 17, 2, 3)] = true := by decide +kernel
theorem c61075a1_gens : allOn 0 0 1 (-475) 3906 [(25, 87, 1), ((-10), 87, 1), (15, 12, 1)] = true := by decide +kernel

-- 61229a1: 20 primes
set_option maxHeartbeats 0 in
theorem c61229a1_cert0 : certAll 0 0 1 53 1536 [(5, 3, 2, 3), (11, 2, 23, 3), (13, 11, 2, 3), (17, 3, 2, 3), (23, 2, 11, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 29, 2, 3), (41, 3, 2, 3), (43, 2, 3, 3), (47, 2, 17, 3), (59, 2, 17, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c61229a1_cert1 : certAll 0 0 1 53 1536 [(61, 11, 2, 3), (67, 2, 3, 3), (71, 2, 11, 3), (73, 11, 2, 3), (79, 2, 3, 3), (83, 2, 17, 3), (89, 3, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c61229a1_gens : allOn 0 0 1 53 1536 [((-8), 24, 1), ((-1), 38, 1), (6, 45, 1)] = true := by decide +kernel

-- 61376c1: 20 primes
set_option maxHeartbeats 0 in
theorem c61376c1_cert0 : certAll 0 1 0 (-145) 399 [(5, 3, 13, 3), (11, 5, 3, 13), (13, 3, 5, 3), (17, 11, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 19, 3), (37, 3, 5, 3), (41, 11, 3, 3), (43, 5, 3, 3), (47, 3, 19, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c61376c1_cert1 : certAll 0 1 0 (-145) 399 [(53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (73, 11, 3, 3), (79, 3, 11, 3), (83, 5, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c61376c1_gens : allOn 0 1 0 (-145) 399 [(11, 16, 1), (17, 56, 1), (10, 7, 1), (3, 0, 1)] = true := by decide +kernel

-- 61504cg1: 21 primes
set_option maxHeartbeats 0 in
theorem c61504cg1_cert0 : certAll 0 0 0 (-124) 496 [(5, 3, 7, 3), (7, 5, 3, 3), (11, 3, 7, 3), (13, 5, 3, 3), (17, 3, 7, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 13, 3), (37, 7, 3, 3), (41, 3, 13, 3), (43, 5, 3, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c61504cg1_cert1 : certAll 0 0 0 (-124) 496 [(59, 3, 5, 3), (61, 5, 3, 3), (67, 7, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c61504cg1_gens : allOn 0 0 0 (-124) 496 [(2, 16, 1), (10, 16, 1), ((-6), 32, 1)] = true := by decide +kernel

-- 61598c1: 20 primes
set_option maxHeartbeats 0 in
theorem c61598c1_cert0 : certAll 1 0 1 35 (-120) [(5, 3, 23, 3), (7, 3, 11, 3), (11, 7, 3, 7), (13, 3, 7, 3), (17, 5, 3, 3), (23, 3, 5, 3), (29, 3, 43, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3), (47, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c61598c1_cert1 : certAll 1 0 1 35 (-120) [(53, 3, 5, 3), (61, 3, 7, 3), (67, 11, 3, 3), (73, 5, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c61598c1_gens : allOn 1 0 1 35 (-120) [(4, 7, 1), (23, 102, 1), (7, 18, 1)] = true := by decide +kernel

-- 61651a1: 22 primes
set_option maxHeartbeats 0 in
theorem c61651a1_cert0 : certAll 1 0 0 (-12) 19 [(5, 2, 7, 2), (7, 3, 17, 3), (13, 2, 31, 2), (17, 2, 3, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 5, 2), (37, 3, 2, 2), (41, 2, 3, 2), (43, 5, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c61651a1_cert1 : certAll 1 0 0 (-12) 19 [(53, 3, 2, 2), (59, 2, 3, 2), (61, 2, 13, 2), (67, 7, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (83, 2, 3, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c61651a1_gens : allOn 1 0 0 (-12) 19 [(2, 1, 1), (3, 2, 1), ((-1), 6, 1)] = true := by decide +kernel

-- 61672b1: 22 primes
set_option maxHeartbeats 0 in
theorem c61672b1_cert0 : certAll 0 1 0 (-92) 304 [(5, 3, 7, 3), (7, 3, 19, 3), (11, 23, 3, 7), (17, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 11, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3), (47, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c61672b1_cert1 : certAll 0 1 0 (-92) 304 [(53, 3, 5, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 7, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 11, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c61672b1_gens : allOn 0 1 0 (-92) 304 [(6, 2, 1), (4, 4, 1), (8, 12, 1)] = true := by decide +kernel

-- 61805c1: 20 primes
set_option maxHeartbeats 0 in
theorem c61805c1_cert0 : certAll 1 0 0 (-71) 226 [(7, 3, 13, 3), (11, 7, 2, 2), (13, 2, 7, 2), (17, 2, 3, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 7, 2), (37, 3, 2, 2), (41, 2, 3, 2), (43, 19, 2, 2), (53, 3, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c61805c1_cert1 : certAll 1 0 0 (-71) 226 [(59, 2, 3, 2), (61, 2, 7, 2), (67, 19, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c61805c1_gens : allOn 1 0 0 (-71) 226 [(6, 2, 1), (1, 12, 1), (3, 5, 1)] = true := by decide +kernel

-- 61826a1: 22 primes
set_option maxHeartbeats 0 in
theorem c61826a1_cert0 : certAll 1 1 0 (-161) 709 [(5, 11, 3, 17), (7, 3, 29, 3), (11, 5, 7, 5), (13, 3, 5, 3), (17, 3, 5, 3), (23, 5, 3, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 7, 3, 3), (41, 3, 5, 3), (43, 3, 11, 3), (47, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c61826a1_cert1 : certAll 1 1 0 (-161) 709 [(53, 17, 3, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 7, 3), (83, 3, 7, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c61826a1_gens : allOn 1 1 0 (-161) 709 [(9, 5, 1), ((-10), 43, 1), (14, 31, 1)] = true := by decide +kernel

-- 61839b1: 22 primes
set_option maxHeartbeats 0 in
theorem c61839b1_cert0 : certAll 1 (-1) 1 (-17) 20 [(5, 2, 13, 2), (7, 5, 11, 5), (11, 5, 2, 2), (13, 2, 5, 2), (17, 2, 5, 2), (19, 2, 7, 2), (23, 5, 2, 2), (29, 7, 2, 2), (31, 2, 7, 2), (37, 17, 2, 2), (41, 2, 5, 2), (43, 5, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c61839b1_cert1 : certAll 1 (-1) 1 (-17) 20 [(47, 2, 11, 2), (53, 7, 2, 2), (59, 2, 11, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 5, 2, 2), (73, 2, 5, 2), (79, 5, 2, 2), (83, 2, 17, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c61839b1_gens : allOn 1 (-1) 1 (-17) 20 [(0, 4, 1), ((-3), 7, 1), (1, 1, 1)] = true := by decide +kernel

-- 61886d1: 20 primes
set_option maxHeartbeats 0 in
theorem c61886d1_cert0 : certAll 1 1 0 (-1591) 27029 [(5, 47, 3, 47), (7, 3, 19, 3), (13, 3, 5, 3), (17, 3, 5, 3), (19, 3, 43, 3), (23, 5, 3, 3), (31, 5, 3, 3), (37, 7, 3, 3), (41, 3, 5, 3), (43, 3, 7, 3), (47, 5, 3, 3), (53, 7, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c61886d1_cert1 : certAll 1 1 0 (-1591) 27029 [(59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 43, 3), (83, 3, 7, 3), (89, 7, 3, 3)] = true := by decide +kernel
theorem c61886d1_gens : allOn 1 1 0 (-1591) 27029 [(46, 209, 1), ((-41), 180, 1), ((-3530), 29837, 125)] = true := by decide +kernel

-- 61995a1: 21 primes
set_option maxHeartbeats 0 in
theorem c61995a1_cert0 : certAll 0 (-1) 1 (-26) 32 [(7, 2, 13, 13), (11, 2, 7, 7), (13, 7, 2, 7), (17, 7, 2, 7), (19, 2, 11, 11), (23, 2, 19, 7), (29, 11, 2, 7), (31, 2, 7, 7), (37, 7, 2, 7), (41, 7, 2, 7), (43, 2, 11, 7), (47, 2, 19, 7)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c61995a1_cert1 : certAll 0 (-1) 1 (-26) 32 [(53, 11, 2, 7), (59, 2, 7, 7), (61, 7, 2, 7), (67, 2, 11, 7), (71, 2, 29, 7), (73, 19, 2, 7), (79, 2, 7, 7), (89, 7, 2, 7), (97, 19, 2, 7)] = true := by decide +kernel
theorem c61995a1_gens : allOn 0 (-1) 1 (-26) 32 [((-4), 7, 1), (1, 2, 1), (6, 7, 1)] = true := by decide +kernel

-- 62078c1: 23 primes
set_option maxHeartbeats 0 in
theorem c62078c1_cert0 : certAll 1 (-1) 1 (-69) 189 [(5, 3, 13, 3), (7, 5, 3, 3), (11, 3, 17, 3), (13, 5, 3, 3), (17, 3, 11, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 13, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 11, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c62078c1_cert1 : certAll 1 (-1) 1 (-69) 189 [(47, 3, 5, 3), (53, 3, 5, 3), (59, 3, 5, 3), (61, 5, 3, 3), (67, 13, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 5, 3, 3), (83, 3, 11, 3), (89, 3, 5, 3), (97, 19, 3, 3)] = true := by decide +kernel
theorem c62078c1_gens : allOn 1 (-1) 1 (-69) 189 [(7, 0, 1), ((-1), 16, 1), (3, 0, 1)] = true := by decide +kernel

-- 62168c1: 20 primes
set_option maxHeartbeats 0 in
theorem c62168c1_cert0 : certAll 0 1 0 (-172) 816 [(5, 3, 13, 3), (7, 3, 41, 3), (13, 3, 7, 3), (17, 5, 3, 3), (23, 3, 5, 3), (29, 3, 13, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3), (53, 3, 5, 3), (59, 7, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c62168c1_cert1 : certAll 0 1 0 (-172) 816 [(61, 3, 7, 3), (67, 13, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 41, 3, 3)] = true := by decide +kernel
theorem c62168c1_gens : allOn 0 1 0 (-172) 816 [(6, 6, 1), (8, 4, 1), (2, 22, 1)] = true := by decide +kernel

-- 62246b1: 23 primes
set_option maxHeartbeats 0 in
theorem c62246b1_cert0 : certAll 1 0 0 (-372) 2704 [(5, 3, 13, 3), (7, 3, 19, 3), (11, 7, 3, 13), (13, 3, 7, 3), (17, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 11, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c62246b1_cert1 : certAll 1 0 0 (-372) 2704 [(47, 3, 5, 3), (53, 3, 5, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 13, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c62246b1_gens : allOn 1 0 0 (-372) 2704 [(8, 12, 1), (12, (-4), 1), (24, 76, 1)] = true := by decide +kernel

-- 62282a1: 21 primes
set_option maxHeartbeats 0 in
theorem c62282a1_cert0 : certAll 1 0 1 (-30) (-28) [(5, 3, 43, 3), (7, 3, 23, 3), (13, 3, 7, 3), (17, 5, 3, 3), (23, 3, 5, 3), (29, 3, 17, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3), (47, 3, 5, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c62282a1_cert1 : certAll 1 0 1 (-30) (-28) [(59, 7, 3, 3), (61, 3, 7, 3), (67, 23, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c62282a1_gens : allOn 1 0 1 (-30) (-28) [((-4), 7, 1), (7, 7, 1), ((-5), 3, 1)] = true := by decide +kernel

-- 62319c1: 21 primes
set_option maxHeartbeats 0 in
theorem c62319c1_cert0 : certAll 1 0 0 (-187) (-166) [(5, 2, 23, 2), (7, 5, 11, 5), (11, 7, 2, 2), (13, 2, 7, 2), (17, 2, 11, 2), (19, 2, 7, 2), (23, 7, 2, 2), (29, 5, 2, 2), (31, 2, 5, 2), (37, 11, 2, 2), (41, 2, 13, 2), (43, 5, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c62319c1_cert1 : certAll 1 0 0 (-187) (-166) [(53, 7, 2, 2), (59, 2, 5, 2), (67, 11, 2, 2), (71, 7, 2, 2), (73, 2, 7, 2), (79, 5, 2, 2), (83, 2, 11, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c62319c1_gens : allOn 1 0 0 (-187) (-166) [((-10), 32, 1), (17, 32, 1), ((-26), 175, 8)] = true := by decide +kernel

-- 62546a1: 20 primes
set_option maxHeartbeats 0 in
theorem c62546a1_cert0 : certAll 1 1 0 (-71) 229 [(5, 7, 3, 7), (7, 3, 13, 3), (13, 3, 5, 3), (17, 3, 5, 3), (19, 3, 7, 3), (23, 5, 3, 3), (29, 3, 5, 3), (37, 17, 3, 3), (41, 3, 5, 3), (43, 3, 7, 3), (47, 5, 3, 3), (53, 7, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c62546a1_cert1 : certAll 1 1 0 (-71) 229 [(59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 7, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c62546a1_gens : allOn 1 1 0 (-71) 229 [((-6), 25, 1), (5, 3, 1), ((-10), 13, 1)] = true := by decide +kernel

-- 62576b1: 22 primes
set_option maxHeartbeats 0 in
theorem c62576b1_cert0 : certAll 0 (-1) 0 (-104) (-272) [(5, 7, 3, 7), (7, 3, 13, 3), (11, 5, 17, 5), (13, 3, 5, 3), (17, 3, 5, 3), (19, 3, 7, 3), (23, 5, 3, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 11, 3, 3), (41, 3, 5, 3), (47, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c62576b1_cert1 : certAll 0 (-1) 0 (-104) (-272) [(53, 7, 3, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 7, 3), (83, 3, 11, 3), (89, 7, 3, 3), (97, 23, 3, 3)] = true := by decide +kernel
theorem c62576b1_gens : allOn 0 (-1) 0 (-104) (-272) [((-4), 8, 1), (12, 8, 1), ((-3), 2, 1)] = true := by decide +kernel

-- 62592c1: 22 primes
set_option maxHeartbeats 0 in
theorem c62592c1_cert0 : certAll 0 (-1) 0 (-57) 9 [(5, 11, 7, 23), (7, 5, 13, 5), (11, 13, 7, 7), (13, 5, 17, 5), (17, 5, 7, 5), (19, 5, 11, 5), (23, 11, 5, 5), (29, 5, 17, 7), (31, 7, 5, 5), (37, 7, 5, 5), (41, 5, 11, 5), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c62592c1_cert1 : certAll 0 (-1) 0 (-57) 9 [(47, 11, 5, 5), (53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (67, 7, 5, 5), (73, 5, 7, 5), (79, 5, 13, 5), (83, 5, 7, 5), (89, 7, 5, 5), (97, 7, 5, 5)] = true := by decide +kernel
theorem c62592c1_gens : allOn 0 (-1) 0 (-57) 9 [((-3), 12, 1), (9, 12, 1), ((-7), 4, 1)] = true := by decide +kernel

-- 62823b1: 19 primes
set_option maxHeartbeats 0 in
theorem c62823b1_cert0 : certAll 0 (-1) 1 (-22) 42 [(5, 11, 2, 17), (7, 2, 17, 5), (11, 2, 7, 7), (13, 5, 2, 5), (17, 5, 2, 5), (23, 2, 5, 5), (29, 5, 2, 7), (31, 2, 5, 5), (37, 7, 2, 5), (41, 5, 2, 5), (47, 2, 5, 5), (53, 7, 2, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c62823b1_cert1 : certAll 0 (-1) 1 (-22) 42 [(59, 2, 5, 5), (61, 5, 2, 5), (67, 2, 5, 5), (73, 5, 2, 5), (79, 2, 11, 5), (83, 2, 7, 5), (97, 7, 2, 5)] = true := by decide +kernel
theorem c62823b1_gens : allOn 0 (-1) 1 (-22) 42 [(4, 1, 1), (1, 4, 1), (2, 1, 1)] = true := by decide +kernel

-- 63002h1: 19 primes
set_option maxHeartbeats 0 in
theorem c63002h1_cert0 : certAll 1 (-1) 0 (-394) 3124 [(5, 3, 13, 3), (7, 5, 3, 3), (11, 3, 37, 3), (13, 31, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (31, 5, 3, 3), (37, 23, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3), (47, 3, 11, 3), (59, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c63002h1_cert1 : certAll 1 (-1) 0 (-394) 3124 [(61, 11, 3, 3), (71, 3, 23, 3), (73, 11, 3, 3), (79, 5, 3, 3), (83, 3, 23, 3), (89, 3, 5, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c63002h1_gens : allOn 1 (-1) 0 (-394) 3124 [((-4), 70, 1), (13, 2, 1), (300, (-14), 27)] = true := by decide +kernel

-- 63213b1: 21 primes
set_option maxHeartbeats 0 in
theorem c63213b1_cert0 : certAll 0 1 1 (-90) 20 [(5, 7, 2, 7), (7, 2, 23, 5), (11, 2, 17, 7), (13, 11, 2, 5), (17, 7, 2, 5), (23, 2, 29, 5), (29, 7, 2, 5), (31, 2, 7, 5), (37, 11, 2, 5), (41, 7, 2, 7), (43, 2, 7, 5), (47, 2, 29, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c63213b1_cert1 : certAll 0 1 1 (-90) 20 [(53, 7, 2, 5), (59, 2, 11, 5), (61, 11, 2, 5), (67, 2, 7, 5), (71, 2, 31, 5), (73, 23, 2, 5), (79, 2, 7, 5), (89, 7, 2, 5), (97, 23, 2, 5)] = true := by decide +kernel
theorem c63213b1_gens : allOn 0 1 1 (-90) 20 [(0, 4, 1), ((-9), 13, 1), (18, 67, 1)] = true := by decide +kernel

-- 63298c1: 19 primes
set_option maxHeartbeats 0 in
theorem c63298c1_cert0 : certAll 1 (-1) 1 (-129) 657 [(5, 3, 13, 3), (7, 5, 3, 3), (11, 3, 17, 3), (13, 5, 3, 3), (17, 3, 13, 3), (19, 5, 3, 3), (23, 3, 5, 3), (31, 11, 3, 3), (37, 17, 3, 3), (41, 3, 13, 3), (43, 5, 3, 3), (47, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c63298c1_cert1 : certAll 1 (-1) 1 (-129) 657 [(53, 3, 5, 3), (59, 3, 5, 3), (61, 5, 3, 3), (67, 13, 3, 3), (73, 5, 3, 3), (79, 5, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c63298c1_gens : allOn 1 (-1) 1 (-129) 657 [(7, 4, 1), ((-1), 28, 1), ((-9), 36, 1)] = true := by decide +kernel

-- 63422h1: 21 primes
set_option maxHeartbeats 0 in
theorem c63422h1_cert0 : certAll 1 (-1) 1 (-279) 1839 [(5, 3, 17, 3), (7, 5, 3, 3), (11, 3, 23, 3), (13, 5, 3, 3), (17, 3, 11, 3), (23, 3, 5, 3), (29, 3, 17, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 17, 3), (43, 5, 3, 3), (47, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c63422h1_cert1 : certAll 1 (-1) 1 (-279) 1839 [(53, 3, 5, 3), (59, 3, 5, 3), (61, 5, 3, 3), (67, 11, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (83, 3, 11, 3), (89, 3, 5, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c63422h1_gens : allOn 1 (-1) 1 (-279) 1839 [(11, (-2), 1), (3, 30, 1), (19, 46, 1)] = true := by decide +kernel

-- 63437a1: 20 primes
set_option maxHeartbeats 0 in
theorem c63437a1_cert0 : certAll 1 (-1) 1 (-93) 30 [(5, 2, 7, 2), (7, 17, 3, 3), (13, 2, 3, 2), (17, 2, 5, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 5, 2, 2), (41, 2, 17, 2), (43, 17, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c63437a1_cert1 : certAll 1 (-1) 1 (-93) 30 [(53, 3, 2, 2), (59, 2, 19, 2), (61, 2, 3, 2), (67, 5, 2, 2), (71, 3, 2, 2), (83, 2, 5, 2), (89, 2, 17, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c63437a1_gens : allOn 1 (-1) 1 (-93) 30 [(14, 29, 1), ((-1), 11, 1), (87, 759, 1)] = true := by decide +kernel

-- 63447a1: 22 primes
set_option maxHeartbeats 0 in
theorem c63447a1_cert0 : certAll 1 1 1 (-2) 20 [(5, 2, 13, 2), (7, 5, 29, 5), (13, 2, 7, 2), (17, 2, 13, 2), (19, 2, 7, 2), (23, 7, 2, 2), (29, 5, 2, 2), (31, 2, 5, 2), (37, 17, 2, 2), (41, 2, 13, 2), (43, 5, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c63447a1_cert1 : certAll 1 1 1 (-2) 20 [(53, 7, 2, 2), (59, 2, 5, 2), (61, 2, 7, 2), (67, 13, 2, 2), (71, 7, 2, 2), (73, 2, 7, 2), (79, 5, 2, 2), (83, 2, 17, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c63447a1_gens : allOn 1 1 1 (-2) 20 [(0, 4, 1), ((-3), 4, 1), ((-2), 5, 1)] = true := by decide +kernel

-- 63472g1: 21 primes
set_option maxHeartbeats 0 in
theorem c63472g1_cert0 : certAll 0 1 0 56 372 [(5, 3, 7, 3), (7, 3, 11, 3), (11, 5, 3, 5), (13, 3, 5, 3), (17, 19, 3, 3), (19, 5, 3, 3), (23, 3, 7, 3), (29, 3, 5, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c63472g1_cert1 : certAll 0 1 0 56 372 [(53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 23, 3), (73, 23, 3, 3), (79, 3, 19, 3), (83, 5, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c63472g1_gens : allOn 0 1 0 56 372 [((-2), 16, 1), (14, 64, 1), (4, 26, 1)] = true := by decide +kernel

-- 63574d1: 20 primes
set_option maxHeartbeats 0 in
theorem c63574d1_cert0 : certAll 1 (-1) 0 (-91) 361 [(5, 3, 23, 3), (11, 3, 17, 3), (13, 5, 3, 3), (17, 3, 11, 3), (23, 3, 5, 3), (29, 3, 37, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 11, 3), (43, 5, 3, 3), (47, 3, 5, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c63574d1_cert1 : certAll 1 (-1) 0 (-91) 361 [(59, 3, 5, 3), (61, 5, 3, 3), (67, 23, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (83, 3, 11, 3), (89, 3, 5, 3), (97, 23, 3, 3)] = true := by decide +kernel
theorem c63574d1_gens : allOn 1 (-1) 0 (-91) 361 [(4, 5, 1), (6, (-5), 1), ((-10), 19, 1)] = true := by decide +kernel

-- 63789c1: 22 primes
set_option maxHeartbeats 0 in
theorem c63789c1_cert0 : certAll 1 1 1 (-1934) 40592 [(5, 2, 17, 2), (7, 5, 13, 5), (13, 2, 5, 2), (17, 2, 5, 2), (19, 2, 7, 2), (23, 5, 2, 2), (29, 7, 2, 2), (31, 2, 7, 2), (37, 41, 2, 2), (41, 2, 5, 2), (43, 5, 2, 2), (47, 2, 53, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c63789c1_cert1 : certAll 1 1 1 (-1934) 40592 [(53, 7, 2, 2), (59, 2, 31, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 5, 2, 2), (73, 2, 5, 2), (79, 5, 2, 2), (83, 2, 31, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c63789c1_gens : allOn 1 1 1 (-1934) 40592 [(4, 179, 1), (48, 223, 1), (246, 3688, 1)] = true := by decide +kernel

-- 63936o1: 22 primes
set_option maxHeartbeats 0 in
theorem c63936o1_cert0 : certAll 0 0 0 (-84) 416 [(5, 11, 13, 47), (7, 5, 19, 5), (11, 7, 17, 13), (13, 5, 7, 5), (17, 5, 11, 5), (19, 5, 7, 5), (23, 7, 5, 5), (29, 5, 13, 7), (31, 11, 5, 5), (41, 5, 11, 5), (43, 5, 7, 5), (47, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c63936o1_cert1 : certAll 0 0 0 (-84) 416 [(53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (67, 13, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 17, 5, 5)] = true := by decide +kernel
theorem c63936o1_gens : allOn 0 0 0 (-84) 416 [((-2), 24, 1), (10, 24, 1), (4, 12, 1)] = true := by decide +kernel

-- 64018h1: 23 primes
set_option maxHeartbeats 0 in
theorem c64018h1_cert0 : certAll 1 0 0 (-362) 1444 [(5, 3, 17, 3), (7, 3, 13, 3), (11, 7, 3, 7), (13, 3, 7, 3), (17, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 23, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c64018h1_cert1 : certAll 1 0 0 (-362) 1444 [(47, 3, 5, 3), (53, 3, 5, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 17, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c64018h1_gens : allOn 1 0 0 (-362) 1444 [((-12), 70, 1), (4, 6, 1), (52, 326, 1)] = true := by decide +kernel

-- 64432d1: 23 primes
set_option maxHeartbeats 0 in
theorem c64432d1_cert0 : certAll 0 1 0 (-24) 100 [(5, 3, 17, 3), (7, 3, 13, 3), (11, 5, 3, 5), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 17, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c64432d1_cert1 : certAll 0 1 0 (-24) 100 [(47, 3, 17, 3), (53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 41, 3), (73, 43, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c64432d1_gens : allOn 0 1 0 (-24) 100 [(2, 8, 1), ((-2), 12, 1), ((-6), 8, 1)] = true := by decide +kernel

-- 64522c1: 21 primes
set_option maxHeartbeats 0 in
theorem c64522c1_cert0 : certAll 1 0 0 55 1561 [(5, 3, 73, 3), (7, 3, 11, 3), (11, 5, 3, 7), (13, 3, 5, 3), (17, 7, 3, 3), (23, 3, 11, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 11, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c64522c1_cert1 : certAll 1 0 0 55 1561 [(59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 17, 3), (73, 17, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c64522c1_gens : allOn 1 0 0 55 1561 [((-6), 35, 1), (10, 51, 1), (58, 419, 1)] = true := by decide +kernel

-- 64672h1: 21 primes
set_option maxHeartbeats 0 in
theorem c64672h1_cert0 : certAll 0 1 0 (-102) 364 [(5, 3, 7, 3), (7, 3, 17, 3), (11, 13, 3, 7), (13, 3, 53, 3), (17, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 7, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c64672h1_cert1 : certAll 0 1 0 (-102) 364 [(59, 13, 3, 3), (61, 3, 13, 3), (67, 7, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c64672h1_gens : allOn 0 1 0 (-102) 364 [(6, 2, 1), (5, 2, 1), (9, 16, 1)] = true := by decide +kernel

-- 64763a1: 20 primes
set_option maxHeartbeats 0 in
theorem c64763a1_cert0 : certAll 0 0 1 (-1) 12 [(5, 3, 2, 3), (11, 2, 13, 3), (13, 17, 2, 3), (17, 3, 2, 3), (19, 2, 3, 3), (23, 2, 13, 3), (29, 3, 2, 3), (37, 11, 2, 3), (41, 3, 2, 3), (43, 2, 3, 3), (47, 2, 11, 3), (53, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c64763a1_cert1 : certAll 0 0 1 (-1) 12 [(59, 2, 17, 3), (61, 11, 2, 3), (67, 2, 3, 3), (71, 2, 11, 3), (73, 13, 2, 3), (79, 2, 3, 3), (89, 3, 2, 3), (97, 13, 2, 3)] = true := by decide +kernel
theorem c64763a1_gens : allOn 0 0 1 (-1) 12 [(0, 3, 1), (1, 3, 1), ((-2), 2, 1)] = true := by decide +kernel

-- 64776a1: 22 primes
set_option maxHeartbeats 0 in
theorem c64776a1_cert0 : certAll 0 (-1) 0 (-97) 421 [(5, 7, 17, 7), (7, 5, 13, 5), (11, 7, 17, 7), (13, 5, 7, 5), (17, 5, 11, 5), (19, 5, 7, 5), (23, 7, 5, 5), (29, 5, 31, 7), (31, 11, 5, 5), (37, 11, 5, 5), (41, 5, 11, 5), (47, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c64776a1_cert1 : certAll 0 (-1) 0 (-97) 421 [(53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (67, 17, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 17, 5, 5)] = true := by decide +kernel
theorem c64776a1_gens : allOn 0 (-1) 0 (-97) 421 [(7, 6, 1), (1, 18, 1), (5, 6, 1)] = true := by decide +kernel

-- 65122e1: 23 primes
set_option maxHeartbeats 0 in
theorem c65122e1_cert0 : certAll 1 (-1) 1 (-339) 2547 [(5, 3, 23, 3), (7, 5, 3, 3), (11, 3, 17, 3), (13, 5, 3, 3), (17, 3, 11, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 19, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 11, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c65122e1_cert1 : certAll 1 (-1) 1 (-339) 2547 [(47, 3, 5, 3), (53, 3, 5, 3), (59, 3, 5, 3), (61, 5, 3, 3), (67, 23, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 5, 3, 3), (83, 3, 11, 3), (89, 3, 5, 3), (97, 19, 3, 3)] = true := by decide +kernel
theorem c65122e1_gens : allOn 1 (-1) 1 (-339) 2547 [(11, 2, 1), ((-5), 66, 1), (27, 98, 1)] = true := by decide +kernel

-- 65283c1: 21 primes
set_option maxHeartbeats 0 in
theorem c65283c1_cert0 : certAll 1 0 0 (-370) 2711 [(5, 2, 7, 2), (7, 5, 13, 5), (11, 5, 2, 2), (13, 2, 5, 2), (17, 2, 5, 2), (19, 2, 11, 2), (23, 5, 2, 2), (29, 11, 2, 2), (31, 2, 7, 2), (37, 7, 2, 2), (41, 2, 5, 2), (43, 5, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c65283c1_cert1 : certAll 1 0 0 (-370) 2711 [(53, 11, 2, 2), (59, 2, 7, 2), (61, 2, 5, 2), (71, 5, 2, 2), (73, 2, 5, 2), (79, 5, 2, 2), (83, 2, 7, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c65283c1_gens : allOn 1 0 0 (-370) 2711 [(11, (-4), 1), (14, 11, 1), (94, (-11), 8)] = true := by decide +kernel

-- 65424a1: 21 primes
set_option maxHeartbeats 0 in
theorem c65424a1_cert0 : certAll 0 (-1) 0 (-120) 576 [(5, 17, 7, 17), (7, 5, 11, 5), (11, 5, 7, 7), (13, 7, 5, 5), (17, 19, 5, 5), (19, 5, 17, 5), (23, 5, 7, 5), (31, 5, 17, 5), (37, 7, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5), (53, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c65424a1_cert1 : certAll 0 (-1) 0 (-120) 576 [(59, 5, 17, 5), (61, 37, 5, 5), (67, 5, 17, 5), (71, 5, 17, 5), (73, 17, 5, 5), (79, 5, 19, 5), (83, 5, 7, 5), (89, 7, 5, 5), (97, 7, 5, 5)] = true := by decide +kernel
theorem c65424a1_gens : allOn 0 (-1) 0 (-120) 576 [(6, 6, 1), (0, 24, 1), (8, 8, 1)] = true := by decide +kernel

-- 65428d1: 20 primes
set_option maxHeartbeats 0 in
theorem c65428d1_cert0 : certAll 0 0 0 (-16) 1 [(5, 3, 37, 3), (7, 5, 3, 3), (13, 23, 3, 3), (19, 5, 3, 3), (23, 3, 29, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 29, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3), (47, 3, 29, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c65428d1_cert1 : certAll 0 0 0 (-16) 1 [(59, 3, 41, 3), (61, 23, 3, 3), (67, 5, 3, 3), (73, 23, 3, 3), (79, 5, 3, 3), (83, 3, 29, 3), (89, 3, 5, 3), (97, 23, 3, 3)] = true := by decide +kernel
theorem c65428d1_gens : allOn 0 0 0 (-16) 1 [(0, 1, 1), ((-2), 5, 1), (4, 1, 1)] = true := by decide +kernel

-- 65481c1: 19 primes
set_option maxHeartbeats 0 in
theorem c65481c1_cert0 : certAll 1 1 1 (-234) 1230 [(5, 2, 43, 2), (7, 5, 31, 5), (11, 5, 2, 2), (17, 2, 5, 2), (19, 2, 7, 2), (29, 7, 2, 2), (31, 2, 7, 2), (37, 11, 2, 2), (41, 2, 5, 2), (43, 5, 2, 2), (53, 7, 2, 2), (59, 2, 11, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c65481c1_cert1 : certAll 1 1 1 (-234) 1230 [(61, 2, 5, 2), (67, 5, 2, 2), (71, 5, 2, 2), (79, 5, 2, 2), (83, 2, 11, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c65481c1_gens : allOn 1 1 1 (-234) 1230 [(4, 17, 1), (10, (-1), 1), (110, 175, 8), (7, (-4), 1)] = true := by decide +kernel

-- 65509a1: 23 primes
set_option maxHeartbeats 0 in
theorem c65509a1_cert0 : certAll 0 (-1) 1 (-347) 2607 [(5, 7, 3, 7), (7, 3, 13, 3), (11, 7, 17, 7), (13, 3, 7, 3), (17, 3, 11, 3), (19, 3, 7, 3), (23, 7, 3, 3), (29, 3, 37, 3), (31, 17, 3, 3), (37, 11, 3, 3), (41, 3, 11, 3), (43, 3, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c65509a1_cert1 : certAll 0 (-1) 1 (-347) 2607 [(47, 7, 3, 3), (53, 7, 3, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 17, 3, 3), (71, 7, 3, 3), (73, 3, 7, 3), (79, 3, 7, 3), (83, 3, 11, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c65509a1_gens : allOn 0 (-1) 1 (-347) 2607 [(11, 0, 1), (9, 11, 1), (708, (-33), 64)] = true := by decide +kernel

-- 65515a1: 18 primes
set_option maxHeartbeats 0 in
theorem c65515a1_cert0 : certAll 1 0 0 (-220) 1275 [(7, 3, 11, 3), (11, 7, 2, 2), (13, 2, 7, 2), (17, 2, 3, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 7, 2), (37, 3, 2, 2), (41, 2, 3, 2), (47, 2, 11, 2), (53, 3, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c65515a1_cert1 : certAll 1 0 0 (-220) 1275 [(61, 2, 7, 2), (67, 11, 2, 2), (71, 3, 2, 2), (79, 3, 2, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c65515a1_gens : allOn 1 0 0 (-220) 1275 [(15, 30, 1), (10, 5, 1), ((-10), 55, 1)] = true := by decide +kernel

-- 65563a1: 22 primes
set_option maxHeartbeats 0 in
theorem c65563a1_cert0 : certAll 0 1 1 (-85) 275 [(5, 3, 17, 3), (11, 5, 3, 13), (13, 3, 5, 3), (17, 11, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 13, 3), (37, 3, 5, 3), (41, 11, 3, 3), (43, 5, 3, 3), (47, 3, 23, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c65563a1_cert1 : certAll 0 1 1 (-85) 275 [(53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 3, 11, 3), (83, 5, 3, 3), (89, 11, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c65563a1_gens : allOn 0 1 1 (-85) 275 [(5, 0, 1), (3, 7, 1), (42, 5, 8)] = true := by decide +kernel

-- 65710b1: 22 primes
set_option maxHeartbeats 0 in
theorem c65710b1_cert0 : certAll 1 (-1) 0 (-40) 100 [(7, 17, 3, 3), (11, 3, 7, 3), (13, 7, 3, 3), (17, 3, 11, 3), (19, 7, 3, 3), (23, 3, 11, 3), (29, 3, 7, 3), (31, 11, 3, 3), (37, 7, 3, 3), (41, 3, 17, 3), (43, 7, 3, 3), (47, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c65710b1_cert1 : certAll 1 (-1) 0 (-40) 100 [(53, 3, 7, 3), (59, 3, 7, 3), (61, 7, 3, 3), (67, 7, 3, 3), (71, 3, 29, 3), (73, 17, 3, 3), (79, 11, 3, 3), (83, 3, 7, 3), (89, 3, 37, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c65710b1_gens : allOn 1 (-1) 0 (-40) 100 [(0, 10, 1), (5, 0, 1), (10, 20, 1)] = true := by decide +kernel

-- 66170b1: 21 primes
set_option maxHeartbeats 0 in
theorem c66170b1_cert0 : certAll 1 (-1) 0 (-100) 436 [(7, 11, 3, 3), (11, 3, 29, 3), (17, 3, 11, 3), (19, 29, 3, 3), (23, 3, 19, 3), (29, 3, 17, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 11, 3), (43, 17, 3, 3), (47, 3, 19, 3), (53, 3, 17, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c66170b1_cert1 : certAll 1 (-1) 0 (-100) 436 [(59, 3, 11, 3), (61, 11, 3, 3), (67, 17, 3, 3), (71, 3, 17, 3), (73, 17, 3, 3), (79, 11, 3, 3), (83, 3, 11, 3), (89, 3, 11, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c66170b1_gens : allOn 1 (-1) 0 (-100) 436 [(18, 56, 1), (5, 4, 1), ((-8), 30, 1)] = true := by decide +kernel

-- 66387a1: 20 primes
set_option maxHeartbeats 0 in
theorem c66387a1_cert0 : certAll 1 1 1 (-112) 410 [(5, 2, 7, 2), (7, 5, 11, 5), (11, 17, 2, 2), (13, 2, 17, 2), (17, 2, 11, 2), (19, 2, 23, 2), (23, 7, 2, 2), (29, 5, 2, 2), (31, 2, 5, 2), (37, 7, 2, 2), (43, 5, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c66387a1_cert1 : certAll 1 1 1 (-112) 410 [(53, 11, 2, 2), (59, 2, 5, 2), (61, 2, 11, 2), (67, 7, 2, 2), (71, 7, 2, 2), (79, 5, 2, 2), (83, 2, 7, 2), (89, 2, 5, 2)] = true := by decide +kernel
theorem c66387a1_gens : allOn 1 1 1 (-112) 410 [(5, 0, 1), (6, (-5), 1), (46, (-21), 8)] = true := by decide +kernel

-- 66531a1: 19 primes
set_option maxHeartbeats 0 in
theorem c66531a1_cert0 : certAll 1 1 1 (-604) 5462 [(5, 2, 7, 2), (7, 5, 13, 5), (11, 5, 2, 2), (13, 2, 5, 2), (17, 2, 5, 2), (19, 2, 11, 2), (23, 5, 2, 2), (29, 11, 2, 2), (31, 2, 7, 2), (37, 7, 2, 2), (41, 2, 5, 2), (43, 5, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c66531a1_cert1 : certAll 1 1 1 (-604) 5462 [(53, 11, 2, 2), (59, 2, 7, 2), (61, 2, 5, 2), (73, 2, 5, 2), (79, 5, 2, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c66531a1_gens : allOn 1 1 1 (-604) 5462 [(14, (-9), 1), (20, 33, 1), (5, 48, 1)] = true := by decide +kernel

-- 66848j1: 23 primes
set_option maxHeartbeats 0 in
theorem c66848j1_cert0 : certAll 0 0 0 (-13) 4 [(5, 3, 7, 3), (7, 11, 3, 3), (11, 3, 5, 3), (13, 5, 3, 3), (17, 3, 5, 3), (19, 7, 3, 3), (23, 3, 5, 3), (29, 3, 7, 3), (31, 5, 3, 3), (37, 5, 3, 3), (41, 3, 11, 3), (43, 7, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c66848j1_cert1 : certAll 0 0 0 (-13) 4 [(47, 3, 5, 3), (53, 3, 7, 3), (59, 3, 7, 3), (61, 7, 3, 3), (67, 5, 3, 3), (71, 3, 23, 3), (73, 19, 3, 3), (79, 5, 3, 3), (83, 3, 5, 3), (89, 3, 11, 3), (97, 5, 3, 3)] = true := by decide +kernel
theorem c66848j1_gens : allOn 0 0 0 (-13) 4 [((-1), 4, 1), ((-3), 4, 1), (0, 2, 1)] = true := by decide +kernel

-- 66993d1: 21 primes
set_option maxHeartbeats 0 in
theorem c66993d1_cert0 : certAll 0 1 1 (-202) 1042 [(5, 7, 2, 7), (7, 2, 13, 5), (11, 2, 17, 7), (13, 5, 2, 5), (17, 5, 2, 5), (19, 2, 7, 5), (23, 2, 5, 5), (29, 5, 2, 7), (37, 11, 2, 5), (41, 5, 2, 5), (43, 2, 7, 5), (47, 2, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c66993d1_cert1 : certAll 0 1 1 (-202) 1042 [(53, 7, 2, 5), (59, 2, 5, 5), (61, 5, 2, 5), (67, 2, 5, 5), (71, 2, 5, 5), (73, 5, 2, 5), (83, 2, 11, 5), (89, 7, 2, 5), (97, 29, 2, 5)] = true := by decide +kernel
theorem c66993d1_gens : allOn 0 1 1 (-202) 1042 [(8, 1, 1), (5, 13, 1), (7, 4, 1)] = true := by decide +kernel

-- 67037b1: 21 primes
set_option maxHeartbeats 0 in
theorem c67037b1_cert0 : certAll 1 0 0 (-65) 196 [(5, 2, 7, 2), (7, 3, 13, 3), (11, 5, 2, 2), (13, 2, 5, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 7, 2), (37, 3, 2, 2), (41, 2, 3, 2), (47, 2, 23, 2), (53, 3, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c67037b1_cert1 : certAll 1 0 0 (-65) 196 [(59, 2, 3, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (83, 2, 3, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c67037b1_gens : allOn 1 0 0 (-65) 196 [(5, (-4), 1), (4, 0, 1), (1, 11, 1)] = true := by decide +kernel

-- 67042a1: 22 primes
set_option maxHeartbeats 0 in
theorem c67042a1_cert0 : certAll 1 0 0 6 100 [(5, 3, 13, 3), (7, 3, 29, 3), (11, 5, 3, 5), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (43, 5, 3, 3), (47, 3, 19, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c67042a1_cert1 : certAll 1 0 0 6 100 [(53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c67042a1_gens : allOn 1 0 0 6 100 [((-4), 6, 1), (0, 10, 1), ((-2), 10, 1)] = true := by decide +kernel

-- 67064a1: 21 primes
set_option maxHeartbeats 0 in
theorem c67064a1_cert0 : certAll 0 (-1) 0 (-3004) 64388 [(5, 47, 3, 47), (7, 3, 11, 3), (11, 5, 7, 5), (13, 3, 5, 3), (17, 3, 5, 3), (19, 3, 41, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 7, 3, 3), (41, 3, 5, 3), (43, 3, 7, 3), (47, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c67064a1_cert1 : certAll 0 (-1) 0 (-3004) 64388 [(53, 7, 3, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 29, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c67064a1_gens : allOn 0 (-1) 0 (-3004) 64388 [(8, 202, 1), (32, 2, 1), (28, 38, 1)] = true := by decide +kernel

-- 67119a1: 20 primes
set_option maxHeartbeats 0 in
theorem c67119a1_cert0 : certAll 0 1 1 (-510) 4430 [(5, 7, 2, 7), (7, 2, 17, 5), (11, 2, 17, 7), (17, 7, 2, 5), (19, 2, 7, 5), (23, 2, 19, 5), (29, 7, 2, 5), (31, 2, 7, 5), (37, 11, 2, 5), (41, 7, 2, 7), (43, 2, 7, 5), (47, 2, 17, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c67119a1_cert1 : certAll 0 1 1 (-510) 4430 [(53, 7, 2, 5), (59, 2, 11, 5), (61, 11, 2, 5), (67, 2, 7, 5), (71, 2, 17, 5), (79, 2, 7, 5), (89, 7, 2, 5), (97, 17, 2, 5)] = true := by decide +kernel
theorem c67119a1_gens : allOn 0 1 1 (-510) 4430 [(15, 19, 1), (12, 13, 1), (42, 347, 8)] = true := by decide +kernel

-- 67194e1: 21 primes
set_option maxHeartbeats 0 in
theorem c67194e1_cert0 : certAll 1 (-1) 0 (-81) 81 [(5, 7, 13, 7), (7, 5, 11, 5), (11, 7, 23, 7), (13, 5, 7, 5), (17, 5, 11, 5), (19, 5, 7, 5), (23, 7, 5, 5), (29, 5, 13, 7), (31, 11, 5, 5), (37, 11, 5, 5), (43, 5, 7, 5), (47, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c67194e1_cert1 : certAll 1 (-1) 0 (-81) 81 [(53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c67194e1_gens : allOn 1 (-1) 0 (-81) 81 [(0, 9, 1), ((-6), 21, 1), ((-9), 9, 1)] = true := by decide +kernel

-- 67244a1: 22 primes
set_option maxHeartbeats 0 in
theorem c67244a1_cert0 : certAll 0 (-1) 0 (-669) 6889 [(5, 11, 3, 37), (7, 3, 17, 3), (11, 5, 7, 5), (13, 3, 5, 3), (17, 3, 5, 3), (19, 3, 11, 3), (23, 5, 3, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 7, 3, 3), (41, 3, 5, 3), (43, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c67244a1_cert1 : certAll 0 (-1) 0 (-669) 6889 [(47, 5, 3, 3), (53, 11, 3, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (73, 3, 5, 3), (79, 3, 7, 3), (83, 3, 7, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c67244a1_gens : allOn 0 (-1) 0 (-669) 6889 [(15, 2, 1), (19, 26, 1), ((-9), 110, 1)] = true := by decide +kernel

-- 67302f1: 22 primes
set_option maxHeartbeats 0 in
theorem c67302f1_cert0 : certAll 1 (-1) 0 (-261) 1381 [(5, 19, 13, 23), (7, 5, 11, 5), (11, 7, 17, 13), (13, 5, 7, 5), (17, 5, 13, 5), (19, 5, 7, 5), (23, 7, 5, 5), (29, 5, 13, 7), (31, 11, 5, 5), (37, 17, 5, 5), (41, 5, 11, 5), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c67302f1_cert1 : certAll 1 (-1) 0 (-261) 1381 [(47, 7, 5, 5), (53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (67, 11, 5, 5), (73, 5, 7, 5), (79, 5, 7, 5), (83, 5, 17, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c67302f1_gens : allOn 1 (-1) 0 (-261) 1381 [((-10), 59, 1), (14, 11, 1), (26, 95, 1)] = true := by decide +kernel

-- 67418a1: 22 primes
set_option maxHeartbeats 0 in
theorem c67418a1_cert0 : certAll 1 1 0 (-124) 464 [(5, 7, 3, 7), (7, 3, 11, 3), (11, 7, 17, 7), (17, 3, 11, 3), (19, 3, 7, 3), (23, 7, 3, 3), (29, 3, 23, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 17, 3), (43, 3, 7, 3), (47, 7, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c67418a1_cert1 : certAll 1 1 0 (-124) 464 [(53, 7, 3, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 11, 3, 3), (71, 7, 3, 3), (73, 3, 7, 3), (79, 3, 7, 3), (83, 3, 11, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c67418a1_gens : allOn 1 1 0 (-124) 464 [(8, 4, 1), ((-8), 36, 1), (7, (-3), 1)] = true := by decide +kernel

-- 67484b1: 22 primes
set_option maxHeartbeats 0 in
theorem c67484b1_cert0 : certAll 0 0 0 (-1) 25 [(5, 3, 7, 3), (7, 5, 3, 3), (11, 3, 7, 3), (13, 7, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 7, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c67484b1_cert1 : certAll 0 0 0 (-1) 25 [(47, 3, 11, 3), (53, 3, 5, 3), (59, 3, 7, 3), (67, 5, 3, 3), (71, 3, 23, 3), (73, 19, 3, 3), (79, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c67484b1_gens : allOn 0 0 0 (-1) 25 [(1, 5, 1), ((-1), 5, 1), ((-3), 1, 1)] = true := by decide +kernel

-- 67520z1: 22 primes
set_option maxHeartbeats 0 in
theorem c67520z1_cert0 : certAll 0 0 0 (-532) 5344 [(7, 13, 3, 3), (11, 3, 17, 3), (13, 11, 3, 3), (17, 3, 11, 3), (19, 13, 3, 3), (23, 3, 11, 3), (29, 3, 13, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 13, 3), (43, 13, 3, 3), (47, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c67520z1_cert1 : certAll 0 0 0 (-532) 5344 [(53, 3, 13, 3), (59, 3, 17, 3), (61, 17, 3, 3), (67, 11, 3, 3), (71, 3, 37, 3), (73, 17, 3, 3), (79, 11, 3, 3), (83, 3, 11, 3), (89, 3, 13, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c67520z1_gens : allOn 0 0 0 (-532) 5344 [(18, 40, 1), (38, 200, 1), ((-12), 100, 1)] = true := by decide +kernel

-- 67926b1: 22 primes
set_option maxHeartbeats 0 in
theorem c67926b1_cert0 : certAll 1 1 0 (-59) 141 [(5, 11, 7, 23), (7, 5, 17, 5), (11, 13, 7, 7), (13, 5, 19, 5), (17, 5, 7, 5), (19, 5, 11, 5), (23, 11, 5, 5), (29, 5, 13, 7), (37, 7, 5, 5), (41, 5, 11, 5), (43, 5, 7, 5), (47, 11, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c67926b1_cert1 : certAll 1 1 0 (-59) 141 [(53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (67, 7, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 17, 5), (83, 5, 7, 5), (89, 7, 5, 5), (97, 7, 5, 5)] = true := by decide +kernel
theorem c67926b1_gens : allOn 1 1 0 (-59) 141 [(2, 5, 1), (5, (-1), 1), (14, 41, 1)] = true := by decide +kernel

-- 68309a1: 20 primes
set_option maxHeartbeats 0 in
theorem c68309a1_cert0 : certAll 0 0 1 (-11) 6 [(5, 7, 2, 7), (7, 2, 43, 5), (13, 17, 2, 5), (17, 7, 2, 5), (19, 2, 7, 7), (23, 2, 43, 5), (29, 7, 2, 5), (37, 17, 2, 5), (41, 7, 2, 5), (43, 2, 7, 5), (47, 2, 23, 5), (53, 7, 2, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c68309a1_cert1 : certAll 0 0 1 (-11) 6 [(59, 2, 17, 5), (61, 17, 2, 5), (67, 2, 7, 5), (71, 2, 23, 5), (73, 23, 2, 5), (79, 2, 7, 5), (89, 7, 2, 5), (97, 43, 2, 5)] = true := by decide +kernel
theorem c68309a1_gens : allOn 0 0 1 (-11) 6 [(0, 2, 1), (3, 0, 1), ((-3), 3, 1)] = true := by decide +kernel

-- 68499j1: 20 primes
set_option maxHeartbeats 0 in
theorem c68499j1_cert0 : certAll 0 0 1 (-459) 3800 [(5, 7, 2, 7), (7, 2, 19, 5), (11, 2, 31, 7), (13, 5, 2, 5), (19, 2, 7, 5), (23, 2, 5, 5), (29, 5, 2, 7), (31, 2, 5, 5), (37, 29, 2, 5), (41, 5, 2, 5), (47, 2, 5, 5), (53, 7, 2, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c68499j1_cert1 : certAll 0 0 1 (-459) 3800 [(61, 5, 2, 5), (67, 2, 5, 5), (71, 2, 5, 5), (73, 5, 2, 5), (79, 2, 7, 5), (83, 2, 29, 5), (89, 7, 2, 5), (97, 11, 2, 5)] = true := by decide +kernel
theorem c68499j1_gens : allOn 0 0 1 (-459) 3800 [(12, 4, 1), (3, 49, 1), (30, 130, 1)] = true := by decide +kernel

-- 68594b1: 23 primes
set_option maxHeartbeats 0 in
theorem c68594b1_cert0 : certAll 1 0 1 (-13) 72 [(5, 3, 13, 3), (7, 3, 29, 3), (11, 5, 3, 7), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 13, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c68594b1_cert1 : certAll 1 0 1 (-13) 72 [(47, 3, 11, 3), (53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 13, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 13, 3, 3)] = true := by decide +kernel
theorem c68594b1_gens : allOn 1 0 1 (-13) 72 [(3, 6, 1), ((-5), 6, 1), (11, 30, 1)] = true := by decide +kernel

-- 68672c1: 20 primes
set_option maxHeartbeats 0 in
theorem c68672c1_cert0 : certAll 0 0 0 (-988) 12016 [(5, 3, 7, 3), (7, 41, 3, 3), (11, 3, 5, 3), (13, 5, 3, 3), (19, 7, 3, 3), (23, 3, 5, 3), (31, 5, 3, 3), (41, 3, 47, 3), (43, 7, 3, 3), (47, 3, 5, 3), (53, 3, 7, 3), (59, 3, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c68672c1_cert1 : certAll 0 0 0 (-988) 12016 [(61, 7, 3, 3), (67, 5, 3, 3), (71, 3, 23, 3), (73, 23, 3, 3), (79, 5, 3, 3), (83, 3, 5, 3), (89, 3, 41, 3), (97, 5, 3, 3)] = true := by decide +kernel
theorem c68672c1_gens : allOn 0 0 0 (-988) 12016 [(50, 296, 1), (13, 37, 1), ((-24), 148, 1)] = true := by decide +kernel

-- 68751d1: 23 primes
set_option maxHeartbeats 0 in
theorem c68751d1_cert0 : certAll 1 (-1) 1 (-104) (-196) [(5, 2, 13, 2), (7, 5, 11, 5), (11, 7, 2, 2), (13, 2, 7, 2), (17, 2, 11, 2), (19, 2, 7, 2), (23, 7, 2, 2), (29, 5, 2, 2), (31, 2, 5, 2), (37, 11, 2, 2), (41, 2, 13, 2), (43, 5, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c68751d1_cert1 : certAll 1 (-1) 1 (-104) (-196) [(47, 2, 5, 2), (53, 7, 2, 2), (59, 2, 5, 2), (61, 2, 7, 2), (67, 11, 2, 2), (71, 7, 2, 2), (73, 2, 7, 2), (79, 5, 2, 2), (83, 2, 11, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c68751d1_gens : allOn 1 (-1) 1 (-104) (-196) [((-6), 16, 1), ((-3), 10, 1), (21, 70, 1)] = true := by decide +kernel

-- 68773a1: 21 primes
set_option maxHeartbeats 0 in
theorem c68773a1_cert0 : certAll 0 (-1) 1 (-296) 2058 [(5, 7, 2, 7), (7, 2, 5, 3), (11, 2, 5, 7), (13, 3, 2, 3), (17, 3, 2, 3), (19, 2, 7, 3), (23, 2, 3, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 5, 2, 3), (41, 3, 2, 3), (43, 2, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c68773a1_cert1 : certAll 0 (-1) 1 (-296) 2058 [(47, 2, 3, 3), (53, 5, 2, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 3, 3), (73, 3, 2, 3), (79, 2, 7, 3), (83, 2, 5, 3), (89, 5, 2, 3)] = true := by decide +kernel
theorem c68773a1_gens : allOn 0 (-1) 1 (-296) 2058 [((-1), 48, 1), (264, 35, 27), (9, 6, 1)] = true := by decide +kernel

-- 68802d1: 22 primes
set_option maxHeartbeats 0 in
theorem c68802d1_cert0 : certAll 1 0 1 (-173) 812 [(5, 13, 97, 13), (7, 5, 11, 5), (11, 5, 17, 13), (13, 11, 5, 5), (17, 7, 5, 5), (19, 5, 7, 5), (23, 5, 11, 5), (31, 5, 7, 5), (37, 11, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5), (47, 5, 11, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c68802d1_cert1 : certAll 1 0 1 (-173) 812 [(53, 7, 5, 5), (59, 5, 17, 5), (61, 17, 5, 5), (67, 5, 7, 5), (71, 5, 23, 5), (73, 17, 5, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c68802d1_gens : allOn 1 0 1 (-173) 812 [(3, 16, 1), (9, (-2), 1), (12, 16, 1)] = true := by decide +kernel

-- 68811b1: 23 primes
set_option maxHeartbeats 0 in
theorem c68811b1_cert0 : certAll 0 1 1 (-102) 380 [(5, 7, 2, 7), (7, 2, 97, 5), (11, 2, 17, 7), (13, 5, 2, 5), (17, 5, 2, 5), (19, 2, 7, 5), (23, 2, 5, 5), (29, 5, 2, 7), (31, 2, 5, 5), (37, 17, 2, 5), (41, 5, 2, 5), (43, 2, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c68811b1_cert1 : certAll 0 1 1 (-102) 380 [(47, 2, 5, 5), (53, 7, 2, 5), (59, 2, 5, 5), (61, 5, 2, 5), (67, 2, 5, 5), (71, 2, 5, 5), (73, 5, 2, 5), (79, 2, 7, 5), (83, 2, 17, 5), (89, 7, 2, 5), (97, 11, 2, 5)] = true := by decide +kernel
theorem c68811b1_gens : allOn 0 1 1 (-102) 380 [(6, 4, 1), (3, 10, 1), (9, 16, 1)] = true := by decide +kernel

-- 68890d1: 19 primes
set_option maxHeartbeats 0 in
theorem c68890d1_cert0 : certAll 1 0 1 22 156 [(7, 3, 13, 3), (11, 7, 3, 7), (13, 3, 7, 3), (17, 7, 3, 3), (19, 29, 3, 3), (23, 3, 29, 3), (29, 3, 17, 3), (31, 3, 7, 3), (37, 3, 7, 3), (41, 7, 3, 3), (43, 17, 3, 3), (47, 3, 29, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c68890d1_cert1 : certAll 1 0 1 22 156 [(53, 3, 17, 3), (61, 3, 7, 3), (67, 17, 3, 3), (73, 17, 3, 3), (79, 3, 7, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c68890d1_gens : allOn 1 0 1 22 156 [(5, 17, 1), ((-3), 9, 1), (21, 89, 1)] = true := by decide +kernel

-- 69158c1: 22 primes
set_option maxHeartbeats 0 in
theorem c69158c1_cert0 : certAll 1 0 0 (-582) 5476 [(5, 3, 43, 3), (7, 3, 41, 3), (11, 7, 3, 13), (13, 3, 7, 3), (17, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3), (47, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c69158c1_cert1 : certAll 1 0 0 (-582) 5476 [(53, 3, 5, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 41, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c69158c1_gens : allOn 1 0 0 (-582) 5476 [(12, 10, 1), ((-20), 106, 1), (44, 234, 1)] = true := by decide +kernel

-- 69232a1: 22 primes
set_option maxHeartbeats 0 in
theorem c69232a1_cert0 : certAll 0 0 0 29 130 [(5, 3, 7, 3), (7, 5, 3, 3), (11, 3, 7, 3), (13, 7, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 11, 3), (31, 5, 3, 3), (37, 7, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3), (47, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c69232a1_cert1 : certAll 0 0 0 29 130 [(53, 3, 5, 3), (59, 3, 7, 3), (61, 7, 3, 3), (67, 5, 3, 3), (71, 3, 23, 3), (73, 17, 3, 3), (79, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c69232a1_gens : allOn 0 0 0 29 130 [((-3), 4, 1), (5, 20, 1), ((-1), 10, 1)] = true := by decide +kernel

-- 69309c1: 20 primes
set_option maxHeartbeats 0 in
theorem c69309c1_cert0 : certAll 0 0 1 (-57) (-54) [(5, 11, 2, 23), (7, 2, 19, 5), (11, 2, 7, 7), (13, 7, 2, 5), (19, 2, 11, 5), (23, 2, 29, 5), (29, 11, 2, 5), (31, 2, 7, 5), (37, 7, 2, 5), (41, 7, 2, 7), (47, 2, 29, 5), (53, 11, 2, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c69309c1_cert1 : certAll 0 0 1 (-57) (-54) [(59, 2, 7, 5), (61, 7, 2, 5), (67, 2, 11, 5), (71, 2, 31, 5), (73, 23, 2, 5), (79, 2, 7, 5), (89, 7, 2, 5), (97, 23, 2, 5)] = true := by decide +kernel
theorem c69309c1_gens : allOn 0 0 1 (-57) (-54) [(11, 25, 1), ((-6), 8, 1), ((-14), 47, 8)] = true := by decide +kernel

-- 69321a1: 21 primes
set_option maxHeartbeats 0 in
theorem c69321a1_cert0 : certAll 0 (-1) 1 (-182) 992 [(5, 17, 2, 17), (11, 2, 17, 13), (13, 5, 2, 5), (17, 5, 2, 5), (19, 2, 13, 5), (23, 2, 5, 5), (29, 5, 2, 11), (31, 2, 5, 5), (37, 11, 2, 5), (41, 5, 2, 5), (43, 2, 13, 5), (47, 2, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c69321a1_cert1 : certAll 0 (-1) 1 (-182) 992 [(53, 11, 2, 5), (59, 2, 5, 5), (67, 2, 5, 5), (71, 2, 5, 5), (73, 5, 2, 5), (79, 2, 11, 5), (83, 2, 11, 5), (89, 11, 2, 5), (97, 19, 2, 5)] = true := by decide +kernel
theorem c69321a1_gens : allOn 0 (-1) 1 (-182) 992 [(14, 31, 1), (7, 3, 1), (0, 31, 1)] = true := by decide +kernel

-- 69359a1: 21 primes
set_option maxHeartbeats 0 in
theorem c69359a1_cert0 : certAll 0 0 1 (-377) 2816 [(5, 11, 2, 13), (7, 2, 13, 5), (11, 2, 7, 7), (13, 7, 2, 5), (17, 7, 2, 5), (19, 2, 13, 5), (23, 2, 11, 5), (31, 2, 7, 5), (37, 7, 2, 5), (41, 7, 2, 7), (47, 2, 19, 5), (53, 13, 2, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c69359a1_cert1 : certAll 0 0 1 (-377) 2816 [(59, 2, 7, 5), (61, 7, 2, 5), (67, 2, 11, 5), (71, 2, 11, 5), (73, 11, 2, 5), (79, 2, 7, 5), (83, 2, 7, 5), (89, 7, 2, 5), (97, 11, 2, 5)] = true := by decide +kernel
theorem c69359a1_gens : allOn 0 0 1 (-377) 2816 [(21, 64, 1), (82, 39, 8), (12, 4, 1)] = true := by decide +kernel

-- 69402e1: 22 primes
set_option maxHeartbeats 0 in
theorem c69402e1_cert0 : certAll 1 1 0 (-71) 201 [(5, 7, 23, 7), (7, 5, 13, 5), (11, 5, 17, 5), (13, 11, 5, 5), (17, 7, 5, 5), (19, 5, 7, 7), (23, 5, 11, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 17, 5, 5), (41, 7, 5, 5), (47, 5, 19, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c69402e1_cert1 : certAll 1 1 0 (-71) 201 [(53, 7, 5, 5), (59, 5, 17, 5), (61, 11, 5, 5), (67, 5, 7, 5), (71, 5, 11, 5), (73, 11, 5, 5), (79, 5, 7, 5), (83, 5, 17, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c69402e1_gens : allOn 1 1 0 (-71) 201 [(5, (-1), 1), (4, (-3), 1), (8, 11, 1)] = true := by decide +kernel

-- 69477a1: 22 primes
set_option maxHeartbeats 0 in
theorem c69477a1_cert0 : certAll 1 1 1 (-7) 20 [(5, 2, 7, 2), (7, 5, 17, 5), (11, 13, 2, 2), (13, 2, 19, 2), (17, 2, 7, 2), (19, 2, 11, 2), (23, 11, 2, 2), (31, 2, 5, 2), (37, 7, 2, 2), (41, 2, 11, 2), (43, 5, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c69477a1_cert1 : certAll 1 1 1 (-7) 20 [(53, 7, 2, 2), (59, 2, 5, 2), (61, 2, 7, 2), (67, 7, 2, 2), (71, 7, 2, 2), (73, 2, 7, 2), (79, 5, 2, 2), (83, 2, 7, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c69477a1_gens : allOn 1 1 1 (-7) 20 [(2, 3, 1), ((-4), 0, 1), (5, 9, 1)] = true := by decide +kernel

-- 69668b1: 22 primes
set_option maxHeartbeats 0 in
theorem c69668b1_cert0 : certAll 0 1 0 (-30) 49 [(5, 3, 17, 3), (7, 3, 17, 3), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 31, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 23, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c69668b1_cert1 : certAll 0 1 0 (-30) 49 [(53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 17, 3), (73, 17, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c69668b1_gens : allOn 0 1 0 (-30) 49 [(2, 1, 1), (4, 3, 1), (0, 7, 1)] = true := by decide +kernel

-- 69850m1: 20 primes
set_option maxHeartbeats 0 in
theorem c69850m1_cert0 : certAll 1 (-1) 0 (-142) 616 [(7, 17, 3, 3), (13, 23, 3, 3), (17, 3, 41, 3), (19, 17, 3, 3), (23, 3, 17, 3), (31, 41, 3, 3), (37, 17, 3, 3), (41, 3, 17, 3), (43, 23, 3, 3), (47, 3, 17, 3), (53, 3, 17, 3), (59, 3, 17, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c69850m1_cert1 : certAll 1 (-1) 0 (-142) 616 [(61, 17, 3, 3), (67, 43, 3, 3), (71, 3, 23, 3), (73, 17, 3, 3), (79, 23, 3, 3), (83, 3, 17, 3), (89, 3, 23, 3), (97, 43, 3, 3)] = true := by decide +kernel
theorem c69850m1_gens : allOn 1 (-1) 0 (-142) 616 [((-1), 28, 1), (10, 6, 1), (14, 28, 1)] = true := by decide +kernel

-- 69966t1: 20 primes
set_option maxHeartbeats 0 in
theorem c69966t1_cert0 : certAll 1 (-1) 0 (-324) (-896) [(5, 7, 37, 7), (7, 5, 19, 5), (11, 5, 17, 7), (17, 7, 5, 5), (19, 5, 7, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 11, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5), (47, 5, 29, 5), (53, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c69966t1_cert1 : certAll 1 (-1) 0 (-324) (-896) [(59, 5, 11, 5), (61, 11, 5, 5), (67, 5, 7, 5), (71, 5, 43, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 29, 5, 5)] = true := by decide +kernel
theorem c69966t1_gens : allOn 1 (-1) 0 (-324) (-896) [(23, 47, 1), (20, 8, 1), (32, 128, 1), ((-16), 8, 1)] = true := by decide +kernel

-- 70022b1: 22 primes
set_option maxHeartbeats 0 in
theorem c70022b1_cert0 : certAll 1 (-1) 0 (-517) (-2603) [(7, 13, 3, 3), (11, 3, 17, 3), (13, 11, 3, 3), (17, 3, 11, 3), (19, 13, 3, 3), (23, 3, 11, 3), (29, 3, 13, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 13, 3), (43, 13, 3, 3), (47, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c70022b1_cert1 : certAll 1 (-1) 0 (-517) (-2603) [(53, 3, 13, 3), (59, 3, 19, 3), (61, 19, 3, 3), (67, 11, 3, 3), (71, 3, 29, 3), (73, 37, 3, 3), (79, 11, 3, 3), (83, 3, 11, 3), (89, 3, 13, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c70022b1_gens : allOn 1 (-1) 0 (-517) (-2603) [(186, 2419, 1), (29, 64, 1), ((-6), 19, 1)] = true := by decide +kernel

-- 70363a1: 22 primes
set_option maxHeartbeats 0 in
theorem c70363a1_cert0 : certAll 0 0 1 (-1459) 21450 [(5, 3, 2, 3), (7, 2, 3, 3), (11, 2, 7, 3), (13, 5, 2, 3), (19, 2, 3, 3), (23, 2, 5, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 7, 2, 3), (41, 3, 2, 3), (43, 2, 3, 3), (47, 2, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c70363a1_cert1 : certAll 0 0 1 (-1459) 21450 [(53, 3, 2, 3), (59, 2, 5, 3), (61, 5, 2, 3), (67, 2, 3, 3), (71, 2, 5, 3), (73, 5, 2, 3), (79, 2, 3, 3), (83, 2, 7, 3), (89, 3, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c70363a1_gens : allOn 0 0 1 (-1459) 21450 [(21, 8, 1), (1412, (-49), 64), ((-13), 195, 1)] = true := by decide +kernel

-- 70397b1: 20 primes
set_option maxHeartbeats 0 in
theorem c70397b1_cert0 : certAll 0 (-1) 1 (-3418) 78052 [(7, 2, 31, 3), (11, 2, 13, 13), (13, 3, 2, 3), (19, 2, 7, 3), (23, 2, 3, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 11, 2, 3), (43, 2, 7, 3), (47, 2, 3, 3), (53, 7, 2, 3), (59, 2, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c70397b1_cert1 : certAll 0 (-1) 1 (-3418) 78052 [(61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 3, 3), (73, 3, 2, 3), (79, 2, 7, 3), (83, 2, 11, 3), (89, 7, 2, 3), (97, 19, 2, 3)] = true := by decide +kernel
theorem c70397b1_gens : allOn 0 (-1) 1 (-3418) 78052 [(35, 8, 1), (32, 20, 1), (894, 233, 27)] = true := by decide +kernel

-- 70436b1: 22 primes
set_option maxHeartbeats 0 in
theorem c70436b1_cert0 : certAll 0 1 0 (-22) (-39) [(5, 3, 7, 3), (7, 3, 19, 3), (11, 13, 3, 7), (13, 3, 11, 3), (17, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 11, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c70436b1_cert1 : certAll 0 1 0 (-22) (-39) [(47, 3, 5, 3), (53, 3, 5, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 7, 3, 3), (73, 5, 3, 3), (79, 3, 11, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c70436b1_gens : allOn 0 1 0 (-22) (-39) [((-2), 1, 1), ((-4), 1, 1), ((-3), 3, 1)] = true := by decide +kernel

-- 70449a1: 21 primes
set_option maxHeartbeats 0 in
theorem c70449a1_cert0 : certAll 0 (-1) 1 82 1472 [(7, 2, 47, 13), (11, 2, 29, 13), (13, 11, 2, 7), (17, 7, 2, 7), (19, 2, 7, 7), (29, 7, 2, 7), (31, 2, 7, 7), (37, 11, 2, 7), (41, 7, 2, 7), (43, 2, 7, 7), (47, 2, 29, 7), (53, 7, 2, 7)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c70449a1_cert1 : certAll 0 (-1) 1 82 1472 [(59, 2, 11, 7), (61, 11, 2, 7), (67, 2, 7, 7), (71, 2, 29, 7), (73, 31, 2, 7), (79, 2, 7, 7), (83, 2, 11, 7), (89, 7, 2, 7), (97, 31, 2, 7)] = true := by decide +kernel
theorem c70449a1_gens : allOn 0 (-1) 1 82 1472 [(20, 103, 1), (2, 40, 1), (452, 3073, 64)] = true := by decide +kernel

-- 70449b1: 21 primes
set_option maxHeartbeats 0 in
theorem c70449b1_cert0 : certAll 0 (-1) 1 (-40) 132 [(5, 37, 2, 37), (7, 2, 19, 5), (13, 7, 2, 5), (17, 19, 2, 5), (19, 2, 31, 5), (29, 7, 2, 5), (31, 2, 19, 5), (37, 7, 2, 5), (41, 7, 2, 7), (43, 2, 7, 5), (47, 2, 7, 5), (53, 7, 2, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c70449b1_cert1 : certAll 0 (-1) 1 (-40) 132 [(59, 2, 41, 5), (61, 29, 2, 5), (67, 2, 19, 5), (71, 2, 29, 5), (73, 31, 2, 5), (79, 2, 19, 5), (83, 2, 7, 5), (89, 7, 2, 5), (97, 7, 2, 5)] = true := by decide +kernel
theorem c70449b1_gens : allOn 0 (-1) 1 (-40) 132 [(4, 4, 1), ((-5), 13, 1), (13, 40, 1)] = true := by decide +kernel

-- 70535a1: 20 primes
set_option maxHeartbeats 0 in
theorem c70535a1_cert0 : certAll 1 (-1) 1 (-18) 6 [(7, 13, 3, 3), (11, 3, 2, 2), (13, 2, 3, 2), (17, 2, 7, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 7, 2, 2), (41, 2, 13, 2), (43, 13, 2, 2), (47, 2, 7, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c70535a1_cert1 : certAll 1 (-1) 1 (-18) 6 [(53, 3, 2, 2), (61, 2, 3, 2), (67, 7, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 7, 2, 2), (89, 2, 13, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c70535a1_gens : allOn 1 (-1) 1 (-18) 6 [(0, 2, 1), (5, 2, 1), (10, 22, 1)] = true := by decide +kernel

-- 70802b1: 23 primes
set_option maxHeartbeats 0 in
theorem c70802b1_cert0 : certAll 1 1 0 (-21) 25 [(5, 17, 3, 17), (7, 3, 17, 3), (11, 5, 7, 5), (13, 3, 5, 3), (17, 3, 5, 3), (19, 3, 17, 3), (23, 5, 3, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 7, 3, 3), (41, 3, 5, 3), (43, 3, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c70802b1_cert1 : certAll 1 1 0 (-21) 25 [(47, 5, 3, 3), (53, 7, 3, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 11, 3), (83, 3, 7, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c70802b1_gens : allOn 1 1 0 (-21) 25 [(0, 5, 1), (4, 3, 1), (3, (-1), 1)] = true := by decide +kernel

-- 71145a1: 19 primes
set_option maxHeartbeats 0 in
theorem c71145a1_cert0 : certAll 0 0 1 (-2793) 56848 [(7, 2, 29, 13), (11, 2, 13, 13), (13, 11, 2, 7), (19, 2, 7, 7), (23, 2, 13, 7), (29, 7, 2, 7), (37, 11, 2, 7), (41, 7, 2, 7), (43, 2, 7, 7), (53, 7, 2, 7), (59, 2, 11, 7), (61, 11, 2, 7)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c71145a1_cert1 : certAll 0 0 1 (-2793) 56848 [(67, 2, 7, 7), (71, 2, 23, 7), (73, 13, 2, 7), (79, 2, 7, 7), (83, 2, 11, 7), (89, 7, 2, 7), (97, 23, 2, 7)] = true := by decide +kernel
theorem c71145a1_gens : allOn 0 0 1 (-2793) 56848 [(1, 232, 1), (94, 790, 1), (32, 15, 1)] = true := by decide +kernel

-- 71215a1: 21 primes
set_option maxHeartbeats 0 in
theorem c71215a1_cert0 : certAll 1 1 1 10 30 [(7, 3, 23, 3), (11, 13, 2, 2), (13, 2, 19, 2), (17, 2, 7, 2), (19, 2, 17, 2), (23, 13, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 7, 2, 2), (41, 2, 13, 2), (43, 3, 2, 2), (47, 2, 3, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c71215a1_cert1 : certAll 1 1 1 10 30 [(53, 7, 2, 2), (59, 2, 3, 2), (61, 2, 7, 2), (67, 7, 2, 2), (71, 7, 2, 2), (73, 2, 7, 2), (79, 3, 2, 2), (83, 2, 7, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c71215a1_gens : allOn 1 1 1 10 30 [((-2), 3, 1), (3, 8, 1), (10, 30, 1)] = true := by decide +kernel

-- 71234a1: 19 primes
set_option maxHeartbeats 0 in
theorem c71234a1_cert0 : certAll 1 0 1 (-301) 1980 [(7, 3, 11, 3), (11, 7, 3, 7), (13, 3, 7, 3), (17, 7, 3, 3), (19, 13, 3, 3), (23, 3, 11, 3), (29, 3, 17, 3), (31, 3, 7, 3), (37, 3, 7, 3), (41, 7, 3, 3), (43, 17, 3, 3), (47, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c71234a1_cert1 : certAll 1 0 1 (-301) 1980 [(53, 3, 13, 3), (59, 7, 3, 3), (67, 11, 3, 3), (73, 13, 3, 3), (79, 3, 7, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c71234a1_gens : allOn 1 0 1 (-301) 1980 [(10, (-6), 1), (9, 0, 1), (78, (-51), 8)] = true := by decide +kernel

-- 71288i1: 20 primes
set_option maxHeartbeats 0 in
theorem c71288i1_cert0 : certAll 0 0 0 (-2119) 34186 [(5, 3, 53, 3), (11, 3, 17, 3), (13, 5, 3, 3), (17, 3, 11, 3), (23, 3, 5, 3), (29, 3, 17, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 11, 3), (43, 5, 3, 3), (47, 3, 5, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c71288i1_cert1 : certAll 0 0 0 (-2119) 34186 [(59, 3, 5, 3), (61, 5, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 5, 3, 3), (83, 3, 11, 3), (89, 3, 5, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c71288i1_gens : allOn 0 0 0 (-2119) 34186 [((-23), 266, 1), (243, 3724, 1), (33, 14, 1)] = true := by decide +kernel

-- 71374d1: 21 primes
set_option maxHeartbeats 0 in
theorem c71374d1_cert0 : certAll 1 1 0 (-57) 145 [(5, 7, 3, 7), (7, 3, 19, 3), (13, 3, 5, 3), (17, 3, 5, 3), (19, 3, 7, 3), (23, 5, 3, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 23, 3, 3), (43, 3, 7, 3), (47, 5, 3, 3), (53, 7, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c71374d1_cert1 : certAll 1 1 0 (-57) 145 [(59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 7, 3), (83, 3, 17, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c71374d1_gens : allOn 1 1 0 (-57) 145 [(4, (-3), 1), (3, 2, 1), (6, 5, 1)] = true := by decide +kernel

-- 71642b1: 21 primes
set_option maxHeartbeats 0 in
theorem c71642b1_cert0 : certAll 1 (-1) 0 (-58) (-140) [(5, 3, 13, 3), (7, 5, 3, 3), (11, 3, 17, 3), (13, 17, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 11, 3, 3), (41, 3, 5, 3), (47, 3, 11, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c71642b1_cert1 : certAll 1 (-1) 0 (-58) (-140) [(59, 3, 31, 3), (61, 11, 3, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 31, 3, 3), (79, 5, 3, 3), (83, 3, 11, 3), (89, 3, 5, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c71642b1_gens : allOn 1 (-1) 0 (-58) (-140) [((-4), 6, 1), ((-3), 2, 1), ((-5), 5, 1)] = true := by decide +kernel

-- 71688a1: 21 primes
set_option maxHeartbeats 0 in
theorem c71688a1_cert0 : certAll 0 (-1) 0 (-65) 261 [(5, 7, 17, 7), (7, 5, 13, 5), (11, 5, 23, 7), (13, 23, 5, 5), (17, 7, 5, 5), (23, 5, 31, 5), (31, 5, 7, 5), (37, 11, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5), (47, 5, 11, 5), (53, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c71688a1_cert1 : certAll 0 (-1) 0 (-65) 261 [(59, 5, 23, 5), (61, 11, 5, 5), (67, 5, 7, 5), (71, 5, 11, 5), (73, 23, 5, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 23, 5, 5)] = true := by decide +kernel
theorem c71688a1_gens : allOn 0 (-1) 0 (-65) 261 [(5, 6, 1), ((-1), 18, 1), ((-7), 18, 1)] = true := by decide +kernel

-- 72091a1: 20 primes
set_option maxHeartbeats 0 in
theorem c72091a1_cert0 : certAll 0 1 1 (-2) 12 [(5, 3, 2, 3), (7, 2, 37, 3), (11, 2, 3, 7), (13, 3, 2, 3), (19, 2, 3, 3), (29, 3, 2, 3), (31, 2, 5, 3), (37, 3, 2, 3), (41, 5, 2, 3), (43, 2, 3, 3), (47, 2, 5, 3), (53, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c72091a1_cert1 : certAll 0 1 1 (-2) 12 [(59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 5, 3), (73, 5, 2, 3), (79, 2, 7, 3), (83, 2, 3, 3), (89, 7, 2, 3)] = true := by decide +kernel
theorem c72091a1_gens : allOn 0 1 1 (-2) 12 [(0, 3, 1), (1, 3, 1), (2, 4, 1)] = true := by decide +kernel

-- 72098a1: 20 primes
set_option maxHeartbeats 0 in
theorem c72098a1_cert0 : certAll 1 1 0 (-329) 2209 [(5, 11, 3, 17), (7, 3, 29, 3), (11, 23, 7, 7), (17, 3, 7, 3), (19, 3, 11, 3), (23, 11, 3, 3), (29, 3, 19, 3), (31, 7, 3, 3), (37, 7, 3, 3), (41, 3, 11, 3), (43, 3, 7, 3), (53, 7, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c72098a1_cert1 : certAll 1 1 0 (-329) 2209 [(61, 3, 7, 3), (67, 7, 3, 3), (71, 7, 3, 3), (73, 3, 7, 3), (79, 3, 23, 3), (83, 3, 7, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c72098a1_gens : allOn 1 1 0 (-329) 2209 [(0, 47, 1), (47, 282, 1), (21, 61, 1)] = true := by decide +kernel

-- 72266a1: 20 primes
set_option maxHeartbeats 0 in
theorem c72266a1_cert0 : certAll 1 (-1) 0 (-13) 1 [(5, 3, 17, 3), (7, 5, 3, 3), (11, 3, 19, 3), (13, 17, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 11, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c72266a1_cert1 : certAll 1 (-1) 0 (-13) 1 [(59, 3, 11, 3), (67, 5, 3, 3), (71, 3, 17, 3), (73, 11, 3, 3), (79, 5, 3, 3), (83, 3, 11, 3), (89, 3, 5, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c72266a1_gens : allOn 1 (-1) 0 (-13) 1 [(0, 1, 1), ((-2), 5, 1), (4, (-1), 1)] = true := by decide +kernel

-- 72379a1: 21 primes
set_option maxHeartbeats 0 in
theorem c72379a1_cert0 : certAll 0 1 1 (-6) 12 [(5, 3, 2, 3), (11, 2, 3, 13), (13, 3, 2, 3), (17, 11, 2, 3), (19, 2, 3, 3), (23, 2, 5, 3), (29, 3, 2, 3), (31, 2, 19, 3), (37, 3, 2, 3), (41, 5, 2, 3), (43, 2, 3, 3), (47, 2, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c72379a1_cert1 : certAll 0 1 1 (-6) 12 [(53, 3, 2, 3), (59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (73, 11, 2, 3), (79, 2, 11, 3), (83, 2, 3, 3), (89, 5, 2, 3), (97, 5, 2, 3)] = true := by decide +kernel
theorem c72379a1_gens : allOn 0 1 1 (-6) 12 [(0, 3, 1), (2, 3, 1), ((-2), 4, 1)] = true := by decide +kernel

-- 72382a1: 22 primes
set_option maxHeartbeats 0 in
theorem c72382a1_cert0 : certAll 1 1 0 (-64) 176 [(5, 11, 3, 73), (7, 3, 31, 3), (11, 19, 7, 7), (13, 3, 19, 3), (17, 3, 11, 3), (19, 3, 11, 3), (23, 7, 3, 3), (29, 3, 7, 3), (31, 11, 3, 3), (37, 7, 3, 3), (41, 3, 11, 3), (43, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c72382a1_cert1 : certAll 1 1 0 (-64) 176 [(47, 7, 3, 3), (53, 11, 3, 3), (61, 3, 17, 3), (67, 7, 3, 3), (71, 7, 3, 3), (73, 3, 7, 3), (79, 3, 7, 3), (83, 3, 7, 3), (89, 7, 3, 3), (97, 13, 3, 3)] = true := by decide +kernel
theorem c72382a1_gens : allOn 1 1 0 (-64) 176 [(4, 0, 1), (8, 12, 1), (5, 1, 1)] = true := by decide +kernel

-- 72410a1: 20 primes
set_option maxHeartbeats 0 in
theorem c72410a1_cert0 : certAll 1 (-1) 0 (-130) 676 [(7, 17, 3, 3), (11, 3, 17, 3), (17, 3, 11, 3), (19, 23, 3, 3), (23, 3, 11, 3), (29, 3, 23, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 17, 3), (43, 19, 3, 3), (47, 3, 11, 3), (53, 3, 19, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c72410a1_cert1 : certAll 1 (-1) 0 (-130) 676 [(61, 17, 3, 3), (67, 11, 3, 3), (71, 3, 23, 3), (73, 19, 3, 3), (79, 11, 3, 3), (83, 3, 11, 3), (89, 3, 17, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c72410a1_gens : allOn 1 (-1) 0 (-130) 676 [(0, 26, 1), (13, 26, 1), (3, 16, 1)] = true := by decide +kernel

-- 72471b1: 20 primes
set_option maxHeartbeats 0 in
theorem c72471b1_cert0 : certAll 0 (-1) 1 (-212) 1070 [(5, 11, 2, 23), (11, 2, 19, 13), (13, 5, 2, 5), (19, 2, 11, 5), (23, 2, 5, 5), (31, 2, 5, 5), (37, 11, 2, 5), (41, 5, 2, 5), (43, 2, 11, 5), (47, 2, 5, 5), (53, 11, 2, 5), (59, 2, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c72471b1_cert1 : certAll 0 (-1) 1 (-212) 1070 [(61, 5, 2, 5), (67, 2, 5, 5), (71, 2, 5, 5), (73, 5, 2, 5), (79, 2, 13, 5), (83, 2, 11, 5), (89, 13, 2, 5), (97, 19, 2, 5)] = true := by decide +kernel
theorem c72471b1_gens : allOn 0 (-1) 1 (-212) 1070 [(19, 59, 1), (5, 10, 1), ((-2), 38, 1)] = true := by decide +kernel

-- 72578a1: 21 primes
set_option maxHeartbeats 0 in
theorem c72578a1_cert0 : certAll 1 (-1) 0 (-286) 1936 [(5, 3, 7, 3), (7, 5, 3, 3), (13, 5, 3, 3), (17, 3, 29, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 7, 3), (37, 7, 3, 3), (41, 3, 17, 3), (43, 5, 3, 3), (47, 3, 5, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c72578a1_cert1 : certAll 1 (-1) 0 (-286) 1936 [(59, 3, 5, 3), (61, 5, 3, 3), (67, 7, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c72578a1_gens : allOn 1 (-1) 0 (-286) 1936 [(11, 0, 1), (10, (-6), 1), (14, 16, 1)] = true := by decide +kernel

-- 72683a1: 21 primes
set_option maxHeartbeats 0 in
theorem c72683a1_cert0 : certAll 1 1 1 19 42 [(5, 2, 3, 2), (7, 3, 5, 3), (11, 7, 2, 2), (17, 2, 5, 2), (19, 2, 7, 2), (23, 7, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 5, 2, 2), (41, 2, 11, 2), (43, 3, 2, 2), (53, 5, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c72683a1_cert1 : certAll 1 1 1 19 42 [(59, 2, 3, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 5, 2, 2), (73, 2, 5, 2), (79, 3, 2, 2), (83, 2, 5, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c72683a1_gens : allOn 1 1 1 19 42 [(0, 6, 1), (13, 45, 1), (78, 656, 1)] = true := by decide +kernel

-- 72701a1: 19 primes
set_option maxHeartbeats 0 in
theorem c72701a1_cert0 : certAll 1 1 1 (-2) 12 [(5, 2, 3, 2), (11, 13, 2, 2), (13, 2, 11, 2), (17, 2, 11, 2), (23, 11, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 11, 2, 2), (41, 2, 13, 2), (43, 3, 2, 2), (47, 2, 3, 2), (53, 11, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c72701a1_cert1 : certAll 1 1 1 (-2) 12 [(59, 2, 3, 2), (61, 2, 13, 2), (67, 11, 2, 2), (71, 13, 2, 2), (79, 3, 2, 2), (83, 2, 11, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c72701a1_gens : allOn 1 1 1 (-2) 12 [(0, 3, 1), ((-2), 4, 1), ((-3), 2, 1)] = true := by decide +kernel

-- 72751b1: 19 primes
set_option maxHeartbeats 0 in
theorem c72751b1_cert0 : certAll 0 1 1 (-420) 3180 [(5, 3, 2, 3), (11, 2, 3, 13), (13, 3, 2, 3), (17, 13, 2, 3), (23, 2, 29, 3), (29, 3, 2, 3), (37, 3, 2, 3), (43, 2, 3, 3), (47, 2, 11, 3), (53, 3, 2, 3), (59, 2, 3, 3), (61, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c72751b1_cert1 : certAll 0 1 1 (-420) 3180 [(67, 2, 3, 3), (71, 2, 11, 3), (73, 23, 2, 3), (79, 2, 11, 3), (83, 2, 3, 3), (89, 11, 2, 3), (97, 29, 2, 3)] = true := by decide +kernel
theorem c72751b1_gens : allOn 0 1 1 (-420) 3180 [((-3), 66, 1), (11, 3, 1), (318, 53, 27)] = true := by decide +kernel

-- 73132a1: 21 primes
set_option maxHeartbeats 0 in
theorem c73132a1_cert0 : certAll 0 1 0 (-421) 3111 [(5, 3, 7, 3), (7, 3, 5, 3), (11, 13, 3, 7), (13, 3, 17, 3), (17, 11, 3, 3), (19, 11, 3, 3), (23, 3, 5, 3), (29, 3, 11, 3), (31, 3, 13, 3), (37, 3, 11, 3), (41, 5, 3, 3), (43, 17, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c73132a1_cert1 : certAll 0 1 0 (-421) 3111 [(53, 3, 11, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 3, 11, 3), (83, 11, 3, 3), (97, 5, 3, 3)] = true := by decide +kernel
theorem c73132a1_gens : allOn 0 1 0 (-421) 3111 [(25, 94, 1), ((-22), 47, 1), (17, 34, 1)] = true := by decide +kernel

-- 73136b1: 21 primes
set_option maxHeartbeats 0 in
theorem c73136b1_cert0 : certAll 0 1 0 (-112) 564 [(5, 3, 13, 3), (11, 13, 3, 13), (13, 3, 19, 3), (17, 5, 3, 3), (19, 5, 3, 3), (29, 3, 11, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3), (47, 3, 5, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c73136b1_cert1 : certAll 0 1 0 (-112) 564 [(59, 11, 3, 3), (61, 3, 13, 3), (67, 13, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 11, 3), (83, 5, 3, 3), (89, 11, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c73136b1_gens : allOn 0 1 0 (-112) 564 [(4, 14, 1), ((-10), 28, 1), ((-2), 28, 1)] = true := by decide +kernel

-- 73334a1: 21 primes
set_option maxHeartbeats 0 in
theorem c73334a1_cert0 : certAll 1 0 1 (-18) 32 [(5, 3, 7, 3), (7, 3, 13, 3), (11, 5, 3, 7), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (31, 3, 7, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 19, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c73334a1_cert1 : certAll 1 0 1 (-18) 32 [(59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c73334a1_gens : allOn 1 0 1 (-18) 32 [(3, 1, 1), (1, 3, 1), (2, 1, 1)] = true := by decide +kernel

-- 73397c1: 22 primes
set_option maxHeartbeats 0 in
theorem c73397c1_cert0 : certAll 0 1 1 (-24) 36 [(5, 3, 2, 3), (7, 2, 29, 3), (11, 2, 3, 5), (13, 3, 2, 3), (17, 7, 2, 3), (23, 2, 11, 3), (29, 3, 2, 3), (31, 2, 7, 3), (37, 3, 2, 3), (41, 7, 2, 3), (43, 2, 3, 3), (47, 2, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c73397c1_cert1 : certAll 0 1 1 (-24) 36 [(53, 3, 2, 3), (59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 31, 3), (73, 11, 2, 3), (79, 2, 7, 3), (83, 2, 3, 3), (89, 7, 2, 3), (97, 17, 2, 3)] = true := by decide +kernel
theorem c73397c1_gens : allOn 0 1 1 (-24) 36 [(2, 0, 1), (3, 0, 1), (4, 4, 1)] = true := by decide +kernel

-- 73401a1: 22 primes
set_option maxHeartbeats 0 in
theorem c73401a1_cert0 : certAll 0 (-1) 1 (-4) 24 [(5, 7, 2, 7), (7, 2, 11, 5), (11, 2, 29, 5), (13, 17, 2, 5), (17, 7, 2, 5), (19, 2, 7, 7), (23, 2, 11, 5), (29, 7, 2, 5), (31, 2, 7, 5), (37, 17, 2, 5), (41, 7, 2, 5), (47, 2, 11, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c73401a1_cert1 : certAll 0 (-1) 1 (-4) 24 [(53, 7, 2, 5), (59, 2, 11, 5), (61, 11, 2, 5), (67, 2, 7, 5), (71, 2, 17, 5), (73, 11, 2, 5), (79, 2, 7, 5), (83, 2, 19, 5), (89, 7, 2, 5), (97, 11, 2, 5)] = true := by decide +kernel
theorem c73401a1_gens : allOn 0 (-1) 1 (-4) 24 [(1, 4, 1), ((-2), 4, 1), (4, 7, 1)] = true := by decide +kernel

-- 73434b1: 20 primes
set_option maxHeartbeats 0 in
theorem c73434b1_cert0 : certAll 1 1 0 (-19) 1 [(5, 7, 17, 7), (7, 5, 17, 5), (11, 7, 23, 7), (17, 5, 11, 5), (19, 5, 7, 5), (23, 7, 5, 5), (29, 5, 17, 7), (37, 11, 5, 5), (41, 5, 11, 5), (43, 5, 7, 5), (47, 7, 5, 5), (53, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c73434b1_cert1 : certAll 1 1 0 (-19) 1 [(59, 7, 5, 5), (61, 5, 7, 5), (67, 17, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 7, 5), (83, 5, 11, 5), (97, 17, 5, 5)] = true := by decide +kernel
theorem c73434b1_gens : allOn 1 1 0 (-19) 1 [((-2), 7, 1), (4, 1, 1), (0, 1, 1)] = true := by decide +kernel

-- 73931a1: 20 primes
set_option maxHeartbeats 0 in
theorem c73931a1_cert0 : certAll 0 (-1) 1 (-2042) 36222 [(5, 17, 2, 17), (7, 2, 17, 3), (17, 3, 2, 3), (19, 2, 17, 3), (23, 2, 3, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 7, 2, 3), (41, 3, 2, 3), (43, 2, 19, 3), (53, 19, 2, 3), (59, 2, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c73931a1_cert1 : certAll 0 (-1) 1 (-2042) 36222 [(61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 3, 3), (73, 3, 2, 3), (79, 2, 7, 3), (83, 2, 7, 3), (89, 7, 2, 3), (97, 17, 2, 3)] = true := by decide +kernel
theorem c73931a1_gens : allOn 0 (-1) 1 (-2042) 36222 [(29, 23, 1), ((-18), 258, 1), (27, 6, 1)] = true := by decide +kernel

-- 74015a1: 21 primes
set_option maxHeartbeats 0 in
theorem c74015a1_cert0 : certAll 0 (-1) 1 84 72 [(7, 2, 19, 3), (11, 2, 7, 7), (13, 3, 2, 3), (17, 3, 2, 3), (19, 2, 13, 3), (23, 2, 3, 3), (29, 3, 2, 3), (37, 7, 2, 3), (41, 3, 2, 3), (43, 2, 7, 3), (47, 2, 3, 3), (53, 7, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c74015a1_cert1 : certAll 0 (-1) 1 84 72 [(59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 3, 3), (73, 3, 2, 3), (79, 2, 11, 3), (83, 2, 7, 3), (89, 7, 2, 3), (97, 7, 2, 3)] = true := by decide +kernel
theorem c74015a1_gens : allOn 0 (-1) 1 84 72 [(13, 56, 1), (12, 269, 27), (126, 1412, 1)] = true := by decide +kernel

-- 74174a1: 19 primes
set_option maxHeartbeats 0 in
theorem c74174a1_cert0 : certAll 1 0 1 (-83) 282 [(5, 3, 23, 3), (7, 3, 11, 3), (11, 5, 3, 7), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c74174a1_cert1 : certAll 1 0 1 (-83) 282 [(67, 5, 3, 3), (71, 3, 19, 3), (73, 19, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c74174a1_gens : allOn 1 0 1 (-83) 282 [(5, (-2), 1), (3, 6, 1), (6, 0, 1)] = true := by decide +kernel

-- 74179b1: 19 primes
set_option maxHeartbeats 0 in
theorem c74179b1_cert0 : certAll 0 0 1 (-97) 276 [(5, 3, 2, 3), (11, 2, 19, 3), (13, 11, 2, 3), (17, 3, 2, 3), (19, 2, 3, 3), (23, 2, 11, 3), (29, 3, 2, 3), (37, 11, 2, 3), (41, 3, 2, 3), (47, 2, 11, 3), (59, 2, 19, 3), (61, 19, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c74179b1_cert1 : certAll 0 0 1 (-97) 276 [(67, 2, 3, 3), (71, 2, 37, 3), (73, 29, 2, 3), (79, 2, 3, 3), (83, 2, 11, 3), (89, 3, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c74179b1_gens : allOn 0 0 1 (-97) 276 [((-4), 24, 1), (3, 3, 1), ((-11), 3, 1)] = true := by decide +kernel

-- 74216a1: 22 primes
set_option maxHeartbeats 0 in
theorem c74216a1_cert0 : certAll 0 0 0 (-76) 244 [(5, 3, 7, 3), (7, 5, 3, 3), (11, 3, 7, 3), (13, 7, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 7, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 7, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c74216a1_cert1 : certAll 0 0 0 (-76) 244 [(47, 3, 7, 3), (53, 3, 5, 3), (61, 11, 3, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c74216a1_gens : allOn 0 0 0 (-76) 244 [(6, 2, 1), (4, 2, 1), (2, 10, 1)] = true := by decide +kernel

-- 74350c1: 21 primes
set_option maxHeartbeats 0 in
theorem c74350c1_cert0 : certAll 1 0 1 (-51) 98 [(7, 3, 17, 3), (11, 7, 3, 7), (13, 3, 7, 3), (17, 7, 3, 3), (19, 11, 3, 3), (23, 3, 11, 3), (29, 3, 11, 3), (31, 3, 7, 3), (37, 3, 7, 3), (41, 7, 3, 3), (43, 13, 3, 3), (47, 3, 29, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c74350c1_cert1 : certAll 1 0 1 (-51) 98 [(53, 3, 11, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 13, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 3, 7, 3), (83, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c74350c1_gens : allOn 1 0 1 (-51) 98 [(7, 6, 1), (2, 1, 1), ((-8), 6, 1)] = true := by decide +kernel

-- 74434a1: 21 primes
set_option maxHeartbeats 0 in
theorem c74434a1_cert0 : certAll 1 1 0 8 20 [(5, 53, 3, 53), (11, 5, 19, 13), (13, 3, 5, 3), (17, 3, 5, 3), (19, 3, 11, 3), (23, 5, 3, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 19, 3, 3), (41, 3, 5, 3), (43, 3, 19, 3), (47, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c74434a1_cert1 : certAll 1 1 0 8 20 [(53, 19, 3, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 23, 3), (89, 19, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c74434a1_gens : allOn 1 1 0 8 20 [((-2), 2, 1), (2, 6, 1), ((-1), 4, 1)] = true := by decide +kernel

-- 74451a1: 20 primes
set_option maxHeartbeats 0 in
theorem c74451a1_cert0 : certAll 0 (-1) 1 (-92) 362 [(5, 11, 2, 37), (7, 2, 41, 5), (11, 2, 7, 7), (17, 5, 2, 5), (19, 2, 11, 5), (29, 5, 2, 7), (31, 2, 5, 5), (37, 7, 2, 5), (41, 5, 2, 5), (43, 2, 11, 5), (47, 2, 5, 5), (53, 11, 2, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c74451a1_cert1 : certAll 0 (-1) 1 (-92) 362 [(59, 2, 5, 5), (61, 5, 2, 5), (67, 2, 5, 5), (71, 2, 5, 5), (73, 5, 2, 5), (79, 2, 7, 5), (89, 7, 2, 5), (97, 19, 2, 5)] = true := by decide +kernel
theorem c74451a1_gens : allOn 0 (-1) 1 (-92) 362 [(4, 6, 1), (17, 58, 1), (58, 35, 8)] = true := by decide +kernel

-- 74560p1: 21 primes
set_option maxHeartbeats 0 in
theorem c74560p1_cert0 : certAll 0 0 0 (-508) 4432 [(7, 31, 3, 3), (11, 3, 29, 3), (13, 11, 3, 3), (19, 11, 3, 3), (23, 3, 11, 3), (29, 3, 11, 3), (31, 11, 3, 3), (37, 23, 3, 3), (41, 3, 37, 3), (43, 23, 3, 3), (47, 3, 29, 3), (53, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c74560p1_cert1 : certAll 0 0 0 (-508) 4432 [(59, 3, 23, 3), (61, 11, 3, 3), (67, 23, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 41, 3, 3), (83, 3, 23, 3), (89, 3, 37, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c74560p1_gens : allOn 0 0 0 (-508) 4432 [(6, 40, 1), (14, 8, 1), (12, 8, 1)] = true := by decide +kernel

-- 74639b1: 22 primes
set_option maxHeartbeats 0 in
theorem c74639b1_cert0 : certAll 1 1 1 (-121) 462 [(5, 2, 3, 2), (7, 3, 5, 3), (11, 7, 2, 2), (13, 2, 7, 2), (17, 2, 5, 2), (23, 7, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 5, 2, 2), (41, 2, 13, 2), (43, 3, 2, 2), (47, 2, 3, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c74639b1_cert1 : certAll 1 1 1 (-121) 462 [(53, 5, 2, 2), (59, 2, 3, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 5, 2, 2), (73, 2, 5, 2), (79, 3, 2, 2), (83, 2, 5, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c74639b1_gens : allOn 1 1 1 (-121) 462 [(6, (-3), 1), (5, 1, 1), (156, (-70), 27)] = true := by decide +kernel

-- 74864b1: 21 primes
set_option maxHeartbeats 0 in
theorem c74864b1_cert0 : certAll 0 1 0 (-400) 2964 [(5, 3, 7, 3), (7, 3, 13, 3), (11, 5, 3, 7), (13, 3, 5, 3), (17, 13, 3, 3), (19, 5, 3, 3), (23, 3, 7, 3), (29, 3, 5, 3), (31, 3, 13, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c74864b1_cert1 : certAll 0 1 0 (-400) 2964 [(47, 3, 7, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 19, 3, 3), (79, 3, 11, 3), (83, 5, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c74864b1_gens : allOn 0 1 0 (-400) 2964 [(10, 8, 1), (12, 6, 1), ((-6), 72, 1)] = true := by decide +kernel

-- 74921g1: 21 primes
set_option maxHeartbeats 0 in
theorem c74921g1_cert0 : certAll 0 (-1) 1 (-604) (-596) [(5, 17, 2, 17), (13, 3, 2, 3), (17, 3, 2, 3), (19, 2, 17, 3), (23, 2, 3, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 31, 2, 3), (41, 3, 2, 3), (43, 2, 19, 3), (47, 2, 3, 3), (53, 17, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c74921g1_cert1 : certAll 0 (-1) 1 (-604) (-596) [(59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 3, 3), (73, 3, 2, 3), (79, 2, 19, 3), (83, 2, 17, 3), (89, 19, 2, 3), (97, 17, 2, 3)] = true := by decide +kernel
theorem c74921g1_gens : allOn 0 (-1) 1 (-604) (-596) [(47, 269, 1), ((-23), 24, 1), (26, 24, 1)] = true := by decide +kernel

-- 74999a1: 21 primes
set_option maxHeartbeats 0 in
theorem c74999a1_cert0 : certAll 0 (-1) 1 15 72 [(5, 13, 3, 13), (7, 3, 13, 3), (13, 3, 5, 3), (17, 3, 5, 3), (19, 3, 13, 3), (23, 5, 3, 3), (29, 3, 5, 3), (31, 5, 3, 3), (41, 3, 5, 3), (43, 3, 13, 3), (47, 5, 3, 3), (53, 13, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c74999a1_cert1 : certAll 0 (-1) 1 15 72 [(59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 7, 3), (83, 3, 7, 3), (89, 7, 3, 3), (97, 23, 3, 3)] = true := by decide +kernel
theorem c74999a1_gens : allOn 0 (-1) 1 15 72 [(6, 18, 1), (0, 8, 1), (10, 33, 1)] = true := by decide +kernel

-- 75159h1: 20 primes
set_option maxHeartbeats 0 in
theorem c75159h1_cert0 : certAll 1 (-1) 1 (-149) 474 [(5, 2, 17, 2), (11, 13, 2, 2), (13, 2, 23, 2), (17, 2, 11, 2), (19, 2, 13, 2), (23, 13, 2, 2), (29, 5, 2, 2), (31, 2, 5, 2), (37, 11, 2, 2), (43, 5, 2, 2), (47, 2, 5, 2), (53, 11, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c75159h1_cert1 : certAll 1 (-1) 1 (-149) 474 [(59, 2, 5, 2), (61, 2, 11, 2), (67, 11, 2, 2), (73, 2, 11, 2), (79, 5, 2, 2), (83, 2, 11, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c75159h1_gens : allOn 1 (-1) 1 (-149) 474 [((-4), 33, 1), (2, 12, 1), (3, 5, 1)] = true := by decide +kernel

-- 75692a1: 23 primes
set_option maxHeartbeats 0 in
theorem c75692a1_cert0 : certAll 0 0 0 8 25 [(5, 3, 7, 3), (7, 5, 3, 3), (11, 3, 7, 3), (13, 7, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 7, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c75692a1_cert1 : certAll 0 0 0 8 25 [(47, 3, 19, 3), (53, 3, 5, 3), (59, 3, 7, 3), (61, 7, 3, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c75692a1_gens : allOn 0 0 0 8 25 [((-2), 1, 1), (0, 5, 1), (2, 7, 1)] = true := by decide +kernel

-- 75729a1: 20 primes
set_option maxHeartbeats 0 in
theorem c75729a1_cert0 : certAll 0 (-1) 1 (-270) 1802 [(5, 7, 2, 7), (7, 2, 13, 5), (11, 2, 17, 7), (13, 11, 2, 5), (17, 7, 2, 5), (19, 2, 7, 5), (23, 2, 17, 5), (29, 7, 2, 5), (37, 11, 2, 5), (43, 2, 7, 5), (47, 2, 17, 5), (53, 7, 2, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c75729a1_cert1 : certAll 0 (-1) 1 (-270) 1802 [(59, 2, 11, 5), (67, 2, 7, 5), (71, 2, 23, 5), (73, 19, 2, 5), (79, 2, 7, 5), (83, 2, 11, 5), (89, 7, 2, 5), (97, 17, 2, 5)] = true := by decide +kernel
theorem c75729a1_gens : allOn 0 (-1) 1 (-270) 1802 [(9, 4, 1), (10, 1, 1), (11, 6, 1)] = true := by decide +kernel

-- 75765c1: 22 primes
set_option maxHeartbeats 0 in
theorem c75765c1_cert0 : certAll 0 (-1) 1 (-66) 236 [(7, 2, 19, 13), (11, 2, 17, 7), (13, 17, 2, 7), (17, 7, 2, 7), (19, 2, 7, 7), (23, 2, 17, 7), (29, 7, 2, 7), (31, 2, 7, 11), (37, 11, 2, 7), (41, 7, 2, 7), (43, 2, 7, 7), (47, 2, 11, 7)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c75765c1_cert1 : certAll 0 (-1) 1 (-66) 236 [(53, 7, 2, 7), (59, 2, 23, 7), (61, 11, 2, 7), (67, 2, 7, 7), (71, 2, 11, 7), (73, 29, 2, 7), (79, 2, 7, 7), (83, 2, 11, 7), (89, 7, 2, 7), (97, 17, 2, 7)] = true := by decide +kernel
theorem c75765c1_gens : allOn 0 (-1) 1 (-66) 236 [(3, 7, 1), (6, 4, 1), (5, 2, 1)] = true := by decide +kernel

-- 75772a1: 20 primes
set_option maxHeartbeats 0 in
theorem c75772a1_cert0 : certAll 0 0 0 (-14872) 698020 [(5, 3, 17, 3), (7, 5, 3, 3), (13, 23, 3, 3), (17, 3, 5, 3), (23, 3, 47, 3), (29, 3, 5, 3), (37, 29, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3), (47, 3, 23, 3), (53, 3, 5, 3), (59, 3, 23, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c75772a1_cert1 : certAll 0 0 0 (-14872) 698020 [(61, 23, 3, 3), (67, 5, 3, 3), (71, 3, 23, 3), (73, 29, 3, 3), (79, 5, 3, 3), (83, 3, 23, 3), (89, 3, 5, 3), (97, 23, 3, 3)] = true := by decide +kernel
theorem c75772a1_gens : allOn 0 0 0 (-14872) 698020 [(12, 722, 1), (69, 19, 1), (164, 1634, 1)] = true := by decide +kernel

-- 75781a1: 21 primes
set_option maxHeartbeats 0 in
theorem c75781a1_cert0 : certAll 0 0 1 (-13) 12 [(5, 3, 2, 3), (11, 2, 5, 3), (13, 5, 2, 3), (19, 2, 3, 3), (23, 2, 5, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 5, 2, 3), (41, 3, 2, 3), (43, 2, 3, 3), (47, 2, 5, 3), (53, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c75781a1_cert1 : certAll 0 0 1 (-13) 12 [(59, 2, 11, 3), (61, 11, 2, 3), (67, 2, 3, 3), (71, 2, 19, 3), (73, 19, 2, 3), (79, 2, 3, 3), (83, 2, 5, 3), (89, 3, 2, 3), (97, 5, 2, 3)] = true := by decide +kernel
theorem c75781a1_gens : allOn 0 0 1 (-13) 12 [(1, 0, 1), (3, 0, 1), (0, 3, 1)] = true := by decide +kernel

-- 76074b1: 21 primes
set_option maxHeartbeats 0 in
theorem c76074b1_cert0 : certAll 1 0 1 (-163) 602 [(5, 7, 37, 7), (7, 5, 13, 5), (11, 5, 17, 7), (13, 11, 5, 5), (17, 7, 5, 5), (19, 5, 7, 5), (23, 5, 17, 5), (37, 11, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5), (47, 5, 17, 5), (53, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c76074b1_cert1 : certAll 1 0 1 (-163) 602 [(59, 5, 11, 5), (61, 11, 5, 5), (67, 5, 7, 5), (71, 5, 43, 5), (73, 17, 5, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 43, 5, 5)] = true := by decide +kernel
theorem c76074b1_gens : allOn 1 0 1 (-163) 602 [(13, 20, 1), (4, 2, 1), ((-14), (-7), 1)] = true := by decide +kernel

-- 76119a1: 22 primes
set_option maxHeartbeats 0 in
theorem c76119a1_cert0 : certAll 0 (-1) 1 (-50) 152 [(5, 11, 2, 13), (7, 2, 41, 5), (11, 2, 7, 7), (13, 7, 2, 5), (17, 7, 2, 5), (19, 2, 11, 5), (23, 2, 13, 5), (29, 11, 2, 5), (31, 2, 7, 5), (37, 7, 2, 5), (41, 7, 2, 7), (43, 2, 11, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c76119a1_cert1 : certAll 0 (-1) 1 (-50) 152 [(53, 11, 2, 5), (59, 2, 7, 5), (61, 7, 2, 5), (67, 2, 11, 5), (71, 2, 43, 5), (73, 13, 2, 5), (79, 2, 7, 5), (83, 2, 7, 5), (89, 7, 2, 5), (97, 19, 2, 5)] = true := by decide +kernel
theorem c76119a1_gens : allOn 0 (-1) 1 (-50) 152 [(5, 1, 1), (2, 7, 1), (4, 0, 1)] = true := by decide +kernel

-- 76136c1: 19 primes
set_option maxHeartbeats 0 in
theorem c76136c1_cert0 : certAll 0 (-1) 0 (-44) 100 [(5, 7, 3, 7), (7, 3, 13, 3), (11, 5, 23, 5), (13, 3, 5, 3), (19, 3, 7, 3), (23, 5, 3, 3), (29, 3, 5, 3), (37, 23, 3, 3), (41, 3, 5, 3), (43, 3, 7, 3), (47, 5, 3, 3), (59, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c76136c1_cert1 : certAll 0 (-1) 0 (-44) 100 [(61, 3, 5, 3), (67, 5, 3, 3), (73, 3, 5, 3), (79, 3, 7, 3), (83, 3, 23, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c76136c1_gens : allOn 0 (-1) 0 (-44) 100 [(2, 4, 1), (0, 10, 1), (6, 4, 1)] = true := by decide +kernel

-- 76338h1: 22 primes
set_option maxHeartbeats 0 in
theorem c76338h1_cert0 : certAll 1 (-1) 0 (-51) 233 [(5, 19, 17, 37), (7, 5, 13, 5), (11, 7, 19, 13), (13, 5, 7, 5), (17, 5, 11, 5), (19, 5, 7, 5), (23, 7, 5, 5), (29, 5, 11, 7), (31, 11, 5, 5), (37, 11, 5, 5), (41, 5, 17, 5), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c76338h1_cert1 : certAll 1 (-1) 0 (-51) 233 [(47, 7, 5, 5), (53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (67, 11, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 23, 5, 5)] = true := by decide +kernel
theorem c76338h1_gens : allOn 1 (-1) 0 (-51) 233 [(4, 7, 1), ((-2), 19, 1), ((-8), 13, 1)] = true := by decide +kernel

-- 76358e1: 21 primes
set_option maxHeartbeats 0 in
theorem c76358e1_cert0 : certAll 1 (-1) 1 (-159) 519 [(5, 3, 7, 3), (7, 5, 3, 3), (11, 3, 7, 3), (13, 5, 3, 3), (17, 3, 7, 3), (19, 5, 3, 3), (23, 3, 5, 3), (31, 7, 3, 3), (37, 7, 3, 3), (41, 3, 13, 3), (43, 5, 3, 3), (47, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c76358e1_cert1 : certAll 1 (-1) 1 (-159) 519 [(53, 3, 5, 3), (59, 3, 5, 3), (61, 5, 3, 3), (67, 7, 3, 3), (71, 3, 5, 3), (79, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c76358e1_gens : allOn 1 (-1) 1 (-159) 519 [(3, 6, 1), ((-13), 22, 1), (19, 54, 1)] = true := by decide +kernel

-- 76599a1: 22 primes
set_option maxHeartbeats 0 in
theorem c76599a1_cert0 : certAll 1 (-1) 1 (-104) 434 [(5, 2, 17, 2), (7, 5, 29, 5), (11, 7, 2, 2), (13, 2, 7, 2), (17, 2, 11, 2), (19, 2, 7, 2), (23, 7, 2, 2), (29, 5, 2, 2), (31, 2, 5, 2), (37, 11, 2, 2), (41, 2, 13, 2), (43, 5, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c76599a1_cert1 : certAll 1 (-1) 1 (-104) 434 [(47, 2, 5, 2), (59, 2, 5, 2), (61, 2, 7, 2), (67, 11, 2, 2), (71, 7, 2, 2), (73, 2, 7, 2), (79, 5, 2, 2), (83, 2, 11, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c76599a1_gens : allOn 1 (-1) 1 (-104) 434 [(6, (-5), 1), (3, 10, 1), (7, 0, 1)] = true := by decide +kernel

-- 76626e1: 20 primes
set_option maxHeartbeats 0 in
theorem c76626e1_cert0 : certAll 1 (-1) 0 (-429) 3509 [(5, 23, 17, 23), (7, 5, 13, 5), (13, 17, 5, 5), (17, 7, 5, 5), (19, 5, 7, 5), (23, 5, 17, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 17, 5, 5), (41, 7, 5, 7), (47, 5, 17, 5), (53, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c76626e1_cert1 : certAll 1 (-1) 0 (-429) 3509 [(61, 37, 5, 5), (67, 5, 7, 5), (71, 5, 23, 5), (73, 19, 5, 5), (79, 5, 7, 5), (83, 5, 17, 5), (89, 7, 5, 5), (97, 17, 5, 5)] = true := by decide +kernel
theorem c76626e1_gens : allOn 1 (-1) 0 (-429) 3509 [(22, 55, 1), (10, 7, 1), (14, 3, 1)] = true := by decide +kernel

-- 76644c1: 23 primes
set_option maxHeartbeats 0 in
theorem c76644c1_cert0 : certAll 0 0 0 (-192) 1105 [(5, 31, 7, 53), (7, 5, 11, 5), (11, 5, 7, 7), (13, 7, 5, 5), (17, 23, 5, 5), (19, 5, 23, 5), (23, 5, 7, 5), (29, 7, 5, 5), (31, 5, 29, 5), (37, 7, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c76644c1_cert1 : certAll 0 0 0 (-192) 1105 [(47, 5, 7, 5), (53, 7, 5, 5), (59, 5, 23, 5), (61, 19, 5, 5), (67, 5, 19, 5), (71, 5, 19, 5), (73, 19, 5, 5), (79, 5, 23, 5), (83, 5, 7, 5), (89, 7, 5, 5), (97, 7, 5, 5)] = true := by decide +kernel
theorem c76644c1_gens : allOn 0 0 0 (-192) 1105 [(8, 9, 1), (2, 27, 1), ((-10), 45, 1)] = true := by decide +kernel

-- 76784h1: 22 primes
set_option maxHeartbeats 0 in
theorem c76784h1_cert0 : certAll 0 (-1) 0 64 64 [(5, 7, 3, 7), (7, 3, 5, 3), (11, 7, 5, 7), (13, 3, 7, 3), (17, 3, 5, 3), (23, 7, 3, 3), (29, 3, 13, 3), (31, 5, 3, 3), (37, 5, 3, 3), (41, 3, 11, 3), (43, 3, 5, 3), (47, 7, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c76784h1_cert1 : certAll 0 (-1) 0 64 64 [(53, 5, 3, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 7, 3), (83, 3, 5, 3), (89, 5, 3, 3), (97, 5, 3, 3)] = true := by decide +kernel
theorem c76784h1_gens : allOn 0 (-1) 0 64 64 [(0, 8, 1), (8, 32, 1), (32, 184, 1)] = true := by decide +kernel

-- 76784i1: 21 primes
set_option maxHeartbeats 0 in
theorem c76784i1_cert0 : certAll 0 0 0 (-1579) 24154 [(5, 3, 7, 3), (7, 5, 3, 3), (11, 3, 7, 3), (13, 5, 3, 3), (17, 3, 13, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 7, 3), (31, 11, 3, 3), (37, 7, 3, 3), (41, 3, 11, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c76784i1_cert1 : certAll 0 0 0 (-1579) 24154 [(47, 3, 5, 3), (53, 3, 5, 3), (61, 5, 3, 3), (67, 7, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 5, 3, 3), (83, 3, 7, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c76784i1_gens : allOn 0 0 0 (-1579) 24154 [(21, 16, 1), (23, 2, 1), (15, 62, 1)] = true := by decide +kernel

-- 76962e1: 22 primes
set_option maxHeartbeats 0 in
theorem c76962e1_cert0 : certAll 1 0 1 (-628) 6062 [(5, 11, 17, 23), (7, 5, 13, 5), (11, 5, 17, 13), (13, 11, 5, 5), (17, 7, 5, 5), (19, 5, 7, 5), (23, 5, 11, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 17, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c76962e1_cert1 : certAll 1 0 1 (-628) 6062 [(53, 7, 5, 5), (59, 5, 29, 5), (61, 11, 5, 5), (67, 5, 7, 5), (71, 5, 11, 5), (73, 11, 5, 5), (79, 5, 7, 5), (83, 5, 17, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c76962e1_gens : allOn 1 0 1 (-628) 6062 [(16, 5, 1), (7, 41, 1), (13, 5, 1)] = true := by decide +kernel

-- 77063a1: 21 primes
set_option maxHeartbeats 0 in
theorem c77063a1_cert0 : certAll 0 0 1 (-104) (-175) [(5, 11, 23, 13), (11, 13, 19, 13), (13, 5, 19, 5), (17, 5, 61, 5), (19, 5, 13, 5), (23, 13, 5, 5), (31, 11, 5, 5), (37, 19, 5, 5), (41, 5, 19, 5), (43, 5, 11, 5), (47, 11, 5, 5), (53, 13, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c77063a1_cert1 : certAll 0 0 1 (-104) (-175) [(59, 11, 5, 5), (61, 5, 13, 5), (67, 23, 5, 5), (71, 13, 5, 5), (73, 5, 13, 5), (79, 5, 11, 5), (83, 5, 17, 5), (89, 11, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c77063a1_gens : allOn 0 0 1 (-104) (-175) [(17, 54, 1), ((-3), 10, 1), (11, 3, 1)] = true := by decide +kernel

-- 77336d1: 21 primes
set_option maxHeartbeats 0 in
theorem c77336d1_cert0 : certAll 0 1 0 (-140) 784 [(5, 3, 13, 3), (11, 5, 3, 13), (13, 3, 5, 3), (17, 11, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 19, 3), (37, 3, 5, 3), (41, 11, 3, 3), (43, 5, 3, 3), (47, 3, 19, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c77336d1_cert1 : certAll 0 1 0 (-140) 784 [(53, 3, 5, 3), (59, 5, 3, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 3, 11, 3), (83, 5, 3, 3), (89, 11, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c77336d1_gens : allOn 0 1 0 (-140) 784 [(0, 28, 1), (14, 42, 1), (7, 14, 1)] = true := by decide +kernel

-- 77346a1: 23 primes
set_option maxHeartbeats 0 in
theorem c77346a1_cert0 : certAll 1 (-1) 0 (-276) 1836 [(5, 7, 13, 7), (7, 5, 19, 5), (11, 7, 17, 7), (13, 5, 7, 5), (17, 5, 11, 5), (19, 5, 7, 5), (23, 7, 5, 5), (29, 5, 11, 7), (31, 11, 5, 5), (37, 11, 5, 5), (41, 5, 13, 5), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c77346a1_cert1 : certAll 1 (-1) 0 (-276) 1836 [(47, 7, 5, 5), (53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (67, 11, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 19, 5, 5)] = true := by decide +kernel
theorem c77346a1_gens : allOn 1 (-1) 0 (-276) 1836 [(10, (-6), 1), (9, 0, 1), (78, (-45), 8)] = true := by decide +kernel

-- 77346d1: 21 primes
set_option maxHeartbeats 0 in
theorem c77346d1_cert0 : certAll 1 (-1) 0 99 1093 [(5, 7, 13, 7), (7, 5, 11, 5), (11, 7, 19, 7), (13, 5, 7, 5), (19, 5, 7, 5), (23, 7, 5, 5), (29, 5, 13, 7), (31, 11, 5, 5), (37, 11, 5, 5), (41, 5, 13, 5), (43, 5, 7, 5), (53, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c77346d1_cert1 : certAll 1 (-1) 0 99 1093 [(59, 7, 5, 5), (61, 5, 7, 5), (67, 11, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c77346d1_gens : allOn 1 (-1) 0 99 1093 [(2, 35, 1), (26, 131, 1), (11, 53, 1)] = true := by decide +kernel

-- 77496f1: 23 primes
set_option maxHeartbeats 0 in
theorem c77496f1_cert0 : certAll 0 1 0 (-660) 6624 [(5, 41, 13, 53), (7, 5, 11, 5), (11, 5, 19, 13), (13, 11, 5, 5), (17, 7, 5, 5), (19, 5, 7, 5), (23, 5, 11, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 11, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c77496f1_cert1 : certAll 0 1 0 (-660) 6624 [(47, 5, 11, 5), (53, 7, 5, 5), (59, 5, 19, 5), (61, 19, 5, 5), (67, 5, 7, 5), (71, 5, 23, 5), (73, 19, 5, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c77496f1_gens : allOn 0 1 0 (-660) 6624 [(6, 54, 1), (24, 72, 1), (15, 18, 1)] = true := by decide +kernel

-- 77555d1: 22 primes
set_option maxHeartbeats 0 in
theorem c77555d1_cert0 : certAll 1 1 1 (-100) 342 [(7, 3, 11, 3), (11, 7, 2, 2), (13, 2, 7, 2), (17, 2, 11, 2), (19, 2, 7, 2), (23, 7, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 11, 2, 2), (41, 2, 13, 2), (43, 3, 2, 2), (47, 2, 3, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c77555d1_cert1 : certAll 1 1 1 (-100) 342 [(53, 7, 2, 2), (59, 2, 3, 2), (61, 2, 7, 2), (67, 11, 2, 2), (71, 7, 2, 2), (73, 2, 7, 2), (79, 3, 2, 2), (83, 2, 11, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c77555d1_gens : allOn 1 1 1 (-100) 342 [(2, 11, 1), (5, (-2), 1), (6, (-6), 1)] = true := by decide +kernel

-- 77709a1: 22 primes
set_option maxHeartbeats 0 in
theorem c77709a1_cert0 : certAll 1 1 1 (-20) (-34) [(5, 2, 13, 2), (11, 5, 2, 2), (13, 2, 5, 2), (17, 2, 5, 2), (19, 2, 31, 2), (23, 5, 2, 2), (29, 11, 2, 2), (31, 2, 19, 2), (37, 11, 2, 2), (41, 2, 5, 2), (43, 5, 2, 2), (47, 2, 11, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c77709a1_cert1 : certAll 1 1 1 (-20) (-34) [(53, 11, 2, 2), (59, 2, 47, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 5, 2, 2), (73, 2, 5, 2), (79, 5, 2, 2), (83, 2, 11, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c77709a1_gens : allOn 1 1 1 (-20) (-34) [((-3), 4, 1), ((-2), 2, 1), ((-4), 2, 1)] = true := by decide +kernel

-- 77725c1: 21 primes
set_option maxHeartbeats 0 in
theorem c77725c1_cert0 : certAll 1 0 0 (-838) 9417 [(7, 3, 11, 3), (11, 7, 2, 2), (13, 2, 7, 2), (17, 2, 3, 2), (19, 2, 3, 2), (29, 3, 2, 2), (31, 2, 7, 2), (37, 3, 2, 2), (41, 2, 3, 2), (43, 37, 2, 2), (47, 2, 11, 2), (53, 3, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c77725c1_cert1 : certAll 1 0 0 (-838) 9417 [(59, 2, 3, 2), (61, 2, 7, 2), (67, 11, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (83, 2, 3, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c77725c1_gens : allOn 1 0 0 (-838) 9417 [(7, 59, 1), (17, 4, 1), ((-8), 129, 1)] = true := by decide +kernel

-- 77790a1: 20 primes
set_option maxHeartbeats 0 in
theorem c77790a1_cert0 : certAll 1 1 0 (-18) 72 [(7, 13, 11, 13), (11, 7, 17, 7), (13, 11, 7, 7), (17, 7, 11, 7), (19, 13, 7, 7), (23, 7, 11, 7), (29, 7, 13, 7), (31, 11, 7, 11), (37, 11, 7, 7), (41, 7, 13, 7), (47, 7, 11, 7), (53, 7, 13, 7)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c77790a1_cert1 : certAll 1 1 0 (-18) 72 [(59, 7, 23, 7), (61, 37, 7, 7), (67, 11, 7, 7), (73, 19, 7, 7), (79, 11, 7, 7), (83, 7, 11, 7), (89, 7, 13, 7), (97, 11, 7, 7)] = true := by decide +kernel
theorem c77790a1_gens : allOn 1 1 0 (-18) 72 [(6, 12, 1), ((-4), 12, 1), (1, 7, 1)] = true := by decide +kernel

-- 78185b1: 18 primes
set_option maxHeartbeats 0 in
theorem c78185b1_cert0 : certAll 1 0 0 (-1) 30 [(7, 3, 31, 3), (13, 2, 7, 2), (17, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 7, 2), (37, 3, 2, 2), (41, 2, 3, 2), (43, 13, 2, 2), (47, 2, 23, 2), (53, 3, 2, 2), (59, 2, 3, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c78185b1_cert1 : certAll 1 0 0 (-1) 30 [(67, 13, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (83, 2, 3, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c78185b1_gens : allOn 1 0 0 (-1) 30 [((-2), 6, 1), (3, 6, 1), (1, 5, 1)] = true := by decide +kernel

-- 78242a1: 20 primes
set_option maxHeartbeats 0 in
theorem c78242a1_cert0 : certAll 1 (-1) 0 (-3016) 64516 [(5, 3, 7, 3), (7, 5, 3, 3), (11, 3, 7, 3), (13, 5, 3, 3), (17, 3, 11, 3), (23, 3, 5, 3), (31, 17, 3, 3), (37, 7, 3, 3), (41, 3, 11, 3), (43, 5, 3, 3), (47, 3, 5, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c78242a1_cert1 : certAll 1 (-1) 0 (-3016) 64516 [(59, 3, 5, 3), (61, 5, 3, 3), (67, 7, 3, 3), (73, 5, 3, 3), (79, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3), (97, 23, 3, 3)] = true := by decide +kernel
theorem c78242a1_gens : allOn 1 (-1) 0 (-3016) 64516 [(30, 4, 1), (87, 631, 1), (4130, (-716), 125)] = true := by decide +kernel

-- 78287b1: 21 primes
set_option maxHeartbeats 0 in
theorem c78287b1_cert0 : certAll 1 1 1 (-74) 210 [(5, 2, 3, 2), (7, 3, 29, 3), (13, 2, 5, 2), (19, 2, 37, 2), (23, 5, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 7, 2, 2), (41, 2, 5, 2), (43, 3, 2, 2), (47, 2, 3, 2), (53, 19, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c78287b1_cert1 : certAll 1 1 1 (-74) 210 [(59, 2, 3, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 5, 2, 2), (73, 2, 5, 2), (79, 3, 2, 2), (83, 2, 7, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c78287b1_gens : allOn 1 1 1 (-74) 210 [(6, 2, 1), ((-5), 24, 1), (10, 19, 1)] = true := by decide +kernel

-- 78344a1: 21 primes
set_option maxHeartbeats 0 in
theorem c78344a1_cert0 : certAll 0 1 0 (-12) 49 [(5, 3, 13, 3), (11, 13, 3, 13), (13, 3, 19, 3), (17, 5, 3, 3), (19, 5, 3, 3), (29, 3, 13, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3), (47, 3, 5, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c78344a1_cert1 : certAll 0 1 0 (-12) 49 [(59, 11, 3, 3), (61, 3, 11, 3), (67, 11, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 29, 3), (83, 5, 3, 3), (89, 11, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c78344a1_gens : allOn 0 1 0 (-12) 49 [((-4), 7, 1), (3, 7, 1), (24, 119, 1)] = true := by decide +kernel

-- 78361a1: 21 primes
set_option maxHeartbeats 0 in
theorem c78361a1_cert0 : certAll 1 (-1) 1 (-27) 90 [(5, 2, 53, 2), (7, 5, 3, 3), (11, 3, 2, 2), (13, 2, 3, 2), (17, 2, 5, 2), (19, 2, 3, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 11, 2, 2), (41, 2, 5, 2), (47, 2, 11, 2), (53, 3, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c78361a1_cert1 : certAll 1 (-1) 1 (-27) 90 [(59, 2, 17, 2), (61, 2, 3, 2), (67, 5, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 5, 2, 2), (83, 2, 11, 2), (89, 2, 5, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c78361a1_gens : allOn 1 (-1) 1 (-27) 90 [((-2), 12, 1), (21, 81, 1), (30, 27, 8)] = true := by decide +kernel

-- 78830a1: 22 primes
set_option maxHeartbeats 0 in
theorem c78830a1_cert0 : certAll 1 0 1 (-274) 1716 [(7, 3, 19, 3), (11, 13, 3, 7), (13, 3, 19, 3), (17, 19, 3, 3), (19, 13, 3, 3), (23, 3, 7, 3), (29, 3, 13, 3), (31, 3, 19, 3), (37, 3, 13, 3), (41, 7, 3, 3), (43, 13, 3, 3), (47, 3, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c78830a1_cert1 : certAll 1 0 1 (-274) 1716 [(53, 3, 13, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 7, 3, 3), (71, 3, 23, 3), (73, 23, 3, 3), (79, 3, 19, 3), (83, 13, 3, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c78830a1_gens : allOn 1 0 1 (-274) 1716 [(13, 13, 1), (9, (-3), 1), (10, (-8), 1)] = true := by decide +kernel

-- 78923b1: 22 primes
set_option maxHeartbeats 0 in
theorem c78923b1_cert0 : certAll 0 0 1 (-676) 7140 [(5, 3, 17, 3), (7, 5, 3, 3), (11, 3, 17, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 17, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3), (47, 3, 17, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c78923b1_cert1 : certAll 0 0 1 (-676) 7140 [(53, 3, 5, 3), (59, 3, 19, 3), (61, 11, 3, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 5, 3, 3), (83, 3, 17, 3), (89, 3, 5, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c78923b1_gens : allOn 0 0 1 (-676) 7140 [(0, 84, 1), (26, 84, 1), (338, 1855, 8)] = true := by decide +kernel

-- 79077f1: 22 primes
set_option maxHeartbeats 0 in
theorem c79077f1_cert0 : certAll 0 1 1 (-214) 436 [(5, 7, 2, 7), (7, 2, 11, 5), (11, 2, 23, 5), (13, 11, 2, 5), (17, 7, 2, 5), (19, 2, 7, 7), (23, 2, 11, 5), (29, 7, 2, 5), (31, 2, 7, 5), (37, 11, 2, 5), (41, 7, 2, 5), (47, 2, 11, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c79077f1_cert1 : certAll 0 1 1 (-214) 436 [(53, 7, 2, 5), (59, 2, 31, 5), (61, 29, 2, 5), (67, 2, 7, 5), (71, 2, 29, 5), (73, 59, 2, 5), (79, 2, 7, 5), (83, 2, 11, 5), (89, 7, 2, 5), (97, 11, 2, 5)] = true := by decide +kernel
theorem c79077f1_gens : allOn 0 1 1 (-214) 436 [((-7), 40, 1), (2, 4, 1), ((-16), 4, 1)] = true := by decide +kernel

-- 79110c1: 22 primes
set_option maxHeartbeats 0 in
theorem c79110c1_cert0 : certAll 1 (-1) 0 (-135) 625 [(7, 11, 29, 13), (11, 7, 17, 13), (13, 11, 7, 7), (17, 7, 11, 7), (19, 13, 7, 7), (23, 7, 19, 7), (29, 7, 13, 7), (31, 11, 7, 7), (37, 11, 7, 7), (41, 7, 11, 7), (43, 13, 7, 7), (47, 7, 19, 7)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c79110c1_cert1 : certAll 1 (-1) 0 (-135) 625 [(53, 7, 13, 7), (59, 7, 11, 7), (61, 11, 7, 7), (67, 13, 7, 7), (71, 7, 19, 7), (73, 23, 7, 7), (79, 11, 7, 7), (83, 7, 11, 7), (89, 7, 11, 7), (97, 19, 7, 7)] = true := by decide +kernel
theorem c79110c1_gens : allOn 1 (-1) 0 (-135) 625 [(5, 5, 1), (8, (-7), 1), (20, 65, 1)] = true := by decide +kernel

-- 79198d1: 20 primes
set_option maxHeartbeats 0 in
theorem c79198d1_cert0 : certAll 1 0 1 (-60) 110 [(5, 3, 13, 3), (11, 13, 3, 13), (13, 3, 43, 3), (17, 5, 3, 3), (23, 3, 5, 3), (29, 3, 13, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3), (47, 3, 5, 3), (53, 3, 5, 3), (59, 13, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c79198d1_cert1 : certAll 1 0 1 (-60) 110 [(61, 3, 13, 3), (67, 13, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 53, 3), (83, 5, 3, 3), (89, 29, 3, 3), (97, 29, 3, 3)] = true := by decide +kernel
theorem c79198d1_gens : allOn 1 0 1 (-60) 110 [(7, 3, 1), (0, 10, 1), (14, 38, 1)] = true := by decide +kernel

-- 79317b1: 19 primes
set_option maxHeartbeats 0 in
theorem c79317b1_cert0 : certAll 0 0 1 (-129) 1120 [(5, 11, 2, 23), (11, 2, 19, 13), (13, 5, 2, 5), (17, 5, 2, 5), (19, 2, 11, 5), (23, 2, 5, 5), (29, 5, 2, 11), (31, 2, 5, 5), (37, 11, 2, 5), (43, 2, 11, 5), (53, 11, 2, 5), (61, 5, 2, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c79317b1_cert1 : certAll 0 0 1 (-129) 1120 [(67, 2, 5, 5), (71, 2, 5, 5), (73, 5, 2, 5), (79, 2, 17, 5), (83, 2, 11, 5), (89, 17, 2, 5), (97, 17, 2, 5)] = true := by decide +kernel
theorem c79317b1_gens : allOn 0 0 1 (-129) 1120 [(22, 94, 1), (1, 31, 1), ((-5), 40, 1)] = true := by decide +kernel

-- 79555a1: 21 primes
set_option maxHeartbeats 0 in
theorem c79555a1_cert0 : certAll 1 0 0 (-361) 2610 [(11, 13, 2, 2), (13, 2, 19, 2), (17, 2, 3, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 13, 2), (37, 3, 2, 2), (41, 2, 3, 2), (43, 17, 2, 2), (47, 2, 11, 2), (53, 3, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c79555a1_cert1 : certAll 1 0 0 (-361) 2610 [(59, 2, 3, 2), (61, 2, 11, 2), (67, 11, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (83, 2, 3, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c79555a1_gens : allOn 1 0 0 (-361) 2610 [(11, (-6), 1), (13, 6, 1), (10, 0, 1)] = true := by decide +kernel

-- 79675b1: 19 primes
set_option maxHeartbeats 0 in
theorem c79675b1_cert0 : certAll 1 0 0 12 67 [(7, 3, 43, 3), (11, 7, 2, 2), (13, 2, 7, 2), (17, 2, 3, 2), (19, 2, 3, 2), (31, 2, 7, 2), (37, 3, 2, 2), (41, 2, 3, 2), (43, 11, 2, 2), (47, 2, 11, 2), (53, 3, 2, 2), (59, 2, 3, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c79675b1_cert1 : certAll 1 0 0 12 67 [(61, 2, 7, 2), (67, 11, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c79675b1_gens : allOn 1 0 0 12 67 [((-3), 4, 1), (2, 9, 1), ((-2), 7, 1)] = true := by decide +kernel

-- 79934b1: 21 primes
set_option maxHeartbeats 0 in
theorem c79934b1_cert0 : certAll 1 1 0 (-59) 169 [(5, 11, 3, 23), (7, 3, 23, 3), (11, 13, 7, 7), (13, 3, 37, 3), (19, 3, 41, 3), (23, 13, 3, 3), (29, 3, 11, 3), (31, 7, 3, 3), (37, 7, 3, 3), (41, 3, 13, 3), (43, 3, 7, 3), (47, 11, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c79934b1_cert1 : certAll 1 1 0 (-59) 169 [(53, 7, 3, 3), (59, 7, 3, 3), (67, 7, 3, 3), (71, 7, 3, 3), (73, 3, 7, 3), (79, 3, 11, 3), (83, 3, 7, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c79934b1_gens : allOn 1 1 0 (-59) 169 [(8, 13, 1), ((-9), 13, 1), (30, 19, 8)] = true := by decide +kernel

-- 80212b1: 21 primes
set_option maxHeartbeats 0 in
theorem c80212b1_cert0 : certAll 0 (-1) 0 (-30) 121 [(5, 7, 3, 7), (7, 3, 13, 3), (13, 3, 5, 3), (17, 3, 5, 3), (19, 3, 7, 3), (23, 5, 3, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 17, 3, 3), (41, 3, 5, 3), (43, 3, 7, 3), (47, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c80212b1_cert1 : certAll 0 (-1) 0 (-30) 121 [(53, 7, 3, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 7, 3), (83, 3, 23, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c80212b1_gens : allOn 0 (-1) 0 (-30) 121 [(6, 11, 1), ((-5), 11, 1), (28, 143, 1)] = true := by decide +kernel

-- 80222a1: 21 primes
set_option maxHeartbeats 0 in
theorem c80222a1_cert0 : certAll 1 (-1) 0 (-16) (-12) [(5, 17, 13, 17), (7, 5, 37, 5), (11, 7, 43, 13), (13, 5, 7, 5), (17, 5, 11, 5), (23, 7, 5, 5), (29, 5, 11, 7), (31, 11, 5, 5), (37, 11, 5, 5), (43, 5, 7, 5), (47, 7, 5, 5), (53, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c80222a1_cert1 : certAll 1 (-1) 0 (-16) (-12) [(59, 7, 5, 5), (61, 5, 7, 5), (67, 11, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 17, 5, 5)] = true := by decide +kernel
theorem c80222a1_gens : allOn 1 (-1) 0 (-16) (-12) [((-2), 4, 1), ((-1), 2, 1), ((-3), 3, 1)] = true := by decide +kernel

-- 80256a1: 20 primes
set_option maxHeartbeats 0 in
theorem c80256a1_cert0 : certAll 0 (-1) 0 (-835) 9571 [(5, 7, 13, 7), (7, 5, 23, 5), (13, 17, 5, 5), (17, 7, 5, 5), (23, 5, 31, 5), (29, 7, 5, 5), (31, 5, 7, 5), (41, 7, 5, 7), (43, 5, 7, 5), (47, 5, 23, 5), (53, 7, 5, 5), (59, 5, 17, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c80256a1_cert1 : certAll 0 (-1) 0 (-835) 9571 [(61, 17, 5, 5), (67, 5, 7, 5), (71, 5, 29, 5), (73, 29, 5, 5), (79, 5, 7, 5), (83, 5, 17, 5), (89, 7, 5, 5), (97, 23, 5, 5)] = true := by decide +kernel
theorem c80256a1_gens : allOn 0 (-1) 0 (-835) 9571 [(18, 7, 1), (9, 52, 1), (26, 69, 1), (17, 0, 1)] = true := by decide +kernel

-- 80351d1: 21 primes
set_option maxHeartbeats 0 in
theorem c80351d1_cert0 : certAll 1 (-1) 1 51 204 [(5, 2, 7, 2), (7, 5, 3, 3), (11, 3, 2, 2), (13, 2, 3, 2), (17, 2, 7, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (41, 2, 13, 2), (43, 5, 2, 2), (47, 2, 5, 2), (53, 3, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c80351d1_cert1 : certAll 1 (-1) 1 51 204 [(59, 2, 5, 2), (61, 2, 3, 2), (67, 7, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 5, 2, 2), (83, 2, 7, 2), (89, 2, 5, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c80351d1_gens : allOn 1 (-1) 1 51 204 [((-2), 10, 1), (36, 200, 1), (1, 15, 1)] = true := by decide +kernel

-- 80559b1: 19 primes
set_option maxHeartbeats 0 in
theorem c80559b1_cert0 : certAll 1 (-1) 1 (-86) 240 [(5, 2, 7, 2), (7, 5, 11, 5), (11, 5, 2, 2), (13, 2, 5, 2), (17, 2, 5, 2), (19, 2, 11, 2), (23, 5, 2, 2), (29, 7, 2, 2), (31, 2, 23, 2), (37, 7, 2, 2), (41, 2, 5, 2), (43, 5, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c80559b1_cert1 : certAll 1 (-1) 1 (-86) 240 [(53, 7, 2, 2), (61, 2, 5, 2), (73, 2, 5, 2), (79, 5, 2, 2), (83, 2, 7, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c80559b1_gens : allOn 1 (-1) 1 (-86) 240 [(8, 0, 1), ((-1), 18, 1), ((-10), 9, 1)] = true := by decide +kernel

-- 80615d1: 20 primes
set_option maxHeartbeats 0 in
theorem c80615d1_cert0 : certAll 0 1 1 (-2620) 50624 [(7, 2, 11, 3), (11, 2, 3, 13), (13, 3, 2, 3), (17, 7, 2, 3), (19, 2, 3, 3), (29, 3, 2, 3), (31, 2, 7, 3), (37, 3, 2, 3), (41, 7, 2, 3), (43, 2, 3, 3), (47, 2, 11, 3), (53, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c80615d1_cert1 : certAll 0 1 1 (-2620) 50624 [(59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 17, 3), (73, 11, 2, 3), (79, 2, 7, 3), (89, 7, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c80615d1_gens : allOn 0 1 1 (-2620) 50624 [(56, 287, 1), (218, 111, 8), (822, 44, 27)] = true := by decide +kernel

-- 80674a1: 20 primes
set_option maxHeartbeats 0 in
theorem c80674a1_cert0 : certAll 1 1 0 (-10697) 420565 [(5, 7, 3, 7), (7, 3, 43, 3), (13, 3, 5, 3), (17, 3, 5, 3), (23, 5, 3, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 13, 3, 3), (41, 3, 5, 3), (43, 3, 7, 3), (47, 5, 3, 3), (53, 7, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c80674a1_cert1 : certAll 1 1 0 (-10697) 420565 [(59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (73, 3, 5, 3), (79, 3, 7, 3), (83, 3, 13, 3), (89, 7, 3, 3), (97, 23, 3, 3)] = true := by decide +kernel
theorem c80674a1_gens : allOn 1 1 0 (-10697) 420565 [(95, 475, 1), ((-114), 475, 1), (62, (-9), 1)] = true := by decide +kernel

-- 80721b1: 22 primes
set_option maxHeartbeats 0 in
theorem c80721b1_cert0 : certAll 1 (-1) 1 (-113) 618 [(5, 2, 37, 2), (7, 11, 5, 5), (11, 7, 2, 2), (13, 2, 7, 2), (17, 2, 5, 2), (19, 2, 7, 2), (29, 5, 2, 2), (31, 2, 7, 2), (37, 5, 2, 2), (41, 2, 11, 2), (43, 19, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c80721b1_cert1 : certAll 1 (-1) 1 (-113) 618 [(53, 5, 2, 2), (59, 2, 11, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 5, 2, 2), (73, 2, 5, 2), (79, 5, 2, 2), (83, 2, 5, 2), (89, 2, 11, 2), (97, 2, 7, 2)] = true := by decide +kernel
theorem c80721b1_gens : allOn 1 (-1) 1 (-113) 618 [(8, 9, 1), ((-1), 27, 1), (26, 108, 1)] = true := by decide +kernel

-- 80913a1: 20 primes
set_option maxHeartbeats 0 in
theorem c80913a1_cert0 : certAll 0 (-1) 1 (-140) 512 [(5, 13, 2, 13), (11, 2, 17, 17), (13, 11, 2, 5), (17, 13, 2, 5), (19, 2, 13, 5), (23, 2, 11, 5), (29, 11, 2, 5), (31, 2, 13, 5), (37, 11, 2, 5), (41, 11, 2, 11), (43, 2, 11, 5), (47, 2, 11, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c80913a1_cert1 : certAll 0 (-1) 1 (-140) 512 [(53, 11, 2, 5), (59, 2, 17, 5), (67, 2, 13, 5), (73, 19, 2, 5), (79, 2, 13, 5), (83, 2, 11, 5), (89, 11, 2, 5), (97, 11, 2, 5)] = true := by decide +kernel
theorem c80913a1_gens : allOn 0 (-1) 1 (-140) 512 [((-4), 31, 1), (3, 10, 1), (17, 52, 1)] = true := by decide +kernel

-- 80965a1: 21 primes
set_option maxHeartbeats 0 in
theorem c80965a1_cert0 : certAll 0 0 1 (-13) (-12) [(7, 2, 3, 3), (11, 2, 7, 3), (13, 7, 2, 3), (17, 3, 2, 3), (19, 2, 3, 3), (23, 2, 19, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 7, 2, 3), (41, 3, 2, 3), (43, 2, 3, 3), (53, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c80965a1_cert1 : certAll 0 0 1 (-13) (-12) [(59, 2, 7, 3), (61, 7, 2, 3), (67, 2, 3, 3), (71, 2, 11, 3), (73, 19, 2, 3), (79, 2, 3, 3), (83, 2, 7, 3), (89, 3, 2, 3), (97, 19, 2, 3)] = true := by decide +kernel
theorem c80965a1_gens : allOn 0 0 1 (-13) (-12) [((-1), 0, 1), ((-2), 2, 1), ((-3), 0, 1)] = true := by decide +kernel

-- 81063c1: 23 primes
set_option maxHeartbeats 0 in
theorem c81063c1_cert0 : certAll 0 0 1 (-111) 396 [(5, 17, 2, 17), (7, 2, 11, 5), (11, 2, 7, 5), (13, 7, 2, 5), (17, 23, 2, 5), (19, 2, 17, 13), (23, 2, 7, 5), (29, 7, 2, 5), (31, 2, 19, 5), (37, 7, 2, 5), (41, 7, 2, 5), (43, 2, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c81063c1_cert1 : certAll 0 0 1 (-111) 396 [(47, 2, 7, 5), (53, 7, 2, 5), (59, 2, 17, 5), (61, 17, 2, 5), (67, 2, 23, 5), (71, 2, 17, 5), (73, 19, 2, 5), (79, 2, 19, 5), (83, 2, 7, 5), (89, 7, 2, 5), (97, 7, 2, 5)] = true := by decide +kernel
theorem c81063c1_gens : allOn 0 0 1 (-111) 396 [(8, 4, 1), ((-1), 22, 1), (11, 22, 1)] = true := by decide +kernel

-- 81162c1: 22 primes
set_option maxHeartbeats 0 in
theorem c81162c1_cert0 : certAll 1 (-1) 0 (-96) 368 [(5, 11, 7, 17), (7, 5, 19, 5), (11, 13, 7, 7), (13, 5, 19, 5), (17, 5, 7, 5), (19, 5, 11, 5), (29, 5, 13, 7), (31, 7, 5, 5), (37, 7, 5, 5), (41, 5, 11, 5), (43, 5, 7, 5), (47, 11, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c81162c1_cert1 : certAll 1 (-1) 0 (-96) 368 [(53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (67, 7, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 19, 5), (83, 5, 7, 5), (89, 7, 5, 5), (97, 7, 5, 5)] = true := by decide +kernel
theorem c81162c1_gens : allOn 1 (-1) 0 (-96) 368 [(4, 4, 1), (7, (-2), 1), (8, 4, 1)] = true := by decide +kernel

-- 81234h1: 21 primes
set_option maxHeartbeats 0 in
theorem c81234h1_cert0 : certAll 1 (-1) 0 (-198) 1080 [(5, 17, 13, 17), (7, 5, 17, 5), (11, 5, 17, 5), (13, 53, 5, 5), (17, 7, 5, 5), (19, 5, 7, 7), (23, 5, 53, 5), (29, 7, 5, 5), (37, 11, 5, 5), (41, 7, 5, 5), (43, 5, 7, 5), (47, 5, 11, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c81234h1_cert1 : certAll 1 (-1) 0 (-198) 1080 [(53, 7, 5, 5), (59, 5, 17, 5), (61, 11, 5, 5), (67, 5, 7, 5), (71, 5, 11, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 17, 5, 5)] = true := by decide +kernel
theorem c81234h1_gens : allOn 1 (-1) 0 (-198) 1080 [(12, 12, 1), (6, 6, 1), ((-6), 48, 1)] = true := by decide +kernel

-- 81328c1: 19 primes
set_option maxHeartbeats 0 in
theorem c81328c1_cert0 : certAll 0 1 0 96 196 [(5, 3, 73, 3), (7, 3, 19, 3), (11, 5, 3, 5), (19, 5, 3, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (43, 5, 3, 3), (47, 3, 29, 3), (53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c81328c1_cert1 : certAll 0 1 0 96 196 [(67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c81328c1_gens : allOn 0 1 0 96 196 [(2, 20, 1), (6, 32, 1), ((-1), 10, 1), ((-2), 0, 1)] = true := by decide +kernel

-- 81494a1: 21 primes
set_option maxHeartbeats 0 in
theorem c81494a1_cert0 : certAll 1 1 0 (-254) (-716) [(5, 19, 3, 23), (11, 13, 23, 13), (13, 3, 11, 3), (19, 3, 11, 3), (23, 13, 3, 3), (29, 3, 13, 3), (31, 11, 3, 3), (37, 23, 3, 3), (41, 3, 11, 3), (43, 3, 19, 3), (47, 13, 3, 3), (53, 19, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c81494a1_cert1 : certAll 1 1 0 (-254) (-716) [(59, 13, 3, 3), (61, 3, 13, 3), (67, 11, 3, 3), (71, 11, 3, 3), (73, 3, 13, 3), (79, 3, 19, 3), (83, 3, 23, 3), (89, 19, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c81494a1_gens : allOn 1 1 0 (-254) (-716) [(36, 178, 1), ((-13), 31, 1), ((-204), 886, 27)] = true := by decide +kernel

-- 81524c1: 22 primes
set_option maxHeartbeats 0 in
theorem c81524c1_cert0 : certAll 0 (-1) 0 (-517) 4694 [(5, 19, 3, 23), (7, 3, 31, 3), (11, 13, 7, 7), (13, 3, 11, 3), (17, 3, 11, 3), (19, 3, 23, 3), (23, 7, 3, 3), (29, 3, 7, 3), (31, 11, 3, 3), (37, 7, 3, 3), (41, 3, 13, 3), (43, 3, 17, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c81524c1_cert1 : certAll 0 (-1) 0 (-517) 4694 [(47, 7, 3, 3), (53, 11, 3, 3), (59, 11, 3, 3), (61, 3, 13, 3), (67, 7, 3, 3), (71, 7, 3, 3), (73, 3, 7, 3), (79, 3, 7, 3), (83, 3, 7, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c81524c1_gens : allOn 0 (-1) 0 (-517) 4694 [((-7), 89, 1), (122, 89, 8), (345, 89, 27)] = true := by decide +kernel

-- 81939e1: 19 primes
set_option maxHeartbeats 0 in
theorem c81939e1_cert0 : certAll 0 (-1) 1 (-280) 2172 [(5, 23, 2, 23), (7, 2, 31, 5), (17, 31, 2, 5), (19, 2, 31, 5), (23, 2, 7, 5), (31, 2, 17, 5), (37, 7, 2, 5), (41, 7, 2, 7), (43, 2, 7, 5), (47, 2, 7, 5), (53, 7, 2, 5), (59, 2, 17, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c81939e1_cert1 : certAll 0 (-1) 1 (-280) 2172 [(61, 17, 2, 5), (67, 2, 17, 5), (71, 2, 19, 5), (73, 17, 2, 5), (79, 2, 17, 5), (89, 7, 2, 5), (97, 7, 2, 5)] = true := by decide +kernel
theorem c81939e1_gens : allOn 0 (-1) 1 (-280) 2172 [(21, 71, 1), ((-5), 58, 1), ((-18), 32, 1)] = true := by decide +kernel

-- 82093a1: 21 primes
set_option maxHeartbeats 0 in
theorem c82093a1_cert0 : certAll 1 1 1 (-45) 106 [(5, 2, 3, 2), (7, 3, 13, 3), (13, 2, 5, 2), (19, 2, 13, 2), (23, 5, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 7, 2, 2), (41, 2, 5, 2), (43, 3, 2, 2), (47, 2, 3, 2), (53, 13, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c82093a1_cert1 : certAll 1 1 1 (-45) 106 [(59, 2, 3, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 5, 2, 2), (73, 2, 5, 2), (79, 3, 2, 2), (83, 2, 7, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c82093a1_gens : allOn 1 1 1 (-45) 106 [(2, 4, 1), (13, 37, 1), (38, 21, 8)] = true := by decide +kernel

-- 82146a1: 22 primes
set_option maxHeartbeats 0 in
theorem c82146a1_cert0 : certAll 1 1 0 (-2169) 37989 [(5, 7, 13, 7), (7, 5, 19, 5), (13, 5, 7, 5), (17, 5, 13, 5), (19, 5, 7, 5), (23, 7, 5, 5), (29, 5, 13, 7), (31, 13, 5, 5), (37, 17, 5, 5), (41, 5, 13, 5), (43, 5, 7, 5), (47, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c82146a1_cert1 : certAll 1 1 0 (-2169) 37989 [(53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (67, 13, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 7, 5), (83, 5, 17, 5), (89, 7, 5, 5), (97, 23, 5, 5)] = true := by decide +kernel
theorem c82146a1_gens : allOn 1 1 0 (-2169) 37989 [(27, (-9), 1), (26, (-9), 1), (23, 19, 1)] = true := by decide +kernel

-- 82174c1: 22 primes
set_option maxHeartbeats 0 in
theorem c82174c1_cert0 : certAll 1 0 0 (-1705) 26841 [(5, 3, 7, 3), (7, 3, 29, 3), (11, 5, 3, 7), (13, 3, 5, 3), (17, 11, 3, 3), (19, 5, 3, 3), (29, 3, 5, 3), (31, 3, 37, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c82174c1_cert1 : certAll 1 0 0 (-1705) 26841 [(53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 3, 11, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c82174c1_gens : allOn 1 0 0 (-1705) 26841 [(26, 3, 1), ((-6), 195, 1), (34, 75, 1)] = true := by decide +kernel

-- 82288q1: 22 primes
set_option maxHeartbeats 0 in
theorem c82288q1_cert0 : certAll 0 0 0 (-419) 6306 [(5, 17, 7, 17), (7, 5, 11, 5), (11, 13, 7, 7), (13, 5, 19, 5), (17, 5, 7, 5), (19, 5, 13, 5), (23, 13, 5, 5), (29, 5, 17, 7), (31, 7, 5, 5), (41, 5, 19, 5), (43, 5, 7, 5), (47, 13, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c82288q1_cert1 : certAll 0 0 0 (-419) 6306 [(53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (67, 7, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 13, 5), (83, 5, 7, 5), (89, 7, 5, 5), (97, 7, 5, 5)] = true := by decide +kernel
theorem c82288q1_gens : allOn 0 0 0 (-419) 6306 [(113, 1184, 1), (17, 64, 1), ((-15), 96, 1)] = true := by decide +kernel

-- 82296i1: 20 primes
set_option maxHeartbeats 0 in
theorem c82296i1_cert0 : certAll 0 0 0 (-207) 1170 [(5, 7, 13, 7), (7, 5, 11, 5), (11, 5, 17, 7), (13, 11, 5, 5), (17, 7, 5, 5), (19, 5, 7, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 11, 5, 5), (41, 7, 5, 7), (47, 5, 11, 5), (53, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c82296i1_cert1 : certAll 0 0 0 (-207) 1170 [(59, 5, 17, 5), (61, 17, 5, 5), (67, 5, 7, 5), (71, 5, 19, 5), (73, 17, 5, 5), (79, 5, 7, 5), (83, 5, 11, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c82296i1_gens : allOn 0 0 0 (-207) 1170 [(9, 6, 1), (3, 24, 1), (7, 8, 1)] = true := by decide +kernel

-- 82480a1: 22 primes
set_option maxHeartbeats 0 in
theorem c82480a1_cert0 : certAll 0 1 0 (-136) 660 [(7, 3, 13, 3), (11, 7, 3, 7), (13, 3, 7, 3), (17, 7, 3, 3), (19, 23, 3, 3), (23, 3, 31, 3), (29, 3, 17, 3), (31, 3, 7, 3), (37, 3, 7, 3), (41, 7, 3, 3), (43, 17, 3, 3), (47, 3, 17, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c82480a1_cert1 : certAll 0 1 0 (-136) 660 [(53, 3, 17, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 47, 3, 3), (71, 3, 17, 3), (73, 17, 3, 3), (79, 3, 7, 3), (83, 7, 3, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c82480a1_gens : allOn 0 1 0 (-136) 660 [(2, 20, 1), (12, 30, 1), (7, 10, 1)] = true := by decide +kernel

-- 82538a1: 22 primes
set_option maxHeartbeats 0 in
theorem c82538a1_cert0 : certAll 1 1 0 (-18) 16 [(5, 7, 3, 7), (7, 3, 5, 3), (11, 7, 5, 7), (13, 3, 7, 3), (17, 3, 5, 3), (19, 3, 7, 3), (23, 7, 3, 3), (29, 3, 11, 3), (37, 5, 3, 3), (41, 3, 17, 3), (43, 3, 5, 3), (47, 7, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c82538a1_cert1 : certAll 1 1 0 (-18) 16 [(53, 5, 3, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 7, 3), (83, 3, 5, 3), (89, 5, 3, 3), (97, 5, 3, 3)] = true := by decide +kernel
theorem c82538a1_gens : allOn 1 1 0 (-18) 16 [(0, 4, 1), (1, 0, 1), ((-2), 8, 1)] = true := by decide +kernel

-- 82539e1: 21 primes
set_option maxHeartbeats 0 in
theorem c82539e1_cert0 : certAll 1 (-1) 1 (-11) 46 [(5, 2, 7, 2), (7, 5, 53, 5), (11, 5, 2, 2), (13, 2, 5, 2), (17, 2, 5, 2), (19, 2, 29, 2), (23, 5, 2, 2), (29, 17, 2, 2), (37, 7, 2, 2), (41, 2, 5, 2), (43, 5, 2, 2), (47, 2, 17, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c82539e1_cert1 : certAll 1 (-1) 1 (-11) 46 [(53, 17, 2, 2), (59, 2, 7, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 5, 2, 2), (73, 2, 5, 2), (79, 5, 2, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c82539e1_gens : allOn 1 (-1) 1 (-11) 46 [(1, 5, 1), (4, 5, 1), ((-2), 8, 1)] = true := by decide +kernel

-- 82547b1: 20 primes
set_option maxHeartbeats 0 in
theorem c82547b1_cert0 : certAll 0 0 1 (-1267) 17346 [(5, 3, 2, 3), (7, 2, 3, 3), (11, 2, 19, 3), (13, 43, 2, 3), (17, 3, 2, 3), (19, 2, 3, 3), (29, 3, 2, 3), (31, 2, 3, 3), (41, 3, 2, 3), (43, 2, 3, 3), (47, 2, 11, 3), (53, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c82547b1_cert1 : certAll 0 0 1 (-1267) 17346 [(59, 2, 19, 3), (61, 11, 2, 3), (67, 2, 3, 3), (71, 2, 11, 3), (73, 19, 2, 3), (79, 2, 3, 3), (83, 2, 11, 3), (89, 3, 2, 3)] = true := by decide +kernel
theorem c82547b1_gens : allOn 0 0 1 (-1267) 17346 [(14, 48, 1), (19, 11, 1), (42, 195, 1)] = true := by decide +kernel

-- 82701f1: 21 primes
set_option maxHeartbeats 0 in
theorem c82701f1_cert0 : certAll 0 0 1 (-1809) 29612 [(5, 47, 2, 47), (7, 2, 47, 5), (11, 2, 7, 7), (13, 5, 2, 5), (17, 5, 2, 5), (19, 2, 31, 5), (23, 2, 5, 5), (29, 5, 2, 7), (31, 2, 5, 5), (41, 5, 2, 5), (43, 2, 67, 5), (47, 2, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c82701f1_cert1 : certAll 0 0 1 (-1809) 29612 [(53, 11, 2, 5), (61, 5, 2, 5), (67, 2, 5, 5), (71, 2, 5, 5), (73, 5, 2, 5), (79, 2, 7, 5), (83, 2, 7, 5), (89, 7, 2, 5), (97, 19, 2, 5)] = true := by decide +kernel
theorem c82701f1_gens : allOn 0 0 1 (-1809) 29612 [(24, 4, 1), (15, 76, 1), (210, 113, 8)] = true := by decide +kernel

-- 82763a1: 22 primes
set_option maxHeartbeats 0 in
theorem c82763a1_cert0 : certAll 0 (-1) 1 (-10) 22 [(5, 17, 2, 17), (7, 2, 29, 3), (13, 3, 2, 3), (17, 3, 2, 3), (19, 2, 17, 3), (23, 2, 3, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 7, 2, 3), (41, 3, 2, 3), (43, 2, 17, 3), (47, 2, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c82763a1_cert1 : certAll 0 (-1) 1 (-10) 22 [(53, 17, 2, 3), (59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 3, 3), (73, 3, 2, 3), (79, 2, 7, 3), (83, 2, 7, 3), (89, 7, 2, 3), (97, 19, 2, 3)] = true := by decide +kernel
theorem c82763a1_gens : allOn 0 (-1) 1 (-10) 22 [(2, 2, 1), (1, 3, 1), (4, 5, 1)] = true := by decide +kernel

-- 82808c1: 19 primes
set_option maxHeartbeats 0 in
theorem c82808c1_cert0 : certAll 0 1 0 28 64 [(5, 3, 7, 3), (7, 3, 17, 3), (13, 3, 23, 3), (17, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 17, 3), (31, 3, 5, 3), (37, 3, 5, 3), (43, 5, 3, 3), (47, 3, 5, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c82808c1_cert1 : certAll 0 1 0 28 64 [(59, 7, 3, 3), (61, 3, 7, 3), (67, 7, 3, 3), (73, 5, 3, 3), (79, 3, 13, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c82808c1_gens : allOn 0 1 0 28 64 [((-2), 2, 1), (0, 8, 1), (6, 22, 1)] = true := by decide +kernel

-- 83016f1: 23 primes
set_option maxHeartbeats 0 in
theorem c83016f1_cert0 : certAll 0 0 0 (-39) 1226 [(5, 7, 17, 7), (7, 5, 29, 5), (11, 7, 31, 7), (13, 5, 7, 5), (17, 5, 11, 5), (19, 5, 7, 5), (23, 7, 5, 5), (29, 5, 17, 7), (31, 11, 5, 5), (37, 11, 5, 5), (41, 5, 11, 5), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c83016f1_cert1 : certAll 0 0 0 (-39) 1226 [(47, 7, 5, 5), (53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (67, 17, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 19, 5, 5)] = true := by decide +kernel
theorem c83016f1_gens : allOn 0 0 0 (-39) 1226 [((-11), 18, 1), (7, 36, 1), ((-5), 36, 1)] = true := by decide +kernel

-- 83105a1: 21 primes
set_option maxHeartbeats 0 in
theorem c83105a1_cert0 : certAll 1 0 0 (-3031) 64086 [(7, 3, 19, 3), (13, 2, 17, 2), (17, 2, 3, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 19, 2), (37, 3, 2, 2), (41, 2, 3, 2), (43, 13, 2, 2), (47, 2, 7, 2), (53, 3, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c83105a1_cert1 : certAll 1 0 0 (-3031) 64086 [(59, 2, 3, 2), (61, 2, 7, 2), (67, 7, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (83, 2, 3, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c83105a1_gens : allOn 1 0 0 (-3031) 64086 [(26, 42, 1), (59, 273, 1), (15, 141, 1)] = true := by decide +kernel

-- 83111c1: 20 primes
set_option maxHeartbeats 0 in
theorem c83111c1_cert0 : certAll 1 1 1 (-42) 670 [(5, 2, 3, 2), (11, 13, 2, 2), (13, 2, 23, 2), (17, 2, 11, 2), (19, 2, 17, 2), (23, 13, 2, 2), (29, 3, 2, 2), (37, 11, 2, 2), (41, 2, 13, 2), (43, 3, 2, 2), (47, 2, 3, 2), (53, 11, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c83111c1_cert1 : certAll 1 1 1 (-42) 670 [(59, 2, 3, 2), (67, 11, 2, 2), (71, 11, 2, 2), (73, 2, 11, 2), (79, 3, 2, 2), (83, 2, 11, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c83111c1_gens : allOn 1 1 1 (-42) 670 [(2, 23, 1), (16, 58, 1), (100, 954, 1)] = true := by decide +kernel

-- 83262a1: 23 primes
set_option maxHeartbeats 0 in
theorem c83262a1_cert0 : certAll 1 1 0 (-21) 9 [(5, 11, 7, 53), (7, 5, 19, 5), (11, 5, 7, 5), (13, 7, 5, 5), (17, 7, 5, 5), (19, 5, 11, 11), (23, 5, 29, 5), (29, 11, 5, 5), (31, 5, 7, 5), (37, 7, 5, 5), (41, 7, 5, 5), (43, 5, 11, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c83262a1_cert1 : certAll 1 1 0 (-21) 9 [(47, 5, 23, 5), (53, 11, 5, 5), (59, 5, 7, 5), (61, 7, 5, 5), (67, 5, 11, 5), (71, 5, 23, 5), (73, 23, 5, 5), (79, 5, 7, 5), (83, 5, 7, 5), (89, 7, 5, 5), (97, 29, 5, 5)] = true := by decide +kernel
theorem c83262a1_gens : allOn 1 1 0 (-21) 9 [(0, 3, 1), (6, 9, 1), ((-3), 9, 1)] = true := by decide +kernel

-- 83350a1: 22 primes
set_option maxHeartbeats 0 in
theorem c83350a1_cert0 : certAll 1 1 0 (-400) 2000 [(7, 3, 19, 3), (11, 7, 19, 7), (13, 3, 7, 3), (17, 3, 11, 3), (19, 3, 7, 3), (23, 7, 3, 3), (29, 3, 13, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 11, 3), (43, 3, 7, 3), (47, 7, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c83350a1_cert1 : certAll 1 1 0 (-400) 2000 [(53, 7, 3, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 13, 3, 3), (71, 7, 3, 3), (73, 3, 7, 3), (79, 3, 7, 3), (83, 3, 11, 3), (89, 7, 3, 3), (97, 19, 3, 3)] = true := by decide +kernel
theorem c83350a1_gens : allOn 1 1 0 (-400) 2000 [((-20), 60, 1), (5, 10, 1), ((-5), 65, 1)] = true := by decide +kernel

-- 83582g1: 21 primes
set_option maxHeartbeats 0 in
theorem c83582g1_cert0 : certAll 1 (-1) 0 430 1992 [(5, 7, 47, 7), (7, 17, 5, 5), (11, 7, 5, 7), (13, 5, 7, 5), (17, 7, 5, 5), (19, 11, 7, 7), (29, 5, 11, 5), (31, 5, 7, 5), (37, 5, 7, 5), (41, 5, 17, 5), (43, 19, 5, 5), (47, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c83582g1_cert1 : certAll 1 (-1) 0 430 1992 [(53, 5, 11, 5), (59, 5, 17, 5), (61, 11, 5, 5), (67, 5, 7, 5), (71, 5, 11, 5), (73, 11, 5, 5), (83, 7, 5, 5), (89, 5, 17, 5), (97, 5, 7, 5)] = true := by decide +kernel
theorem c83582g1_gens : allOn 1 (-1) 0 430 1992 [(6, 66, 1), (236, 3516, 1), (29, 181, 1)] = true := by decide +kernel

-- 83718d1: 21 primes
set_option maxHeartbeats 0 in
theorem c83718d1_cert0 : certAll 1 (-1) 0 (-216) 1156 [(5, 7, 23, 7), (7, 5, 11, 5), (11, 7, 19, 7), (13, 5, 7, 5), (19, 5, 7, 5), (23, 7, 5, 5), (29, 5, 37, 7), (31, 11, 5, 5), (37, 11, 5, 5), (41, 5, 19, 5), (43, 5, 7, 5), (47, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c83718d1_cert1 : certAll 1 (-1) 0 (-216) 1156 [(53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c83718d1_gens : allOn 1 (-1) 0 (-216) 1156 [(14, 20, 1), (5, 11, 1), (11, (-1), 1)] = true := by decide +kernel

-- 83798c1: 17 primes
set_option maxHeartbeats 0 in
theorem c83798c1_cert0 : certAll 1 (-1) 1 (-972) 12495 [(5, 3, 23, 3), (7, 5, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 29, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 17, 3, 3), (43, 5, 3, 3), (47, 3, 23, 3), (53, 3, 5, 3), (61, 17, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c83798c1_cert1 : certAll 1 (-1) 1 (-972) 12495 [(67, 5, 3, 3), (71, 3, 23, 3), (73, 23, 3, 3), (83, 3, 17, 3), (97, 29, 3, 3)] = true := by decide +kernel
theorem c83798c1_gens : allOn 1 (-1) 1 (-972) 12495 [(13, 37, 1), ((-9), 147, 1), (615, 823, 27)] = true := by decide +kernel

-- 83806a1: 19 primes
set_option maxHeartbeats 0 in
theorem c83806a1_cert0 : certAll 1 0 1 (-52) 114 [(5, 3, 7, 3), (7, 3, 13, 3), (13, 3, 5, 3), (17, 13, 3, 3), (19, 5, 3, 3), (23, 3, 7, 3), (31, 3, 13, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 7, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c83806a1_cert1 : certAll 1 0 1 (-52) 114 [(61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 17, 3), (73, 17, 3, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c83806a1_gens : allOn 1 0 1 (-52) 114 [(1, 7, 1), (9, 15, 1), ((-7), 15, 1)] = true := by decide +kernel

-- 83876a1: 21 primes
set_option maxHeartbeats 0 in
theorem c83876a1_cert0 : certAll 0 1 0 (-125) 319 [(5, 3, 7, 3), (7, 3, 17, 3), (11, 5, 3, 7), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 19, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c83876a1_cert1 : certAll 0 1 0 (-125) 319 [(59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 17, 3), (73, 17, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c83876a1_gens : allOn 0 1 0 (-125) 319 [((-3), 26, 1), (10, 13, 1), (49, 338, 1)] = true := by decide +kernel

-- 83928b1: 22 primes
set_option maxHeartbeats 0 in
theorem c83928b1_cert0 : certAll 0 (-1) 0 (-577) 5509 [(5, 7, 17, 7), (7, 5, 11, 5), (11, 7, 19, 7), (17, 5, 11, 5), (19, 5, 7, 5), (23, 7, 5, 5), (29, 5, 17, 7), (31, 11, 5, 5), (37, 11, 5, 5), (41, 5, 17, 5), (43, 5, 7, 5), (47, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c83928b1_cert1 : certAll 0 (-1) 0 (-577) 5509 [(53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (67, 11, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c83928b1_gens : allOn 0 (-1) 0 (-577) 5509 [(25, 78, 1), (13, 6, 1), (7, 42, 1)] = true := by decide +kernel

-- 84176a1: 20 primes
set_option maxHeartbeats 0 in
theorem c84176a1_cert0 : certAll 0 0 0 (-59) (-134) [(5, 13, 7, 13), (7, 5, 11, 5), (11, 19, 7, 7), (13, 5, 23, 5), (17, 5, 7, 5), (19, 5, 17, 5), (23, 17, 5, 5), (29, 5, 31, 7), (31, 7, 5, 5), (37, 7, 5, 5), (41, 5, 13, 5), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c84176a1_cert1 : certAll 0 0 0 (-59) (-134) [(47, 17, 5, 5), (61, 5, 7, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 13, 5), (83, 5, 7, 5), (89, 7, 5, 5), (97, 7, 5, 5)] = true := by decide +kernel
theorem c84176a1_gens : allOn 0 0 0 (-59) (-134) [((-3), 4, 1), ((-5), 6, 1), (13, 36, 1)] = true := by decide +kernel

-- 84341a1: 19 primes
set_option maxHeartbeats 0 in
theorem c84341a1_cert0 : certAll 1 1 1 (-58) 132 [(7, 3, 13, 3), (11, 7, 2, 2), (13, 2, 7, 2), (17, 2, 59, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 17, 2, 2), (41, 2, 17, 2), (47, 2, 3, 2), (53, 7, 2, 2), (59, 2, 3, 2), (61, 2, 7, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c84341a1_cert1 : certAll 1 1 1 (-58) 132 [(67, 29, 2, 2), (71, 7, 2, 2), (73, 2, 7, 2), (79, 3, 2, 2), (83, 2, 17, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c84341a1_gens : allOn 1 1 1 (-58) 132 [(0, 11, 1), (46, 19, 8), ((-3), 18, 1)] = true := by decide +kernel

-- 84470b1: 22 primes
set_option maxHeartbeats 0 in
theorem c84470b1_cert0 : certAll 1 0 1 (-48) 506 [(7, 3, 11, 3), (11, 7, 3, 7), (13, 3, 7, 3), (17, 7, 3, 3), (19, 13, 3, 3), (23, 3, 11, 3), (29, 3, 13, 3), (31, 3, 7, 3), (37, 3, 7, 3), (41, 7, 3, 3), (43, 13, 3, 3), (47, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c84470b1_cert1 : certAll 1 0 1 (-48) 506 [(53, 3, 13, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 11, 3, 3), (71, 3, 23, 3), (73, 23, 3, 3), (79, 3, 7, 3), (83, 7, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c84470b1_gens : allOn 1 0 1 (-48) 506 [((-5), 27, 1), (5, 17, 1), ((-10), 7, 1)] = true := by decide +kernel

-- 84534a1: 20 primes
set_option maxHeartbeats 0 in
theorem c84534a1_cert0 : certAll 1 1 0 (-301) 1885 [(5, 11, 7, 17), (7, 5, 29, 5), (11, 5, 7, 5), (13, 7, 5, 5), (17, 7, 5, 5), (19, 5, 17, 11), (23, 5, 11, 5), (29, 17, 5, 5), (31, 5, 7, 5), (37, 7, 5, 5), (43, 5, 11, 5), (53, 17, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c84534a1_cert1 : certAll 1 1 0 (-301) 1885 [(59, 5, 7, 5), (61, 7, 5, 5), (67, 5, 11, 5), (71, 5, 11, 5), (79, 5, 7, 5), (83, 5, 7, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c84534a1_gens : allOn 1 1 0 (-301) 1885 [(2, 35, 1), (9, (-2), 1), (11, 2, 1), (10, (-5), 1)] = true := by decide +kernel

-- 84650g1: 20 primes
set_option maxHeartbeats 0 in
theorem c84650g1_cert0 : certAll 1 (-1) 0 (-67) (-59) [(7, 11, 3, 3), (11, 3, 23, 3), (13, 11, 3, 3), (17, 3, 11, 3), (23, 3, 29, 3), (29, 3, 17, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 11, 3), (43, 17, 3, 3), (47, 3, 23, 3), (53, 3, 17, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c84650g1_cert1 : certAll 1 (-1) 0 (-67) (-59) [(59, 3, 11, 3), (61, 11, 3, 3), (67, 17, 3, 3), (71, 3, 37, 3), (73, 29, 3, 3), (79, 11, 3, 3), (89, 3, 11, 3), (97, 23, 3, 3)] = true := by decide +kernel
theorem c84650g1_gens : allOn 1 (-1) 0 (-67) (-59) [((-6), 13, 1), ((-1), 3, 1), ((-2), 9, 1)] = true := by decide +kernel

-- 84746a1: 20 primes
set_option maxHeartbeats 0 in
theorem c84746a1_cert0 : certAll 1 0 0 (-1260) 17296 [(5, 3, 7, 3), (7, 3, 23, 3), (11, 5, 3, 7), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c84746a1_cert1 : certAll 1 0 0 (-1260) 17296 [(47, 3, 17, 3), (53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (73, 11, 3, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c84746a1_gens : allOn 1 0 0 (-1260) 17296 [(24, 20, 1), (16, 28, 1), (20, 4, 1)] = true := by decide +kernel

-- 85174a1: 20 primes
set_option maxHeartbeats 0 in
theorem c85174a1_cert0 : certAll 1 0 1 (-56) 6 [(7, 3, 11, 3), (11, 7, 3, 7), (13, 3, 7, 3), (17, 7, 3, 3), (19, 29, 3, 3), (23, 3, 11, 3), (29, 3, 17, 3), (31, 3, 7, 3), (43, 11, 3, 3), (47, 3, 11, 3), (53, 3, 11, 3), (59, 7, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c85174a1_cert1 : certAll 1 0 1 (-56) 6 [(61, 3, 7, 3), (67, 11, 3, 3), (71, 3, 17, 3), (73, 11, 3, 3), (79, 3, 7, 3), (83, 7, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c85174a1_gens : allOn 1 0 1 (-56) 6 [((-7), 11, 1), (9, 11, 1), (25, 107, 1)] = true := by decide +kernel

-- 85222a1: 21 primes
set_option maxHeartbeats 0 in
theorem c85222a1_cert0 : certAll 1 0 1 (-40) 90 [(5, 3, 13, 3), (7, 3, 11, 3), (11, 7, 3, 7), (13, 3, 7, 3), (17, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 13, 3), (31, 3, 5, 3), (37, 3, 5, 3), (43, 5, 3, 3), (47, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c85222a1_cert1 : certAll 1 0 1 (-40) 90 [(53, 3, 5, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 11, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 7, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c85222a1_gens : allOn 1 0 1 (-40) 90 [(3, (-3), 1), (4, (-2), 1), (2, 3, 1)] = true := by decide +kernel

-- 85295a1: 21 primes
set_option maxHeartbeats 0 in
theorem c85295a1_cert0 : certAll 1 0 0 (-81) 286 [(11, 13, 2, 2), (13, 2, 23, 2), (17, 2, 3, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 17, 2), (37, 3, 2, 2), (41, 2, 3, 2), (43, 13, 2, 2), (47, 2, 17, 2), (53, 3, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c85295a1_cert1 : certAll 1 0 0 (-81) 286 [(59, 2, 3, 2), (61, 2, 13, 2), (67, 13, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (83, 2, 3, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c85295a1_gens : allOn 1 0 0 (-81) 286 [(5, 1, 1), ((-9), 22, 1), ((-2), 22, 1)] = true := by decide +kernel

-- 85318e1: 22 primes
set_option maxHeartbeats 0 in
theorem c85318e1_cert0 : certAll 1 (-1) 1 (-282) 345 [(5, 3, 7, 3), (7, 5, 3, 3), (11, 3, 7, 3), (13, 7, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 7, 3), (31, 5, 3, 3), (37, 7, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3), (47, 3, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c85318e1_cert1 : certAll 1 (-1) 1 (-282) 345 [(53, 3, 5, 3), (59, 3, 11, 3), (61, 11, 3, 3), (67, 5, 3, 3), (71, 3, 17, 3), (73, 17, 3, 3), (79, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c85318e1_gens : allOn 1 (-1) 1 (-282) 345 [((-15), 39, 1), (1, 7, 1), ((-7), 47, 1)] = true := by decide +kernel

-- 85863a1: 20 primes
set_option maxHeartbeats 0 in
theorem c85863a1_cert0 : certAll 0 (-1) 1 (-232) 1440 [(5, 19, 2, 23), (7, 2, 11, 5), (11, 2, 7, 7), (13, 5, 2, 5), (19, 2, 11, 5), (23, 2, 5, 5), (29, 5, 2, 7), (31, 2, 5, 5), (37, 7, 2, 5), (43, 2, 19, 5), (47, 2, 5, 5), (53, 19, 2, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c85863a1_cert1 : certAll 0 (-1) 1 (-232) 1440 [(61, 5, 2, 5), (67, 2, 5, 5), (71, 2, 5, 5), (73, 5, 2, 5), (79, 2, 7, 5), (83, 2, 7, 5), (89, 7, 2, 5), (97, 11, 2, 5)] = true := by decide +kernel
theorem c85863a1_gens : allOn 0 (-1) 1 (-232) 1440 [(10, 4, 1), (9, 0, 1), (74, (-1), 8)] = true := by decide +kernel

-- 85970a1: 21 primes
set_option maxHeartbeats 0 in
theorem c85970a1_cert0 : certAll 1 0 1 (-164) 786 [(7, 3, 11, 3), (11, 13, 3, 7), (13, 3, 11, 3), (17, 11, 3, 3), (19, 13, 3, 3), (23, 3, 7, 3), (29, 3, 13, 3), (31, 3, 19, 3), (37, 3, 11, 3), (41, 7, 3, 3), (43, 11, 3, 3), (53, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c85970a1_cert1 : certAll 1 0 1 (-164) 786 [(59, 7, 3, 3), (61, 3, 7, 3), (67, 7, 3, 3), (71, 3, 29, 3), (73, 11, 3, 3), (79, 3, 19, 3), (83, 11, 3, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c85970a1_gens : allOn 1 0 1 (-164) 786 [(8, (-7), 1), (13, 23, 1), (5, 7, 1)] = true := by decide +kernel

-- 86007a1: 22 primes
set_option maxHeartbeats 0 in
theorem c86007a1_cert0 : certAll 1 1 1 (-82) 242 [(5, 2, 23, 2), (7, 5, 31, 5), (11, 7, 2, 2), (13, 2, 7, 2), (19, 2, 7, 2), (23, 7, 2, 2), (29, 5, 2, 2), (31, 2, 5, 2), (37, 11, 2, 2), (41, 2, 13, 2), (43, 5, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c86007a1_cert1 : certAll 1 1 1 (-82) 242 [(53, 7, 2, 2), (59, 2, 5, 2), (61, 2, 7, 2), (67, 11, 2, 2), (71, 7, 2, 2), (73, 2, 7, 2), (79, 5, 2, 2), (83, 2, 11, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c86007a1_gens : allOn 1 1 1 (-82) 242 [(8, 9, 1), ((-1), 18, 1), ((-10), 18, 1)] = true := by decide +kernel

-- 86321a1: 21 primes
set_option maxHeartbeats 0 in
theorem c86321a1_cert0 : certAll 1 0 0 (-36) 79 [(5, 2, 53, 2), (7, 3, 5, 3), (11, 7, 2, 2), (13, 2, 7, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 7, 2), (41, 2, 3, 2), (43, 29, 2, 2), (47, 2, 5, 2), (53, 3, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c86321a1_cert1 : certAll 1 0 0 (-36) 79 [(59, 2, 3, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (83, 2, 3, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c86321a1_gens : allOn 1 0 0 (-36) 79 [(3, (-2), 1), (2, 3, 1), (5, 3, 1)] = true := by decide +kernel

-- 86487a1: 20 primes
set_option maxHeartbeats 0 in
theorem c86487a1_cert0 : certAll 0 (-1) 1 (-198) 2774 [(7, 2, 11, 13), (11, 2, 29, 13), (13, 11, 2, 7), (19, 2, 7, 7), (23, 2, 11, 7), (29, 7, 2, 7), (31, 2, 7, 7), (37, 11, 2, 7), (41, 7, 2, 7), (43, 2, 7, 7), (53, 7, 2, 7), (59, 2, 23, 7)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c86487a1_cert1 : certAll 0 (-1) 1 (-198) 2774 [(61, 23, 2, 7), (67, 2, 7, 7), (71, 2, 23, 7), (73, 23, 2, 7), (79, 2, 7, 7), (83, 2, 11, 7), (89, 7, 2, 7), (97, 11, 2, 7)] = true := by decide +kernel
theorem c86487a1_gens : allOn 0 (-1) 1 (-198) 2774 [(17, 63, 1), (144, 1714, 1), ((-18), 13, 1)] = true := by decide +kernel

-- 86534e1: 19 primes
set_option maxHeartbeats 0 in
theorem c86534e1_cert0 : certAll 1 0 1 (-110) 480 [(5, 3, 13, 3), (11, 13, 3, 13), (13, 3, 11, 3), (17, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 11, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3), (47, 3, 5, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c86534e1_cert1 : certAll 1 0 1 (-110) 480 [(59, 11, 3, 3), (61, 3, 13, 3), (67, 11, 3, 3), (73, 5, 3, 3), (83, 5, 3, 3), (89, 11, 3, 3), (97, 19, 3, 3)] = true := by decide +kernel
theorem c86534e1_gens : allOn 1 0 1 (-110) 480 [((-3), 29, 1), (5, 5, 1), (13, 29, 1)] = true := by decide +kernel

-- 86611a1: 21 primes
set_option maxHeartbeats 0 in
theorem c86611a1_cert0 : certAll 0 0 1 (-157) 756 [(5, 3, 2, 3), (13, 17, 2, 3), (17, 3, 2, 3), (19, 2, 3, 3), (23, 2, 29, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 17, 2, 3), (41, 3, 2, 3), (43, 2, 3, 3), (47, 2, 23, 3), (53, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c86611a1_cert1 : certAll 0 0 1 (-157) 756 [(59, 2, 17, 3), (61, 17, 2, 3), (67, 2, 3, 3), (71, 2, 29, 3), (73, 29, 2, 3), (79, 2, 3, 3), (83, 2, 17, 3), (89, 3, 2, 3), (97, 23, 2, 3)] = true := by decide +kernel
theorem c86611a1_gens : allOn 0 0 1 (-157) 756 [(8, 3, 1), (7, 0, 1), (6, 5, 1)] = true := by decide +kernel

-- 86786a1: 20 primes
set_option maxHeartbeats 0 in
theorem c86786a1_cert0 : certAll 1 0 1 (-45) 152 [(5, 3, 13, 3), (11, 13, 3, 13), (13, 3, 11, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 11, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3), (53, 3, 5, 3), (59, 11, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c86786a1_cert1 : certAll 1 0 1 (-45) 152 [(61, 3, 13, 3), (67, 11, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 11, 3), (83, 5, 3, 3), (89, 11, 3, 3), (97, 23, 3, 3)] = true := by decide +kernel
theorem c86786a1_gens : allOn 1 0 1 (-45) 152 [((-1), 14, 1), (6, 7, 1), ((-8), 7, 1)] = true := by decide +kernel

-- 86802i1: 20 primes
set_option maxHeartbeats 0 in
theorem c86802i1_cert0 : certAll 1 1 0 (-1334) 19044 [(5, 29, 13, 53), (7, 5, 41, 5), (11, 7, 19, 13), (13, 5, 7, 5), (19, 5, 7, 5), (29, 5, 11, 7), (31, 11, 5, 5), (41, 5, 13, 5), (43, 5, 7, 5), (47, 7, 5, 5), (53, 7, 5, 5), (59, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c86802i1_cert1 : certAll 1 1 0 (-1334) 19044 [(61, 5, 7, 5), (67, 11, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 19, 5, 5)] = true := by decide +kernel
theorem c86802i1_gens : allOn 1 1 0 (-1334) 19044 [((-23), 207, 1), (28, 54, 1), (11, 71, 1)] = true := by decide +kernel

-- 86895f1: 21 primes
set_option maxHeartbeats 0 in
theorem c86895f1_cert0 : certAll 0 0 1 (-63) 344 [(7, 2, 23, 13), (11, 2, 23, 13), (13, 23, 2, 7), (17, 7, 2, 7), (19, 2, 7, 7), (23, 2, 37, 7), (29, 7, 2, 7), (37, 11, 2, 7), (41, 7, 2, 7), (43, 2, 7, 7), (47, 2, 11, 7), (53, 7, 2, 7)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c86895f1_cert1 : certAll 0 0 1 (-63) 344 [(59, 2, 23, 7), (61, 11, 2, 7), (67, 2, 7, 7), (71, 2, 11, 7), (73, 23, 2, 7), (79, 2, 7, 7), (83, 2, 11, 7), (89, 7, 2, 7), (97, 23, 2, 7)] = true := by decide +kernel
theorem c86895f1_gens : allOn 0 0 1 (-63) 344 [(9, 22, 1), ((-6), 22, 1), (3, 13, 1)] = true := by decide +kernel

-- 86903b1: 21 primes
set_option maxHeartbeats 0 in
theorem c86903b1_cert0 : certAll 0 1 1 115 (-390) [(5, 3, 17, 3), (7, 3, 17, 3), (11, 5, 3, 7), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 13, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c86903b1_cert1 : certAll 0 1 1 115 (-390) [(59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 13, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c86903b1_gens : allOn 0 1 1 115 (-390) [(6, 23, 1), (100, 1010, 1), (120, 395, 27)] = true := by decide +kernel

-- 87116c1: 21 primes
set_option maxHeartbeats 0 in
theorem c87116c1_cert0 : certAll 0 1 0 (-174) 841 [(5, 3, 13, 3), (7, 3, 23, 3), (11, 5, 3, 5), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 13, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 31, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c87116c1_cert1 : certAll 0 1 0 (-174) 841 [(53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 13, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 13, 3, 3)] = true := by decide +kernel
theorem c87116c1_gens : allOn 0 1 0 (-174) 841 [(0, 29, 1), (6, 7, 1), (58, 29, 8)] = true := by decide +kernel

-- 87130a1: 21 primes
set_option maxHeartbeats 0 in
theorem c87130a1_cert0 : certAll 1 (-1) 0 (-25) 25 [(7, 17, 3, 3), (11, 3, 19, 3), (13, 37, 3, 3), (17, 3, 11, 3), (19, 11, 3, 3), (23, 3, 19, 3), (29, 3, 11, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 17, 3), (43, 11, 3, 3), (47, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c87130a1_cert1 : certAll 1 (-1) 0 (-25) 25 [(59, 3, 23, 3), (61, 11, 3, 3), (67, 11, 3, 3), (71, 3, 11, 3), (73, 19, 3, 3), (79, 17, 3, 3), (83, 3, 11, 3), (89, 3, 17, 3), (97, 19, 3, 3)] = true := by decide +kernel
theorem c87130a1_gens : allOn 1 (-1) 0 (-25) 25 [(0, 5, 1), (5, 0, 1), ((-5), 5, 1)] = true := by decide +kernel

-- 87194a1: 23 primes
set_option maxHeartbeats 0 in
theorem c87194a1_cert0 : certAll 1 0 1 (-37) 84 [(5, 3, 13, 3), (7, 3, 11, 3), (11, 5, 3, 5), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c87194a1_cert1 : certAll 1 0 1 (-37) 84 [(47, 3, 11, 3), (53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 17, 3), (73, 11, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c87194a1_gens : allOn 1 0 1 (-37) 84 [(3, 0, 1), (1, 6, 1), (4, 0, 1)] = true := by decide +kernel

-- 87228c1: 23 primes
set_option maxHeartbeats 0 in
theorem c87228c1_cert0 : certAll 0 0 0 (-57) 785 [(5, 7, 13, 7), (7, 5, 17, 5), (11, 5, 31, 7), (13, 11, 5, 5), (17, 7, 5, 5), (19, 5, 7, 5), (23, 5, 29, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 11, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c87228c1_cert1 : certAll 0 0 0 (-57) 785 [(47, 5, 29, 5), (53, 7, 5, 5), (59, 5, 11, 5), (61, 11, 5, 5), (67, 5, 7, 5), (71, 5, 17, 5), (73, 17, 5, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 17, 5, 5)] = true := by decide +kernel
theorem c87228c1_gens : allOn 0 0 0 (-57) 785 [(1, 27, 1), (19, 81, 1), (7, 27, 1)] = true := by decide +kernel

-- 87289b1: 20 primes
set_option maxHeartbeats 0 in
theorem c87289b1_cert0 : certAll 1 1 1 (-132) (-20) [(5, 2, 3, 2), (11, 13, 2, 2), (13, 2, 11, 2), (17, 2, 11, 2), (19, 2, 13, 2), (23, 11, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 11, 2, 2), (47, 2, 3, 2), (53, 11, 2, 2), (59, 2, 3, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c87289b1_cert1 : certAll 1 1 1 (-132) (-20) [(61, 2, 13, 2), (67, 11, 2, 2), (71, 13, 2, 2), (73, 2, 11, 2), (79, 3, 2, 2), (83, 2, 11, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c87289b1_gens : allOn 1 1 1 (-132) (-20) [((-10), 25, 1), (166, 569, 8), ((-4), 23, 1)] = true := by decide +kernel

-- 87336g1: 21 primes
set_option maxHeartbeats 0 in
theorem c87336g1_cert0 : certAll 0 0 0 (-399) 3314 [(5, 11, 17, 23), (7, 5, 13, 5), (11, 7, 23, 13), (13, 5, 7, 5), (17, 5, 23, 5), (19, 5, 7, 5), (23, 7, 5, 5), (29, 5, 11, 7), (31, 11, 5, 5), (37, 17, 5, 5), (41, 5, 17, 5), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c87336g1_cert1 : certAll 0 0 0 (-399) 3314 [(47, 7, 5, 5), (53, 7, 5, 5), (59, 7, 5, 5), (67, 17, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 7, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c87336g1_gens : allOn 0 0 0 (-399) 3314 [(13, 18, 1), (1, 54, 1), ((-23), 18, 1)] = true := by decide +kernel

-- 87398b1: 22 primes
set_option maxHeartbeats 0 in
theorem c87398b1_cert0 : certAll 1 0 1 3 20 [(5, 3, 7, 3), (7, 3, 11, 3), (11, 5, 3, 5), (13, 3, 5, 3), (17, 13, 3, 3), (19, 5, 3, 3), (23, 3, 7, 3), (29, 3, 5, 3), (31, 3, 13, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c87398b1_cert1 : certAll 1 0 1 3 20 [(47, 3, 7, 3), (53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 19, 3), (73, 19, 3, 3), (79, 3, 13, 3), (83, 5, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c87398b1_gens : allOn 1 0 1 3 20 [((-1), 4, 1), (1, 4, 1), ((-2), 3, 1)] = true := by decide +kernel

-- 87634a1: 21 primes
set_option maxHeartbeats 0 in
theorem c87634a1_cert0 : certAll 1 0 1 (-4358) 110352 [(5, 3, 7, 3), (7, 3, 11, 3), (11, 5, 3, 7), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (47, 3, 11, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c87634a1_cert1 : certAll 1 0 1 (-4358) 110352 [(59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 13, 3), (73, 11, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c87634a1_gens : allOn 1 0 1 (-4358) 110352 [(36, 3, 1), ((-50), 476, 1), (122, 1121, 1)] = true := by decide +kernel

-- 87763b1: 21 primes
set_option maxHeartbeats 0 in
theorem c87763b1_cert0 : certAll 1 (-1) 1 (-588) (-4872) [(5, 2, 67, 2), (7, 17, 3, 3), (11, 3, 2, 2), (17, 2, 5, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 5, 2, 2), (41, 2, 11, 2), (47, 2, 5, 2), (53, 3, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c87763b1_cert1 : certAll 1 (-1) 1 (-588) (-4872) [(59, 2, 11, 2), (61, 2, 3, 2), (67, 5, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 5, 2, 2), (83, 2, 5, 2), (89, 2, 11, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c87763b1_gens : allOn 1 (-1) 1 (-588) (-4872) [((-14), 28, 1), (158, 1877, 1), (28, (-8), 1)] = true := by decide +kernel

-- 87837a1: 17 primes
set_option maxHeartbeats 0 in
theorem c87837a1_cert0 : certAll 0 (-1) 1 (-7172) 236912 [(5, 7, 2, 7), (7, 2, 47, 5), (11, 2, 17, 7), (13, 5, 2, 5), (17, 5, 2, 5), (29, 5, 2, 11), (37, 11, 2, 5), (41, 5, 2, 5), (43, 2, 7, 5), (47, 2, 5, 5), (53, 7, 2, 5), (59, 2, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c87837a1_cert1 : certAll 0 (-1) 1 (-7172) 236912 [(61, 5, 2, 5), (71, 2, 5, 5), (73, 5, 2, 5), (79, 2, 7, 5), (97, 17, 2, 5)] = true := by decide +kernel
theorem c87837a1_gens : allOn 0 (-1) 1 (-7172) 236912 [((-26), 636, 1), ((-64), 655, 1), (50, 28, 1)] = true := by decide +kernel

-- 87855a1: 22 primes
set_option maxHeartbeats 0 in
theorem c87855a1_cert0 : certAll 1 1 1 (-141) 588 [(7, 29, 13, 13), (11, 7, 2, 2), (13, 2, 7, 2), (17, 2, 23, 2), (19, 2, 7, 2), (23, 7, 2, 2), (29, 7, 2, 2), (31, 2, 7, 2), (37, 17, 2, 2), (41, 2, 23, 2), (43, 23, 2, 2), (47, 2, 17, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c87855a1_cert1 : certAll 1 1 1 (-141) 588 [(53, 7, 2, 2), (59, 2, 23, 2), (61, 2, 7, 2), (67, 17, 2, 2), (71, 7, 2, 2), (73, 2, 7, 2), (79, 17, 2, 2), (83, 2, 17, 2), (89, 2, 29, 2), (97, 2, 7, 2)] = true := by decide +kernel
theorem c87855a1_gens : allOn 1 1 1 (-141) 588 [(6, (-1), 1), (7, (-7), 1), (4, 8, 1)] = true := by decide +kernel

-- 87866a1: 22 primes
set_option maxHeartbeats 0 in
theorem c87866a1_cert0 : certAll 1 (-1) 0 22 4 [(5, 17, 7, 17), (7, 5, 11, 5), (11, 5, 7, 5), (13, 7, 5, 5), (17, 7, 5, 5), (19, 5, 17, 13), (23, 5, 11, 5), (29, 11, 5, 5), (31, 5, 7, 5), (37, 7, 5, 5), (41, 7, 5, 5), (43, 5, 11, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c87866a1_cert1 : certAll 1 (-1) 0 22 4 [(47, 5, 11, 5), (53, 11, 5, 5), (59, 5, 7, 5), (61, 7, 5, 5), (67, 5, 17, 5), (71, 5, 17, 5), (73, 17, 5, 5), (79, 5, 7, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c87866a1_gens : allOn 1 (-1) 0 22 4 [(0, 2, 1), (4, 10, 1), (24, 106, 1)] = true := by decide +kernel

-- 87914e1: 23 primes
set_option maxHeartbeats 0 in
theorem c87914e1_cert0 : certAll 1 0 0 5 81 [(5, 3, 23, 3), (7, 3, 13, 3), (11, 5, 3, 7), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c87914e1_cert1 : certAll 1 0 0 5 81 [(47, 3, 23, 3), (53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c87914e1_gens : allOn 1 0 0 5 81 [((-2), 9, 1), (2, 9, 1), ((-4), 3, 1)] = true := by decide +kernel

-- 88022a1: 22 primes
set_option maxHeartbeats 0 in
theorem c88022a1_cert0 : certAll 1 1 0 (-534) 4564 [(5, 13, 3, 13), (7, 3, 13, 3), (13, 3, 19, 3), (17, 3, 29, 3), (19, 3, 13, 3), (23, 7, 3, 3), (29, 3, 7, 3), (31, 17, 3, 3), (37, 7, 3, 3), (41, 3, 17, 3), (43, 3, 13, 3), (47, 7, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c88022a1_cert1 : certAll 1 1 0 (-534) 4564 [(53, 13, 3, 3), (59, 13, 3, 3), (61, 3, 13, 3), (67, 7, 3, 3), (71, 7, 3, 3), (73, 3, 7, 3), (79, 3, 7, 3), (83, 3, 7, 3), (89, 7, 3, 3), (97, 43, 3, 3)] = true := by decide +kernel
theorem c88022a1_gens : allOn 1 1 0 (-534) 4564 [(12, 2, 1), (13, (-1), 1), (28, 98, 1)] = true := by decide +kernel

-- 88024a1: 22 primes
set_option maxHeartbeats 0 in
theorem c88024a1_cert0 : certAll 0 0 0 14 1 [(5, 3, 13, 3), (7, 5, 3, 3), (11, 3, 29, 3), (13, 11, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 29, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 11, 3, 3), (43, 5, 3, 3), (47, 3, 23, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c88024a1_cert1 : certAll 0 0 0 14 1 [(53, 3, 5, 3), (59, 3, 11, 3), (61, 11, 3, 3), (67, 5, 3, 3), (71, 3, 23, 3), (73, 23, 3, 3), (79, 5, 3, 3), (83, 3, 11, 3), (89, 3, 5, 3), (97, 29, 3, 3)] = true := by decide +kernel
theorem c88024a1_gens : allOn 0 0 0 14 1 [(0, 1, 1), (1, 4, 1), (4, 11, 1)] = true := by decide +kernel

-- 88208c1: 20 primes
set_option maxHeartbeats 0 in
theorem c88208c1_cert0 : certAll 0 1 0 (-17448) 881332 [(7, 3, 41, 3), (11, 7, 3, 7), (13, 3, 7, 3), (17, 7, 3, 3), (19, 13, 3, 3), (23, 3, 13, 3), (31, 3, 7, 3), (41, 7, 3, 3), (43, 23, 3, 3), (47, 3, 13, 3), (53, 3, 13, 3), (59, 7, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c88208c1_cert1 : certAll 0 1 0 (-17448) 881332 [(61, 3, 7, 3), (67, 31, 3, 3), (71, 3, 23, 3), (73, 13, 3, 3), (79, 3, 7, 3), (83, 7, 3, 3), (89, 7, 3, 3), (97, 23, 3, 3)] = true := by decide +kernel
theorem c88208c1_gens : allOn 0 1 0 (-17448) 881332 [(78, 32, 1), ((-114), 1184, 1), (108, 518, 1)] = true := by decide +kernel

-- 88264h1: 20 primes
set_option maxHeartbeats 0 in
theorem c88264h1_cert0 : certAll 0 0 0 (-199) 1546 [(5, 3, 7, 3), (7, 5, 3, 3), (13, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 13, 3), (31, 7, 3, 3), (37, 7, 3, 3), (41, 3, 13, 3), (43, 5, 3, 3), (47, 3, 5, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c88264h1_cert1 : certAll 0 0 0 (-199) 1546 [(61, 5, 3, 3), (67, 7, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c88264h1_gens : allOn 0 0 0 (-199) 1546 [(53, 374, 1), (9, 22, 1), ((-15), 34, 1)] = true := by decide +kernel

-- 88337a1: 22 primes
set_option maxHeartbeats 0 in
theorem c88337a1_cert0 : certAll 1 0 0 (-15) 16 [(5, 2, 23, 2), (7, 3, 13, 3), (13, 2, 5, 2), (17, 2, 3, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 7, 2), (37, 3, 2, 2), (41, 2, 3, 2), (43, 5, 2, 2), (47, 2, 17, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c88337a1_cert1 : certAll 1 0 0 (-15) 16 [(53, 3, 2, 2), (59, 2, 3, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (83, 2, 3, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c88337a1_gens : allOn 1 0 0 (-15) 16 [(1, 1, 1), (3, (-1), 1), (0, 4, 1)] = true := by decide +kernel

-- 88362e1: 22 primes
set_option maxHeartbeats 0 in
theorem c88362e1_cert0 : certAll 1 (-1) 0 (-108) 324 [(5, 7, 13, 7), (7, 5, 11, 5), (11, 5, 19, 5), (13, 11, 5, 5), (17, 7, 5, 5), (19, 5, 7, 7), (23, 5, 11, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 11, 5, 5), (41, 7, 5, 5), (47, 5, 11, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c88362e1_cert1 : certAll 1 (-1) 0 (-108) 324 [(53, 7, 5, 5), (59, 5, 19, 5), (61, 19, 5, 5), (67, 5, 7, 5), (71, 5, 23, 5), (73, 19, 5, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c88362e1_gens : allOn 1 (-1) 0 (-108) 324 [(0, 18, 1), (9, 0, 1), (3, 3, 1)] = true := by decide +kernel

-- 88460a1: 21 primes
set_option maxHeartbeats 0 in
theorem c88460a1_cert0 : certAll 0 1 0 (-310) 2025 [(7, 3, 13, 3), (11, 7, 3, 17), (13, 3, 7, 3), (17, 7, 3, 3), (19, 29, 3, 3), (23, 3, 29, 3), (29, 3, 23, 3), (31, 3, 7, 3), (37, 3, 7, 3), (41, 7, 3, 3), (43, 23, 3, 3), (47, 3, 23, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c88460a1_cert1 : certAll 0 1 0 (-310) 2025 [(53, 3, 31, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 37, 3, 3), (71, 3, 23, 3), (73, 29, 3, 3), (79, 3, 7, 3), (89, 7, 3, 3), (97, 23, 3, 3)] = true := by decide +kernel
theorem c88460a1_gens : allOn 0 1 0 (-310) 2025 [(10, 5, 1), (5, 25, 1), ((-10), 65, 1)] = true := by decide +kernel

-- 88492a1: 22 primes
set_option maxHeartbeats 0 in
theorem c88492a1_cert0 : certAll 0 1 0 (-49) 120 [(5, 3, 7, 3), (7, 3, 11, 3), (11, 5, 3, 5), (13, 3, 5, 3), (17, 13, 3, 3), (19, 5, 3, 3), (23, 3, 7, 3), (29, 3, 5, 3), (31, 3, 13, 3), (37, 3, 5, 3), (41, 7, 3, 3), (47, 3, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c88492a1_cert1 : certAll 0 1 0 (-49) 120 [(53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 23, 3), (73, 19, 3, 3), (79, 3, 13, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c88492a1_gens : allOn 0 1 0 (-49) 120 [(3, 3, 1), (5, 5, 1), (4, 2, 1)] = true := by decide +kernel

-- 88502f1: 20 primes
set_option maxHeartbeats 0 in
theorem c88502f1_cert0 : certAll 1 0 1 (-838) 9252 [(5, 3, 13, 3), (7, 3, 29, 3), (11, 5, 3, 7), (13, 3, 5, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 23, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c88502f1_cert1 : certAll 1 0 1 (-838) 9252 [(61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c88502f1_gens : allOn 1 0 1 (-838) 9252 [(19, 7, 1), (15, 3, 1), ((-15), 143, 1), (17, (-9), 1)] = true := by decide +kernel

-- 88582e1: 22 primes
set_option maxHeartbeats 0 in
theorem c88582e1_cert0 : certAll 1 1 0 (-766) 7904 [(5, 17, 3, 17), (7, 3, 11, 3), (11, 5, 7, 5), (17, 3, 5, 3), (19, 3, 17, 3), (23, 5, 3, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 7, 3, 3), (41, 3, 5, 3), (43, 3, 7, 3), (47, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c88582e1_cert1 : certAll 1 1 0 (-766) 7904 [(53, 7, 3, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 37, 3), (83, 3, 7, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c88582e1_gens : allOn 1 1 0 (-766) 7904 [(14, 6, 1), ((-25), (-98), 1), (86, 217, 8)] = true := by decide +kernel

-- 88705c1: 20 primes
set_option maxHeartbeats 0 in
theorem c88705c1_cert0 : certAll 1 (-1) 1 (-597) 20946 [(7, 11, 3, 3), (11, 3, 2, 2), (13, 2, 3, 2), (17, 2, 7, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 7, 2, 2), (41, 2, 11, 2), (43, 23, 2, 2), (47, 2, 7, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c88705c1_cert1 : certAll 1 (-1) 1 (-597) 20946 [(53, 3, 2, 2), (59, 2, 11, 2), (67, 7, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 7, 2, 2), (83, 2, 7, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c88705c1_gens : allOn 1 (-1) 1 (-597) 20946 [(11, 119, 1), (136, 1494, 1), ((-78), 4088, 27)] = true := by decide +kernel

-- 88754a1: 23 primes
set_option maxHeartbeats 0 in
theorem c88754a1_cert0 : certAll 1 (-1) 0 (-10) 11412 [(5, 7, 17, 7), (7, 13, 5, 5), (11, 7, 5, 7), (13, 5, 7, 5), (17, 7, 5, 5), (19, 13, 7, 7), (23, 7, 5, 5), (29, 5, 17, 5), (31, 5, 7, 5), (37, 5, 7, 5), (41, 5, 13, 5), (43, 17, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c88754a1_cert1 : certAll 1 (-1) 0 (-10) 11412 [(47, 7, 5, 5), (53, 5, 13, 5), (59, 5, 13, 5), (61, 13, 5, 5), (67, 5, 7, 5), (71, 5, 23, 5), (73, 13, 5, 5), (79, 5, 7, 5), (83, 7, 5, 5), (89, 5, 17, 5), (97, 5, 7, 5)] = true := by decide +kernel
theorem c88754a1_gens : allOn 1 (-1) 0 (-10) 11412 [(43, 277, 1), (742, 6793, 8), ((-1228), 4793, 64)] = true := by decide +kernel

-- 88765d1: 20 primes
set_option maxHeartbeats 0 in
theorem c88765d1_cert0 : certAll 1 (-1) 1 18 6 [(7, 13, 3, 3), (11, 3, 2, 2), (13, 2, 3, 2), (17, 2, 11, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 11, 2, 2), (43, 11, 2, 2), (47, 2, 11, 2), (53, 3, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c88765d1_cert1 : certAll 1 (-1) 1 18 6 [(59, 2, 31, 2), (61, 2, 3, 2), (67, 11, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 13, 2, 2), (89, 2, 13, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c88765d1_gens : allOn 1 (-1) 1 18 6 [(1, 4, 1), (6, 14, 1), (4, 9, 1)] = true := by decide +kernel

-- 88883a1: 21 primes
set_option maxHeartbeats 0 in
theorem c88883a1_cert0 : certAll 1 (-1) 1 0 14 [(7, 11, 13, 13), (11, 7, 2, 2), (13, 2, 7, 2), (17, 2, 11, 2), (19, 2, 7, 2), (23, 7, 2, 2), (29, 7, 2, 2), (31, 2, 7, 2), (37, 11, 2, 2), (41, 2, 11, 2), (43, 17, 2, 2), (47, 2, 19, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c88883a1_cert1 : certAll 1 (-1) 1 0 14 [(53, 7, 2, 2), (59, 2, 11, 2), (61, 2, 7, 2), (67, 17, 2, 2), (71, 7, 2, 2), (73, 2, 7, 2), (83, 2, 11, 2), (89, 2, 11, 2), (97, 2, 7, 2)] = true := by decide +kernel
theorem c88883a1_gens : allOn 1 (-1) 1 0 14 [((-2), 2, 1), (2, 3, 1), (7, 14, 1)] = true := by decide +kernel

-- 88975c1: 22 primes
set_option maxHeartbeats 0 in
theorem c88975c1_cert0 : certAll 0 (-1) 1 (-3) 33 [(7, 3, 17, 3), (11, 7, 37, 7), (13, 3, 7, 3), (17, 3, 13, 3), (19, 3, 7, 3), (23, 7, 3, 3), (29, 3, 11, 3), (31, 11, 3, 3), (37, 17, 3, 3), (41, 3, 13, 3), (43, 3, 7, 3), (47, 7, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c88975c1_cert1 : certAll 0 (-1) 1 (-3) 33 [(53, 7, 3, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 13, 3, 3), (71, 7, 3, 3), (73, 3, 7, 3), (79, 3, 7, 3), (83, 3, 19, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c88975c1_gens : allOn 0 (-1) 1 (-3) 33 [((-3), 2, 1), (7, 17, 1), (3, 6, 1)] = true := by decide +kernel

-- 89098a1: 23 primes
set_option maxHeartbeats 0 in
theorem c89098a1_cert0 : certAll 1 1 0 (-83) 301 [(5, 7, 3, 7), (7, 3, 5, 3), (11, 7, 5, 7), (13, 3, 7, 3), (17, 3, 5, 3), (19, 3, 7, 3), (23, 7, 3, 3), (29, 3, 13, 3), (31, 5, 3, 3), (37, 5, 3, 3), (41, 3, 13, 3), (43, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c89098a1_cert1 : certAll 1 1 0 (-83) 301 [(47, 7, 3, 3), (53, 5, 3, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 7, 3), (83, 3, 5, 3), (89, 5, 3, 3), (97, 5, 3, 3)] = true := by decide +kernel
theorem c89098a1_gens : allOn 1 1 0 (-83) 301 [(6, 5, 1), ((-10), 21, 1), (38, 213, 1)] = true := by decide +kernel

-- 89294a1: 23 primes
set_option maxHeartbeats 0 in
theorem c89294a1_cert0 : certAll 1 (-1) 1 (-84) 567 [(5, 3, 17, 3), (7, 5, 3, 3), (11, 3, 23, 3), (13, 5, 3, 3), (17, 3, 19, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 11, 3), (31, 11, 3, 3), (37, 23, 3, 3), (41, 3, 17, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c89294a1_cert1 : certAll 1 (-1) 1 (-84) 567 [(47, 3, 5, 3), (53, 3, 5, 3), (59, 3, 5, 3), (61, 5, 3, 3), (67, 17, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 5, 3, 3), (83, 3, 19, 3), (89, 3, 5, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c89294a1_gens : allOn 1 (-1) 1 (-84) 567 [(5, 13, 1), ((-11), 13, 1), ((-3), 29, 1)] = true := by decide +kernel

-- 89421b1: 20 primes
set_option maxHeartbeats 0 in
theorem c89421b1_cert0 : certAll 1 1 1 (-1198) 15164 [(7, 11, 13, 13), (11, 7, 2, 2), (13, 2, 7, 2), (17, 2, 11, 2), (19, 2, 7, 2), (23, 7, 2, 2), (29, 7, 2, 2), (31, 2, 7, 2), (37, 11, 2, 2), (43, 17, 2, 2), (47, 2, 17, 2), (59, 2, 11, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c89421b1_cert1 : certAll 1 1 1 (-1198) 15164 [(61, 2, 7, 2), (67, 23, 2, 2), (71, 7, 2, 2), (73, 2, 7, 2), (79, 11, 2, 2), (83, 2, 11, 2), (89, 2, 11, 2), (97, 2, 7, 2)] = true := by decide +kernel
theorem c89421b1_gens : allOn 1 1 1 (-1198) 15164 [(16, 12, 1), (98, 873, 1), (1844, 3843, 64)] = true := by decide +kernel

-- 89428b1: 20 primes
set_option maxHeartbeats 0 in
theorem c89428b1_cert0 : certAll 0 1 0 47 240 [(7, 3, 13, 3), (11, 7, 3, 13), (13, 3, 7, 3), (17, 7, 3, 3), (19, 11, 3, 3), (23, 3, 19, 3), (29, 3, 11, 3), (31, 3, 7, 3), (37, 3, 7, 3), (41, 7, 3, 3), (43, 11, 3, 3), (47, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c89428b1_cert1 : certAll 0 1 0 47 240 [(53, 3, 19, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 11, 3, 3), (71, 3, 11, 3), (73, 19, 3, 3), (89, 7, 3, 3), (97, 19, 3, 3)] = true := by decide +kernel
theorem c89428b1_gens : allOn 0 1 0 47 240 [(17, 79, 1), ((-22), 79, 8), ((-15), 395, 27)] = true := by decide +kernel

-- 89475a1: 21 primes
set_option maxHeartbeats 0 in
theorem c89475a1_cert0 : certAll 1 1 1 37 1406 [(7, 11, 17, 13), (11, 13, 2, 2), (13, 2, 19, 2), (17, 2, 11, 2), (19, 2, 11, 2), (23, 7, 2, 2), (29, 11, 2, 2), (31, 2, 7, 2), (37, 7, 2, 2), (41, 2, 11, 2), (43, 7, 2, 2), (47, 2, 29, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c89475a1_cert1 : certAll 1 1 1 37 1406 [(53, 11, 2, 2), (59, 2, 7, 2), (61, 2, 13, 2), (67, 7, 2, 2), (73, 2, 7, 2), (79, 11, 2, 2), (83, 2, 7, 2), (89, 2, 11, 2), (97, 2, 7, 2)] = true := by decide +kernel
theorem c89475a1_gens : allOn 1 1 1 37 1406 [(15, 67, 1), (0, 37, 1), (90, 817, 1)] = true := by decide +kernel

-- 89574a1: 21 primes
set_option maxHeartbeats 0 in
theorem c89574a1_cert0 : certAll 1 1 0 (-31) 85 [(5, 11, 7, 47), (7, 5, 37, 5), (11, 5, 7, 5), (13, 7, 5, 5), (19, 5, 23, 11), (23, 5, 7, 5), (29, 7, 5, 5), (31, 5, 37, 5), (37, 7, 5, 5), (41, 7, 5, 5), (43, 5, 7, 5), (47, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c89574a1_cert1 : certAll 1 1 0 (-31) 85 [(53, 7, 5, 5), (59, 5, 23, 5), (61, 11, 5, 5), (67, 5, 11, 5), (71, 5, 11, 5), (73, 11, 5, 5), (79, 5, 11, 5), (83, 5, 7, 5), (97, 7, 5, 5)] = true := by decide +kernel
theorem c89574a1_gens : allOn 1 1 0 (-31) 85 [((-2), 13, 1), (2, 5, 1), (10, 25, 1)] = true := by decide +kernel

-- 89576d1: 20 primes
set_option maxHeartbeats 0 in
theorem c89576d1_cert0 : certAll 0 (-1) 0 (-15) 16 [(5, 13, 3, 13), (7, 3, 11, 3), (11, 5, 7, 7), (13, 3, 5, 3), (17, 3, 5, 3), (19, 3, 11, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 7, 3, 3), (41, 3, 5, 3), (43, 3, 7, 3), (47, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c89576d1_cert1 : certAll 0 (-1) 0 (-15) 16 [(53, 7, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (73, 3, 5, 3), (79, 3, 13, 3), (83, 3, 7, 3), (89, 7, 3, 3), (97, 7, 3, 3)] = true := by decide +kernel
theorem c89576d1_gens : allOn 0 (-1) 0 (-15) 16 [(1, 1, 1), ((-3), 5, 1), (0, 4, 1)] = true := by decide +kernel

-- 89687a1: 21 primes
set_option maxHeartbeats 0 in
theorem c89687a1_cert0 : certAll 1 0 0 (-14) 13 [(5, 2, 7, 2), (7, 3, 17, 3), (11, 5, 2, 2), (17, 2, 3, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 7, 2), (37, 3, 2, 2), (41, 2, 3, 2), (47, 2, 17, 2), (53, 3, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c89687a1_cert1 : certAll 1 0 0 (-14) 13 [(59, 2, 3, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (83, 2, 3, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c89687a1_gens : allOn 1 0 0 (-14) 13 [(1, 0, 1), (3, (-1), 1), (4, 3, 1)] = true := by decide +kernel

-- 89738b1: 21 primes
set_option maxHeartbeats 0 in
theorem c89738b1_cert0 : certAll 1 (-1) 0 (-31) 61 [(5, 3, 7, 3), (7, 5, 3, 3), (13, 5, 3, 3), (17, 3, 13, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 7, 3), (31, 13, 3, 3), (37, 7, 3, 3), (41, 3, 13, 3), (43, 5, 3, 3), (47, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c89738b1_cert1 : certAll 1 (-1) 0 (-31) 61 [(53, 3, 5, 3), (59, 3, 5, 3), (61, 5, 3, 3), (67, 7, 3, 3), (71, 3, 5, 3), (79, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3), (97, 19, 3, 3)] = true := by decide +kernel
theorem c89738b1_gens : allOn 1 (-1) 0 (-31) 61 [(2, 1, 1), (6, 5, 1), ((-6), 1, 1)] = true := by decide +kernel

-- 89992a1: 22 primes
set_option maxHeartbeats 0 in
theorem c89992a1_cert0 : certAll 0 0 0 (-31) 226 [(5, 3, 13, 3), (11, 3, 17, 3), (13, 23, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 17, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3), (47, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c89992a1_cert1 : certAll 0 0 0 (-31) 226 [(53, 3, 5, 3), (59, 3, 11, 3), (61, 11, 3, 3), (67, 5, 3, 3), (71, 3, 37, 3), (73, 11, 3, 3), (79, 5, 3, 3), (83, 3, 17, 3), (89, 3, 5, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c89992a1_gens : allOn 0 0 0 (-31) 226 [(1, 14, 1), (15, 56, 1), (5, 14, 1)] = true := by decide +kernel

-- 90297b1: 22 primes
set_option maxHeartbeats 0 in
theorem c90297b1_cert0 : certAll 0 0 1 (-114) 412 [(5, 7, 13, 7), (7, 5, 11, 5), (11, 7, 13, 7), (13, 5, 7, 5), (17, 5, 23, 5), (19, 5, 7, 5), (23, 7, 5, 5), (29, 5, 13, 7), (31, 11, 5, 5), (37, 13, 5, 5), (41, 5, 11, 5), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c90297b1_cert1 : certAll 0 0 1 (-114) 412 [(47, 7, 5, 5), (53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (67, 11, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (83, 5, 23, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c90297b1_gens : allOn 0 0 1 (-114) 412 [(14, 39, 1), ((-46), 233, 8), (10, 16, 1)] = true := by decide +kernel

-- 90312i1: 19 primes
set_option maxHeartbeats 0 in
theorem c90312i1_cert0 : certAll 0 1 0 (-620) 6864 [(5, 7, 13, 7), (7, 5, 37, 5), (11, 5, 29, 7), (13, 11, 5, 5), (17, 7, 5, 5), (19, 5, 7, 5), (23, 5, 19, 5), (29, 7, 5, 5), (37, 11, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5), (47, 5, 19, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c90312i1_cert1 : certAll 0 1 0 (-620) 6864 [(59, 5, 11, 5), (61, 11, 5, 5), (67, 5, 7, 5), (73, 19, 5, 5), (79, 5, 7, 5), (89, 7, 5, 5), (97, 19, 5, 5)] = true := by decide +kernel
theorem c90312i1_gens : allOn 0 1 0 (-620) 6864 [(34, 162, 1), (16, 36, 1), ((-20), 108, 1)] = true := by decide +kernel

-- 90459o1: 19 primes
set_option maxHeartbeats 0 in
theorem c90459o1_cert0 : certAll 0 0 1 (-1587) 72076 [(5, 17, 2, 17), (7, 2, 11, 5), (11, 2, 7, 7), (13, 7, 2, 5), (17, 11, 2, 5), (29, 7, 2, 5), (31, 2, 13, 5), (37, 7, 2, 5), (41, 7, 2, 7), (43, 2, 7, 5), (47, 2, 7, 5), (59, 2, 11, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c90459o1_cert1 : certAll 0 0 1 (-1587) 72076 [(61, 11, 2, 5), (67, 2, 13, 5), (71, 2, 43, 5), (73, 11, 2, 5), (79, 2, 13, 5), (83, 2, 7, 5), (97, 7, 2, 5)] = true := by decide +kernel
theorem c90459o1_gens : allOn 0 0 1 (-1587) 72076 [((-23), 310, 1), (23, 218, 1), (31, 229, 1)] = true := by decide +kernel

-- 90568e1: 21 primes
set_option maxHeartbeats 0 in
theorem c90568e1_cert0 : certAll 0 1 0 (-36) (-32) [(5, 3, 7, 3), (7, 3, 5, 3), (11, 13, 3, 7), (13, 3, 31, 3), (17, 23, 3, 3), (19, 13, 3, 3), (23, 3, 5, 3), (31, 3, 37, 3), (37, 3, 13, 3), (41, 5, 3, 3), (43, 13, 3, 3), (47, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c90568e1_cert1 : certAll 0 1 0 (-36) (-32) [(53, 3, 13, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 17, 3), (73, 23, 3, 3), (79, 3, 23, 3), (83, 13, 3, 3), (89, 5, 3, 3), (97, 5, 3, 3)] = true := by decide +kernel
theorem c90568e1_gens : allOn 0 1 0 (-36) (-32) [((-2), 6, 1), ((-6), 2, 1), ((-4), 8, 1)] = true := by decide +kernel

-- 90644b1: 20 primes
set_option maxHeartbeats 0 in
theorem c90644b1_cert0 : certAll 0 0 0 56 1 [(5, 3, 23, 3), (7, 5, 3, 3), (11, 3, 19, 3), (13, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 41, 3), (37, 19, 3, 3), (41, 3, 11, 3), (47, 3, 5, 3), (53, 3, 5, 3), (59, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c90644b1_cert1 : certAll 0 0 0 56 1 [(61, 5, 3, 3), (67, 11, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 5, 3, 3), (83, 3, 19, 3), (89, 3, 5, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c90644b1_gens : allOn 0 0 0 56 1 [(8, 31, 1), (2, 11, 1), (2, 31, 8)] = true := by decide +kernel

-- 90704c1: 22 primes
set_option maxHeartbeats 0 in
theorem c90704c1_cert0 : certAll 0 1 0 (-77) (-281) [(5, 3, 7, 3), (7, 3, 43, 3), (11, 23, 3, 7), (13, 3, 11, 3), (17, 5, 3, 3), (19, 5, 3, 3), (23, 3, 5, 3), (31, 3, 5, 3), (37, 3, 5, 3), (41, 5, 3, 3), (43, 5, 3, 3), (47, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c90704c1_cert1 : certAll 0 1 0 (-77) (-281) [(53, 3, 5, 3), (59, 11, 3, 3), (61, 3, 23, 3), (67, 7, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 13, 3, 3)] = true := by decide +kernel
theorem c90704c1_gens : allOn 0 1 0 (-77) (-281) [((-5), 2, 1), ((-6), 1, 1), (10, 7, 1)] = true := by decide +kernel

-- 90840a1: 21 primes
set_option maxHeartbeats 0 in
theorem c90840a1_cert0 : certAll 0 (-1) 0 (-121) 445 [(7, 19, 11, 17), (11, 7, 19, 13), (13, 11, 7, 7), (17, 7, 11, 7), (19, 23, 7, 7), (23, 7, 11, 7), (29, 7, 17, 7), (31, 11, 7, 7), (37, 11, 7, 7), (41, 7, 17, 7), (43, 17, 7, 7), (47, 7, 11, 7)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c90840a1_cert1 : certAll 0 (-1) 0 (-121) 445 [(53, 7, 17, 7), (59, 7, 47, 7), (61, 17, 7, 7), (67, 11, 7, 7), (73, 17, 7, 7), (79, 11, 7, 7), (83, 7, 11, 7), (89, 7, 29, 7), (97, 11, 7, 7)] = true := by decide +kernel
theorem c90840a1_gens : allOn 0 (-1) 0 (-121) 445 [(13, 30, 1), (3, 10, 1), ((-7), 30, 1)] = true := by decide +kernel

-- 90935a1: 21 primes
set_option maxHeartbeats 0 in
theorem c90935a1_cert0 : certAll 0 1 1 34 426 [(7, 2, 17, 3), (11, 2, 3, 7), (17, 7, 2, 3), (19, 2, 3, 3), (23, 2, 11, 3), (29, 3, 2, 3), (31, 2, 7, 3), (37, 3, 2, 3), (41, 7, 2, 3), (43, 2, 3, 3), (47, 2, 17, 3), (53, 3, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c90935a1_cert1 : certAll 0 1 1 34 426 [(59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 11, 3), (73, 11, 2, 3), (79, 2, 7, 3), (83, 2, 3, 3), (89, 7, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c90935a1_gens : allOn 0 1 1 34 426 [(7, 32, 1), (20, 97, 1), ((-6), 539, 27)] = true := by decide +kernel

-- 90953a1: 19 primes
set_option maxHeartbeats 0 in
theorem c90953a1_cert0 : certAll 1 (-1) 1 (-261) (-5418) [(5, 2, 7, 2), (7, 5, 3, 3), (11, 3, 2, 2), (13, 2, 3, 2), (17, 2, 5, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 7, 2, 2), (41, 2, 5, 2), (43, 5, 2, 2), (53, 3, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c90953a1_cert1 : certAll 1 (-1) 1 (-261) (-5418) [(59, 2, 7, 2), (67, 5, 2, 2), (71, 3, 2, 2), (79, 5, 2, 2), (83, 2, 7, 2), (89, 2, 5, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c90953a1_gens : allOn 1 (-1) 1 (-261) (-5418) [(23, 7, 1), (118, 1204, 1), (222, 607, 8)] = true := by decide +kernel

-- 91031c1: 19 primes
set_option maxHeartbeats 0 in
theorem c91031c1_cert0 : certAll 0 1 1 (-9210) 271050 [(5, 3, 2, 3), (11, 2, 3, 17), (13, 3, 2, 3), (17, 13, 2, 3), (19, 2, 3, 3), (23, 2, 41, 3), (31, 2, 13, 3), (37, 3, 2, 3), (41, 11, 2, 3), (47, 2, 11, 3), (53, 3, 2, 3), (59, 2, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c91031c1_cert1 : certAll 0 1 1 (-9210) 271050 [(61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 11, 3), (79, 2, 11, 3), (83, 2, 3, 3), (89, 11, 2, 3), (97, 17, 2, 3)] = true := by decide +kernel
theorem c91031c1_gens : allOn 0 1 1 (-9210) 271050 [((-13), 623, 1), (186, 2113, 8), (3728, 227577, 1)] = true := by decide +kernel

-- 91055a1: 22 primes
set_option maxHeartbeats 0 in
theorem c91055a1_cert0 : certAll 0 1 1 (-46) 110 [(7, 2, 13, 3), (11, 2, 3, 7), (13, 3, 2, 3), (17, 7, 2, 3), (19, 2, 3, 3), (23, 2, 11, 3), (29, 3, 2, 3), (31, 2, 7, 3), (37, 3, 2, 3), (41, 7, 2, 3), (43, 2, 3, 3), (47, 2, 17, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c91055a1_cert1 : certAll 0 1 1 (-46) 110 [(53, 3, 2, 3), (59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 11, 3), (73, 11, 2, 3), (79, 2, 7, 3), (83, 2, 3, 3), (89, 7, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c91055a1_gens : allOn 0 1 1 (-46) 110 [(4, 2, 1), ((-1), 12, 1), (9, 22, 1)] = true := by decide +kernel

-- 91248s1: 23 primes
set_option maxHeartbeats 0 in
theorem c91248s1_cert0 : certAll 0 (-1) 0 (-112) 256 [(5, 11, 7, 17), (7, 5, 23, 5), (11, 13, 7, 7), (13, 5, 11, 5), (17, 5, 7, 5), (19, 5, 17, 5), (23, 13, 5, 5), (29, 5, 13, 7), (31, 7, 5, 5), (37, 7, 5, 5), (41, 5, 11, 5), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c91248s1_cert1 : certAll 0 (-1) 0 (-112) 256 [(47, 13, 5, 5), (53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (67, 7, 5, 5), (71, 7, 5, 5), (73, 5, 7, 5), (79, 5, 11, 5), (83, 5, 7, 5), (89, 7, 5, 5), (97, 7, 5, 5)] = true := by decide +kernel
theorem c91248s1_gens : allOn 0 (-1) 0 (-112) 256 [((-8), 24, 1), (16, 48, 1), (0, 16, 1)] = true := by decide +kernel

-- 91270c1: 22 primes
set_option maxHeartbeats 0 in
theorem c91270c1_cert0 : certAll 1 0 1 (-173) 1428 [(7, 3, 11, 3), (11, 7, 3, 13), (13, 3, 7, 3), (17, 7, 3, 3), (19, 17, 3, 3), (23, 3, 11, 3), (29, 3, 17, 3), (31, 3, 7, 3), (37, 3, 7, 3), (41, 7, 3, 3), (43, 17, 3, 3), (47, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c91270c1_cert1 : certAll 1 0 1 (-173) 1428 [(53, 3, 17, 3), (59, 7, 3, 3), (61, 3, 7, 3), (67, 11, 3, 3), (71, 3, 29, 3), (73, 29, 3, 3), (79, 3, 7, 3), (83, 7, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c91270c1_gens : allOn 1 0 1 (-173) 1428 [(9, 20, 1), ((-1), 40, 1), ((-11), 50, 1)] = true := by decide +kernel

-- 91341d1: 22 primes
set_option maxHeartbeats 0 in
theorem c91341d1_cert0 : certAll 0 0 1 (-129) 562 [(5, 19, 2, 43), (7, 2, 11, 5), (11, 2, 7, 7), (13, 5, 2, 5), (19, 2, 11, 5), (23, 2, 5, 5), (29, 5, 2, 7), (31, 2, 5, 5), (37, 7, 2, 5), (41, 5, 2, 5), (43, 2, 19, 5), (47, 2, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c91341d1_cert1 : certAll 0 0 1 (-129) 562 [(53, 19, 2, 5), (59, 2, 5, 5), (61, 5, 2, 5), (67, 2, 5, 5), (71, 2, 5, 5), (73, 5, 2, 5), (79, 2, 7, 5), (83, 2, 7, 5), (89, 7, 2, 5), (97, 11, 2, 5)] = true := by decide +kernel
theorem c91341d1_gens : allOn 0 0 1 (-129) 562 [(7, 1, 1), (4, 10, 1), (10, 16, 1)] = true := by decide +kernel

-- 91388b1: 17 primes
set_option maxHeartbeats 0 in
theorem c91388b1_cert0 : certAll 0 1 0 54 793 [(5, 3, 13, 3), (7, 3, 5, 3), (13, 3, 7, 3), (17, 7, 3, 3), (19, 13, 3, 3), (29, 3, 13, 3), (37, 3, 7, 3), (41, 5, 3, 3), (43, 13, 3, 3), (47, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c91388b1_cert1 : certAll 0 1 0 54 793 [(71, 3, 47, 3), (73, 41, 3, 3), (79, 3, 7, 3), (83, 7, 3, 3), (97, 5, 3, 3)] = true := by decide +kernel
theorem c91388b1_gens : allOn 0 1 0 54 793 [(14, 67, 1), (4, 33, 1), ((-24), 737, 27)] = true := by decide +kernel

-- 91506a1: 22 primes
set_option maxHeartbeats 0 in
theorem c91506a1_cert0 : certAll 1 1 0 (-481) 3865 [(5, 7, 13, 7), (7, 5, 17, 5), (11, 5, 23, 5), (13, 17, 5, 5), (17, 7, 5, 5), (19, 5, 7, 7), (23, 5, 31, 5), (31, 5, 7, 5), (37, 11, 5, 5), (41, 7, 5, 5), (43, 5, 7, 5), (47, 5, 11, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c91506a1_cert1 : certAll 1 1 0 (-481) 3865 [(53, 7, 5, 5), (59, 5, 23, 5), (61, 11, 5, 5), (67, 5, 7, 5), (71, 5, 11, 5), (73, 17, 5, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 17, 5, 5)] = true := by decide +kernel
theorem c91506a1_gens : allOn 1 1 0 (-481) 3865 [(13, (-2), 1), (12, (-7), 1), (11, 2, 1)] = true := by decide +kernel

-- 91607a1: 20 primes
set_option maxHeartbeats 0 in
theorem c91607a1_cert0 : certAll 1 0 0 (-19) (-30) [(5, 2, 7, 2), (7, 3, 13, 3), (13, 2, 5, 2), (17, 2, 3, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 7, 2), (37, 3, 2, 2), (41, 2, 3, 2), (43, 5, 2, 2), (47, 2, 19, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c91607a1_cert1 : certAll 1 0 0 (-19) (-30) [(53, 3, 2, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c91607a1_gens : allOn 1 0 0 (-19) (-30) [((-2), 2, 1), ((-3), 3, 1), (6, 6, 1)] = true := by decide +kernel

-- 91744d1: 20 primes
set_option maxHeartbeats 0 in
theorem c91744d1_cert0 : certAll 0 1 0 (-1281) 17263 [(5, 3, 7, 3), (7, 3, 5, 3), (11, 13, 3, 7), (13, 3, 11, 3), (17, 13, 3, 3), (19, 11, 3, 3), (23, 3, 5, 3), (29, 3, 11, 3), (31, 3, 13, 3), (37, 3, 13, 3), (41, 5, 3, 3), (43, 11, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c91744d1_cert1 : certAll 0 1 0 (-1281) 17263 [(53, 3, 17, 3), (59, 5, 3, 3), (67, 5, 3, 3), (73, 19, 3, 3), (79, 3, 11, 3), (83, 13, 3, 3), (89, 5, 3, 3), (97, 5, 3, 3)] = true := by decide +kernel
theorem c91744d1_gens : allOn 0 1 0 (-1281) 17263 [((-21), 188, 1), (26, 47, 1), (561, 188, 27)] = true := by decide +kernel

-- 91775c1: 20 primes
set_option maxHeartbeats 0 in
theorem c91775c1_cert0 : certAll 0 1 1 (-38) 84 [(7, 2, 11, 3), (11, 2, 3, 7), (13, 3, 2, 3), (17, 7, 2, 3), (19, 2, 3, 3), (29, 3, 2, 3), (31, 2, 7, 3), (37, 3, 2, 3), (43, 2, 3, 3), (47, 2, 11, 3), (53, 3, 2, 3), (59, 2, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c91775c1_cert1 : certAll 0 1 1 (-38) 84 [(61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 17, 3), (73, 13, 2, 3), (79, 2, 7, 3), (83, 2, 3, 3), (89, 7, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c91775c1_gens : allOn 0 1 1 (-38) 84 [(3, 2, 1), ((-2), 12, 1), (4, 3, 1)] = true := by decide +kernel

-- 91958a1: 20 primes
set_option maxHeartbeats 0 in
theorem c91958a1_cert0 : certAll 1 1 0 (-69) (-179) [(5, 11, 3, 23), (7, 3, 29, 3), (11, 17, 7, 7), (17, 3, 19, 3), (19, 3, 29, 3), (23, 7, 3, 3), (29, 3, 7, 3), (31, 11, 3, 3), (37, 7, 3, 3), (41, 3, 17, 3), (43, 3, 11, 3), (53, 37, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c91958a1_cert1 : certAll 1 1 0 (-69) (-179) [(59, 11, 3, 3), (61, 3, 17, 3), (67, 7, 3, 3), (73, 3, 7, 3), (79, 3, 7, 3), (83, 3, 7, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c91958a1_gens : allOn 1 1 0 (-69) (-179) [((-6), 11, 1), (10, 11, 1), (9, 1, 1)] = true := by decide +kernel

-- 91963a1: 20 primes
set_option maxHeartbeats 0 in
theorem c91963a1_cert0 : certAll 0 0 1 (-11) 20 [(5, 7, 2, 7), (7, 2, 17, 5), (13, 19, 2, 5), (17, 7, 2, 5), (19, 2, 7, 7), (23, 2, 13, 5), (29, 7, 2, 5), (31, 2, 7, 5), (37, 13, 2, 5), (43, 2, 7, 5), (47, 2, 13, 5), (53, 7, 2, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c91963a1_cert1 : certAll 0 0 1 (-11) 20 [(61, 13, 2, 5), (67, 2, 7, 5), (71, 2, 17, 5), (73, 13, 2, 5), (79, 2, 7, 5), (83, 2, 13, 5), (89, 7, 2, 5), (97, 17, 2, 5)] = true := by decide +kernel
theorem c91963a1_gens : allOn 0 0 1 (-11) 20 [(2, 2, 1), (0, 4, 1), (5, 9, 1)] = true := by decide +kernel

-- 91985b1: 22 primes
set_option maxHeartbeats 0 in
theorem c91985b1_cert0 : certAll 0 0 1 (-367) 2580 [(7, 2, 3, 3), (11, 2, 7, 3), (13, 7, 2, 3), (17, 3, 2, 3), (19, 2, 3, 3), (23, 2, 7, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 7, 2, 3), (41, 3, 2, 3), (43, 2, 3, 3), (47, 2, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c91985b1_cert1 : certAll 0 0 1 (-367) 2580 [(53, 3, 2, 3), (59, 2, 17, 3), (61, 19, 2, 3), (67, 2, 3, 3), (71, 2, 17, 3), (73, 17, 2, 3), (79, 2, 3, 3), (83, 2, 7, 3), (89, 3, 2, 3), (97, 7, 2, 3)] = true := by decide +kernel
theorem c91985b1_gens : allOn 0 0 1 (-367) 2580 [(8, 12, 1), ((-17), 62, 1), (114, 121, 8)] = true := by decide +kernel

-- 92096d1: 22 primes
set_option maxHeartbeats 0 in
theorem c92096d1_cert0 : certAll 0 (-1) 0 (-41) 169 [(5, 7, 3, 7), (7, 3, 5, 3), (11, 7, 5, 7), (13, 3, 7, 3), (17, 3, 5, 3), (19, 3, 7, 3), (23, 7, 3, 3), (29, 3, 11, 3), (31, 5, 3, 3), (37, 5, 3, 3), (41, 3, 17, 3), (43, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c92096d1_cert1 : certAll 0 (-1) 0 (-41) 169 [(47, 7, 3, 3), (53, 5, 3, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (83, 3, 5, 3), (89, 5, 3, 3), (97, 5, 3, 3)] = true := by decide +kernel
theorem c92096d1_gens : allOn 0 (-1) 0 (-41) 169 [(5, 8, 1), ((-3), 16, 1), (3, 8, 1)] = true := by decide +kernel

-- 92144a1: 22 primes
set_option maxHeartbeats 0 in
theorem c92144a1_cert0 : certAll 0 1 0 (-1056) 12916 [(5, 3, 23, 3), (7, 3, 5, 3), (11, 7, 3, 7), (17, 7, 3, 3), (19, 29, 3, 3), (23, 3, 5, 3), (29, 3, 19, 3), (31, 3, 7, 3), (37, 3, 7, 3), (41, 5, 3, 3), (43, 23, 3, 3), (47, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c92144a1_cert1 : certAll 0 1 0 (-1056) 12916 [(53, 3, 29, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 19, 3), (73, 19, 3, 3), (79, 3, 7, 3), (83, 7, 3, 3), (89, 5, 3, 3), (97, 5, 3, 3)] = true := by decide +kernel
theorem c92144a1_gens : allOn 0 1 0 (-1056) 12916 [(2, 104, 1), (18, 8, 1), (12, 46, 1)] = true := by decide +kernel

-- 92437a1: 21 primes
set_option maxHeartbeats 0 in
theorem c92437a1_cert0 : certAll 0 (-1) 1 (-24) (-36) [(5, 7, 2, 7), (7, 2, 29, 3), (11, 2, 17, 5), (13, 3, 2, 3), (17, 3, 2, 3), (19, 2, 7, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 17, 2, 3), (41, 3, 2, 3), (43, 2, 7, 3), (53, 7, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c92437a1_cert1 : certAll 0 (-1) 1 (-24) (-36) [(59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 3, 3), (73, 3, 2, 3), (79, 2, 7, 3), (83, 2, 17, 3), (89, 7, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c92437a1_gens : allOn 0 (-1) 1 (-24) (-36) [((-2), 0, 1), ((-3), 0, 1), ((-22), 7, 8)] = true := by decide +kernel

-- 92437b1: 20 primes
set_option maxHeartbeats 0 in
theorem c92437b1_cert0 : certAll 0 (-1) 1 (-2158) 38530 [(7, 2, 17, 3), (11, 2, 19, 17), (17, 3, 2, 3), (19, 2, 7, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 17, 2, 3), (41, 3, 2, 3), (43, 2, 7, 3), (47, 2, 3, 3), (53, 7, 2, 3), (59, 2, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c92437b1_cert1 : certAll 0 (-1) 1 (-2158) 38530 [(61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 3, 3), (73, 3, 2, 3), (79, 2, 7, 3), (83, 2, 19, 3), (89, 7, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c92437b1_gens : allOn 0 (-1) 1 (-2158) 38530 [((-35), 264, 1), (34, 57, 1), ((-124), 13193, 64)] = true := by decide +kernel

-- 92480bb1: 19 primes
set_option maxHeartbeats 0 in
theorem c92480bb1_cert0 : certAll 0 1 0 (-521) 4279 [(7, 3, 29, 3), (11, 7, 3, 7), (13, 3, 7, 3), (19, 13, 3, 3), (29, 3, 13, 3), (31, 3, 7, 3), (37, 3, 7, 3), (41, 7, 3, 3), (43, 13, 3, 3), (47, 3, 19, 3), (53, 3, 13, 3), (59, 7, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c92480bb1_cert1 : certAll 0 1 0 (-521) 4279 [(61, 3, 7, 3), (67, 13, 3, 3), (73, 19, 3, 3), (79, 3, 7, 3), (83, 7, 3, 3), (89, 7, 3, 3), (97, 19, 3, 3)] = true := by decide +kernel
theorem c92480bb1_gens : allOn 0 1 0 (-521) 4279 [((-6), 85, 1), (9, 20, 1), (15, 8, 1), (11, 0, 1)] = true := by decide +kernel

-- 92553b1: 22 primes
set_option maxHeartbeats 0 in
theorem c92553b1_cert0 : certAll 1 1 1 (-22) (-40) [(5, 2, 17, 2), (7, 5, 11, 5), (11, 7, 2, 2), (17, 2, 23, 2), (19, 2, 7, 2), (23, 7, 2, 2), (29, 5, 2, 2), (31, 2, 5, 2), (37, 17, 2, 2), (41, 2, 11, 2), (43, 5, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c92553b1_cert1 : certAll 1 1 1 (-22) (-40) [(53, 7, 2, 2), (59, 2, 5, 2), (61, 2, 7, 2), (67, 11, 2, 2), (71, 7, 2, 2), (73, 2, 7, 2), (79, 5, 2, 2), (83, 2, 17, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c92553b1_gens : allOn 1 1 1 (-22) (-40) [((-4), 3, 1), ((-2), 0, 1), ((-3), 4, 1)] = true := by decide +kernel

-- 92601a1: 21 primes
set_option maxHeartbeats 0 in
theorem c92601a1_cert0 : certAll 0 0 1 33 216 [(5, 7, 2, 7), (7, 2, 29, 5), (13, 17, 2, 5), (17, 7, 2, 5), (19, 2, 7, 5), (23, 2, 29, 5), (29, 7, 2, 5), (31, 2, 7, 5), (37, 17, 2, 5), (41, 7, 2, 7), (43, 2, 7, 5), (47, 2, 23, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c92601a1_cert1 : certAll 0 0 1 33 216 [(53, 7, 2, 5), (59, 2, 17, 5), (61, 17, 2, 5), (67, 2, 7, 5), (71, 2, 23, 5), (73, 23, 2, 5), (83, 2, 17, 5), (89, 7, 2, 5), (97, 29, 2, 5)] = true := by decide +kernel
theorem c92601a1_gens : allOn 0 0 1 33 216 [((-4), 4, 1), (5, 22, 1), ((-1), 13, 1)] = true := by decide +kernel

-- 92651a1: 21 primes
set_option maxHeartbeats 0 in
theorem c92651a1_cert0 : certAll 0 (-1) 1 (-14) 30 [(5, 71, 2, 107), (7, 2, 11, 3), (11, 2, 7, 5), (17, 3, 2, 3), (23, 2, 3, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 7, 2, 3), (41, 3, 2, 3), (43, 2, 7, 3), (47, 2, 3, 3), (53, 7, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c92651a1_cert1 : certAll 0 (-1) 1 (-14) 30 [(59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 3, 3), (73, 3, 2, 3), (79, 2, 17, 3), (83, 2, 7, 3), (89, 7, 2, 3), (97, 7, 2, 3)] = true := by decide +kernel
theorem c92651a1_gens : allOn 0 (-1) 1 (-14) 30 [(2, 2, 1), (3, 2, 1), (0, 5, 1)] = true := by decide +kernel

-- 92869d1: 20 primes
set_option maxHeartbeats 0 in
theorem c92869d1_cert0 : certAll 0 (-1) 1 (-574) 5440 [(5, 11, 2, 13), (11, 2, 13, 5), (13, 3, 2, 3), (17, 3, 2, 3), (19, 2, 11, 3), (23, 2, 3, 3), (31, 2, 3, 3), (37, 11, 2, 3), (41, 3, 2, 3), (43, 2, 11, 3), (47, 2, 3, 3), (53, 11, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c92869d1_cert1 : certAll 0 (-1) 1 (-574) 5440 [(59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (73, 3, 2, 3), (79, 2, 13, 3), (83, 2, 11, 3), (89, 13, 2, 3), (97, 19, 2, 3)] = true := by decide +kernel
theorem c92869d1_gens : allOn 0 (-1) 1 (-574) 5440 [(10, 24, 1), ((-4), 87, 1), ((-11), 101, 1)] = true := by decide +kernel

-- 93087a1: 22 primes
set_option maxHeartbeats 0 in
theorem c93087a1_cert0 : certAll 0 0 1 (-18) (-15) [(5, 7, 13, 7), (7, 13, 5, 5), (11, 7, 5, 7), (13, 5, 7, 5), (17, 7, 5, 5), (19, 11, 7, 7), (23, 7, 5, 5), (29, 5, 11, 5), (31, 5, 7, 5), (37, 5, 7, 5), (41, 5, 13, 5), (43, 11, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c93087a1_cert1 : certAll 0 0 1 (-18) (-15) [(47, 7, 5, 5), (53, 5, 13, 5), (61, 11, 5, 5), (67, 5, 7, 5), (71, 5, 11, 5), (73, 19, 5, 5), (79, 5, 7, 5), (83, 7, 5, 5), (89, 5, 13, 5), (97, 5, 7, 5)] = true := by decide +kernel
theorem c93087a1_gens : allOn 0 0 1 (-18) (-15) [((-1), 1, 1), (5, 4, 1), ((-14), 23, 8)] = true := by decide +kernel

-- 93376c1: 23 primes
set_option maxHeartbeats 0 in
theorem c93376c1_cert0 : certAll 0 1 0 (-129) 415 [(5, 3, 17, 3), (7, 3, 11, 3), (11, 5, 3, 5), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c93376c1_cert1 : certAll 0 1 0 (-129) 415 [(47, 3, 11, 3), (53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 23, 3), (73, 23, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c93376c1_gens : allOn 0 1 0 (-129) 415 [(3, 8, 1), ((-13), 8, 1), (19, 72, 1)] = true := by decide +kernel

-- 93508b1: 22 primes
set_option maxHeartbeats 0 in
theorem c93508b1_cert0 : certAll 0 0 0 (-61) 181 [(5, 3, 7, 3), (7, 5, 3, 3), (11, 3, 7, 3), (13, 7, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 7, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 7, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c93508b1_cert1 : certAll 0 0 0 (-61) 181 [(47, 3, 7, 3), (53, 3, 5, 3), (59, 3, 11, 3), (61, 11, 3, 3), (67, 5, 3, 3), (71, 3, 17, 3), (73, 17, 3, 3), (79, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3)] = true := by decide +kernel
theorem c93508b1_gens : allOn 0 0 0 (-61) 181 [(5, 1, 1), (3, 5, 1), (4, 1, 1)] = true := by decide +kernel

-- 93545e1: 20 primes
set_option maxHeartbeats 0 in
theorem c93545e1_cert0 : certAll 0 0 1 (-67) 132 [(7, 2, 3, 3), (11, 2, 17, 3), (13, 11, 2, 3), (17, 3, 2, 3), (19, 2, 3, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 11, 2, 3), (41, 3, 2, 3), (43, 2, 3, 3), (47, 2, 11, 3), (59, 2, 19, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c93545e1_cert1 : certAll 0 0 1 (-67) 132 [(61, 19, 2, 3), (67, 2, 3, 3), (71, 2, 37, 3), (73, 19, 2, 3), (79, 2, 3, 3), (83, 2, 11, 3), (89, 3, 2, 3), (97, 11, 2, 3)] = true := by decide +kernel
theorem c93545e1_gens : allOn 0 0 1 (-67) 132 [(2, 2, 1), ((-8), 12, 1), ((-3), 17, 1)] = true := by decide +kernel

-- 93783a1: 21 primes
set_option maxHeartbeats 0 in
theorem c93783a1_cert0 : certAll 1 0 0 (-6002) 180009 [(5, 2, 7, 2), (7, 5, 19, 5), (11, 13, 2, 2), (13, 2, 17, 2), (17, 2, 11, 2), (19, 2, 11, 2), (23, 7, 2, 2), (29, 5, 2, 2), (31, 2, 5, 2), (37, 7, 2, 2), (41, 2, 11, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c93783a1_cert1 : certAll 1 0 0 (-6002) 180009 [(53, 11, 2, 2), (61, 2, 13, 2), (67, 7, 2, 2), (71, 7, 2, 2), (73, 2, 7, 2), (79, 5, 2, 2), (83, 2, 7, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c93783a1_gens : allOn 1 0 0 (-6002) 180009 [(49, 40, 1), (307, 5071, 1), (134, 2255, 8)] = true := by decide +kernel

-- 93814a1: 21 primes
set_option maxHeartbeats 0 in
theorem c93814a1_cert0 : certAll 1 1 0 (-196) 980 [(5, 41, 3, 47), (11, 5, 31, 5), (13, 3, 5, 3), (17, 3, 5, 3), (19, 3, 23, 3), (23, 5, 3, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 11, 3, 3), (41, 3, 5, 3), (47, 5, 3, 3), (53, 11, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c93814a1_cert1 : certAll 1 1 0 (-196) 980 [(59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 11, 3), (83, 3, 11, 3), (89, 11, 3, 3), (97, 23, 3, 3)] = true := by decide +kernel
theorem c93814a1_gens : allOn 1 1 0 (-196) 980 [(7, 0, 1), (8, (-2), 1), ((-7), 49, 1)] = true := by decide +kernel

-- 93904a1: 23 primes
set_option maxHeartbeats 0 in
theorem c93904a1_cert0 : certAll 0 1 0 (-104) 340 [(5, 3, 7, 3), (7, 3, 11, 3), (11, 5, 3, 5), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c93904a1_cert1 : certAll 0 1 0 (-104) 340 [(47, 3, 11, 3), (53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 13, 3), (73, 13, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c93904a1_gens : allOn 0 1 0 (-104) 340 [(2, 12, 1), (10, 20, 1), (4, 2, 1)] = true := by decide +kernel

-- 94064a1: 20 primes
set_option maxHeartbeats 0 in
theorem c94064a1_cert0 : certAll 0 0 0 (-187) 970 [(5, 3, 7, 3), (7, 5, 3, 3), (13, 7, 3, 3), (19, 5, 3, 3), (23, 3, 29, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 7, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3), (53, 3, 5, 3), (59, 3, 7, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c94064a1_cert1 : certAll 0 0 0 (-187) 970 [(61, 7, 3, 3), (67, 5, 3, 3), (71, 3, 23, 3), (73, 23, 3, 3), (79, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3), (97, 23, 3, 3)] = true := by decide +kernel
theorem c94064a1_gens : allOn 0 0 0 (-187) 970 [(9, 4, 1), (7, 2, 1), (1, 28, 1)] = true := by decide +kernel

-- 94259d1: 20 primes
set_option maxHeartbeats 0 in
theorem c94259d1_cert0 : certAll 0 (-1) 1 (-46262) 3848910 [(5, 17, 2, 17), (7, 2, 17, 3), (13, 3, 2, 3), (17, 3, 2, 3), (23, 2, 3, 3), (29, 3, 2, 3), (31, 2, 3, 3), (37, 7, 2, 3), (43, 2, 31, 3), (47, 2, 3, 3), (53, 23, 2, 3), (59, 2, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c94259d1_cert1 : certAll 0 (-1) 1 (-46262) 3848910 [(61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 3, 3), (73, 3, 2, 3), (79, 2, 7, 3), (83, 2, 7, 3), (89, 7, 2, 3), (97, 17, 2, 3)] = true := by decide +kernel
theorem c94259d1_gens : allOn 0 (-1) 1 (-46262) 3848910 [(180, 1149, 1), ((-183), 2480, 1), (1242, 4957, 8)] = true := by decide +kernel

-- 94281b1: 22 primes
set_option maxHeartbeats 0 in
theorem c94281b1_cert0 : certAll 0 (-1) 1 (-154) 3234 [(5, 17, 2, 17), (7, 2, 19, 5), (13, 7, 2, 5), (17, 7, 2, 5), (19, 2, 17, 13), (23, 2, 37, 5), (29, 17, 2, 5), (31, 2, 7, 5), (37, 7, 2, 5), (41, 7, 2, 5), (43, 2, 17, 5), (47, 2, 29, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c94281b1_cert1 : certAll 0 (-1) 1 (-154) 3234 [(53, 17, 2, 5), (59, 2, 7, 5), (61, 7, 2, 5), (67, 2, 17, 5), (71, 2, 23, 5), (73, 23, 2, 5), (79, 2, 7, 5), (83, 2, 7, 5), (89, 7, 2, 5), (97, 23, 2, 5)] = true := by decide +kernel
theorem c94281b1_gens : allOn 0 (-1) 1 (-154) 3234 [((-3), 60, 1), ((-14), 49, 1), (63, 489, 1)] = true := by decide +kernel

-- 94659a1: 21 primes
set_option maxHeartbeats 0 in
theorem c94659a1_cert0 : certAll 0 (-1) 1 (-63) 380 [(7, 13, 11, 13), (11, 13, 7, 7), (13, 7, 19, 7), (17, 19, 7, 7), (19, 13, 17, 13), (23, 13, 7, 7), (29, 7, 13, 7), (31, 7, 19, 7), (37, 7, 13, 7), (41, 7, 13, 7), (43, 13, 7, 7), (47, 13, 7, 7)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c94659a1_cert1 : certAll 0 (-1) 1 (-63) 380 [(53, 7, 13, 7), (59, 7, 17, 11), (61, 17, 7, 7), (67, 7, 17, 7), (71, 7, 29, 7), (73, 37, 7, 7), (83, 13, 7, 7), (89, 7, 13, 7), (97, 7, 13, 7)] = true := by decide +kernel
theorem c94659a1_gens : allOn 0 (-1) 1 (-63) 380 [(36, 208, 1), (10, 135, 8), (0, 19, 1)] = true := by decide +kernel

-- 94715b1: 19 primes
set_option maxHeartbeats 0 in
theorem c94715b1_cert0 : certAll 0 0 1 (-268) (-1527) [(7, 13, 3, 3), (11, 3, 13, 3), (13, 11, 3, 3), (17, 3, 13, 3), (23, 3, 11, 3), (37, 13, 3, 3), (41, 3, 13, 3), (43, 23, 3, 3), (47, 3, 13, 3), (53, 3, 11, 3), (59, 3, 13, 3), (61, 11, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c94715b1_cert1 : certAll 0 0 1 (-268) (-1527) [(67, 23, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 17, 3, 3), (83, 3, 13, 3), (89, 3, 17, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c94715b1_gens : allOn 0 0 1 (-268) (-1527) [((-9), 12, 1), ((-11), 9, 1), ((-476), 443, 64)] = true := by decide +kernel

-- 94739a1: 22 primes
set_option maxHeartbeats 0 in
theorem c94739a1_cert0 : certAll 1 0 1 (-4530) 116957 [(5, 2, 7, 2), (7, 3, 11, 3), (11, 13, 2, 2), (13, 2, 11, 2), (17, 2, 3, 2), (19, 2, 3, 2), (29, 3, 2, 2), (31, 2, 5, 2), (37, 3, 2, 2), (41, 2, 3, 2), (43, 5, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c94739a1_cert1 : certAll 1 0 1 (-4530) 116957 [(53, 3, 2, 2), (59, 2, 3, 2), (61, 2, 7, 2), (67, 7, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (83, 2, 3, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c94739a1_gens : allOn 1 0 1 (-4530) 116957 [(310, (-161), 8), (37, 0, 1), (1047, (-538), 27)] = true := by decide +kernel

-- 95134d1: 21 primes
set_option maxHeartbeats 0 in
theorem c95134d1_cert0 : certAll 1 0 0 (-4145) 105961 [(5, 3, 23, 3), (7, 3, 23, 3), (11, 5, 3, 17), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 23, 3), (53, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c95134d1_cert1 : certAll 1 0 0 (-4145) 105961 [(59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c95134d1_gens : allOn 1 0 0 (-4145) 105961 [((-54), 443, 1), (10, 251, 1), (42, 59, 1)] = true := by decide +kernel

-- 95227g1: 22 primes
set_option maxHeartbeats 0 in
theorem c95227g1_cert0 : certAll 1 1 1 (-184) 870 [(5, 2, 3, 2), (7, 3, 19, 3), (13, 2, 5, 2), (17, 2, 5, 2), (19, 2, 23, 2), (23, 5, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 7, 2, 2), (41, 2, 5, 2), (43, 3, 2, 2), (47, 2, 3, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c95227g1_cert1 : certAll 1 1 1 (-184) 870 [(53, 23, 2, 2), (59, 2, 3, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 5, 2, 2), (73, 2, 5, 2), (79, 3, 2, 2), (83, 2, 7, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c95227g1_gens : allOn 1 1 1 (-184) 870 [(6, 2, 1), ((-16), 2, 1), ((-18), 291, 8)] = true := by decide +kernel

-- 95323b1: 20 primes
set_option maxHeartbeats 0 in
theorem c95323b1_cert0 : certAll 1 (-1) 1 (-532) 4600 [(5, 2, 37, 2), (7, 5, 11, 5), (11, 5, 2, 2), (13, 2, 5, 2), (17, 2, 5, 2), (23, 5, 2, 2), (31, 2, 7, 2), (37, 11, 2, 2), (41, 2, 5, 2), (43, 5, 2, 2), (53, 7, 2, 2), (59, 2, 17, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c95323b1_cert1 : certAll 1 (-1) 1 (-532) 4600 [(61, 2, 5, 2), (67, 5, 2, 2), (71, 5, 2, 2), (73, 2, 5, 2), (79, 5, 2, 2), (83, 2, 11, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c95323b1_gens : allOn 1 (-1) 1 (-532) 4600 [(8, 24, 1), (10, 9, 1), (444, 40, 27)] = true := by decide +kernel

-- 95887b1: 19 primes
set_option maxHeartbeats 0 in
theorem c95887b1_cert0 : certAll 0 1 1 (-100) 350 [(5, 3, 2, 3), (7, 2, 13, 3), (13, 3, 2, 3), (17, 7, 2, 3), (19, 2, 3, 3), (31, 2, 7, 3), (37, 3, 2, 3), (41, 7, 2, 3), (43, 2, 3, 3), (47, 2, 17, 3), (53, 3, 2, 3), (59, 2, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c95887b1_cert1 : certAll 0 1 1 (-100) 350 [(61, 3, 2, 3), (71, 2, 37, 3), (73, 37, 2, 3), (79, 2, 7, 3), (83, 2, 3, 3), (89, 7, 2, 3), (97, 17, 2, 3)] = true := by decide +kernel
theorem c95887b1_gens : allOn 0 1 1 (-100) 350 [(4, 5, 1), (5, 0, 1), (6, 1, 1)] = true := by decide +kernel

-- 95954c1: 19 primes
set_option maxHeartbeats 0 in
theorem c95954c1_cert0 : certAll 1 1 0 (-190) 932 [(7, 3, 19, 3), (11, 13, 7, 7), (13, 3, 19, 3), (17, 3, 13, 3), (19, 3, 17, 3), (23, 7, 3, 3), (29, 3, 7, 3), (31, 11, 3, 3), (37, 7, 3, 3), (47, 7, 3, 3), (53, 17, 3, 3), (61, 3, 13, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c95954c1_cert1 : certAll 1 1 0 (-190) 932 [(67, 7, 3, 3), (71, 7, 3, 3), (73, 3, 7, 3), (79, 3, 7, 3), (83, 3, 7, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c95954c1_gens : allOn 1 1 0 (-190) 932 [(8, (-6), 1), (7, (-1), 1), (62, (-33), 8)] = true := by decide +kernel

-- 96153a1: 21 primes
set_option maxHeartbeats 0 in
theorem c96153a1_cert0 : certAll 1 1 1 (-172) 800 [(5, 2, 7, 2), (7, 5, 17, 5), (11, 13, 2, 2), (13, 2, 19, 2), (17, 2, 7, 2), (19, 2, 17, 2), (29, 5, 2, 2), (31, 2, 5, 2), (37, 7, 2, 2), (41, 2, 13, 2), (43, 5, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c96153a1_cert1 : certAll 1 1 1 (-172) 800 [(53, 7, 2, 2), (59, 2, 5, 2), (61, 2, 7, 2), (71, 7, 2, 2), (73, 2, 7, 2), (79, 5, 2, 2), (83, 2, 7, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c96153a1_gens : allOn 1 1 1 (-172) 800 [(8, 0, 1), (7, (-2), 1), (46, 27, 8)] = true := by decide +kernel

-- 96163a1: 21 primes
set_option maxHeartbeats 0 in
theorem c96163a1_cert0 : certAll 0 (-1) 1 (-274) 1666 [(5, 17, 2, 17), (7, 2, 17, 3), (11, 2, 7, 5), (13, 3, 2, 3), (17, 3, 2, 3), (19, 2, 17, 3), (29, 3, 2, 3), (31, 2, 3, 3), (41, 3, 2, 3), (43, 2, 7, 3), (47, 2, 3, 3), (53, 7, 2, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c96163a1_cert1 : certAll 0 (-1) 1 (-274) 1666 [(59, 2, 3, 3), (61, 3, 2, 3), (67, 2, 3, 3), (71, 2, 3, 3), (73, 3, 2, 3), (79, 2, 11, 3), (83, 2, 7, 3), (89, 7, 2, 3), (97, 7, 2, 3)] = true := by decide +kernel
theorem c96163a1_gens : allOn 0 (-1) 1 (-274) 1666 [((-7), 56, 1), (13, 11, 1), (489, 1286, 27)] = true := by decide +kernel

-- 96266d1: 21 primes
set_option maxHeartbeats 0 in
theorem c96266d1_cert0 : certAll 1 0 0 (-145) 681 [(5, 3, 17, 3), (7, 3, 13, 3), (11, 5, 3, 7), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 37, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c96266d1_cert1 : certAll 1 0 0 (-145) 681 [(53, 3, 5, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 23, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 23, 3, 3)] = true := by decide +kernel
theorem c96266d1_gens : allOn 1 0 0 (-145) 681 [(10, 11, 1), (6, 3, 1), (2, 19, 1)] = true := by decide +kernel

-- 96376b1: 19 primes
set_option maxHeartbeats 0 in
theorem c96376b1_cert0 : certAll 0 0 0 (-367) 2770 [(5, 3, 43, 3), (11, 3, 17, 3), (13, 11, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 11, 3), (31, 5, 3, 3), (37, 11, 3, 3), (43, 5, 3, 3), (47, 3, 11, 3), (53, 3, 5, 3), (59, 3, 17, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c96376b1_cert1 : certAll 0 0 0 (-367) 2770 [(67, 5, 3, 3), (71, 3, 23, 3), (73, 19, 3, 3), (79, 5, 3, 3), (83, 3, 11, 3), (89, 3, 5, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c96376b1_gens : allOn 0 0 0 (-367) 2770 [(13, 14, 1), ((-15), 70, 1), (27, 112, 1)] = true := by decide +kernel

-- 96466b1: 23 primes
set_option maxHeartbeats 0 in
theorem c96466b1_cert0 : certAll 1 0 1 (-12) 20 [(5, 3, 13, 3), (7, 3, 17, 3), (11, 5, 3, 5), (13, 3, 5, 3), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 19, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c96466b1_cert1 : certAll 1 0 1 (-12) 20 [(47, 3, 11, 3), (53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 17, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c96466b1_gens : allOn 1 0 1 (-12) 20 [(2, 1, 1), (0, 4, 1), (4, 4, 1)] = true := by decide +kernel

-- 96544a1: 21 primes
set_option maxHeartbeats 0 in
theorem c96544a1_cert0 : certAll 0 (-1) 0 (-362) 2776 [(5, 17, 3, 17), (11, 13, 17, 13), (13, 3, 19, 3), (17, 3, 11, 3), (19, 3, 17, 3), (23, 13, 3, 3), (29, 3, 13, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 13, 3), (43, 3, 11, 3), (47, 13, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c96544a1_cert1 : certAll 0 (-1) 0 (-362) 2776 [(53, 11, 3, 3), (59, 11, 3, 3), (61, 3, 11, 3), (67, 11, 3, 3), (71, 11, 3, 3), (79, 3, 23, 3), (83, 3, 11, 3), (89, 11, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c96544a1_gens : allOn 0 (-1) 0 (-362) 2776 [(6, 28, 1), (12, 4, 1), (11, 2, 1)] = true := by decide +kernel

-- 96873a1: 22 primes
set_option maxHeartbeats 0 in
theorem c96873a1_cert0 : certAll 1 1 1 (-1422) 20040 [(5, 2, 13, 2), (11, 23, 2, 2), (13, 2, 17, 2), (17, 2, 11, 2), (19, 2, 11, 2), (23, 11, 2, 2), (29, 5, 2, 2), (31, 2, 5, 2), (37, 11, 2, 2), (41, 2, 11, 2), (43, 5, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c96873a1_cert1 : certAll 1 1 1 (-1422) 20040 [(53, 11, 2, 2), (59, 2, 5, 2), (61, 2, 23, 2), (67, 19, 2, 2), (71, 11, 2, 2), (73, 2, 11, 2), (79, 5, 2, 2), (83, 2, 11, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c96873a1_gens : allOn 1 1 1 (-1422) 20040 [(13, 56, 1), (20, 0, 1), (230, 385, 8)] = true := by decide +kernel

-- 96937a1: 18 primes
set_option maxHeartbeats 0 in
theorem c96937a1_cert0 : certAll 1 1 1 (-170) 996 [(5, 2, 3, 2), (7, 3, 17, 3), (11, 5, 2, 2), (13, 2, 5, 2), (17, 2, 5, 2), (19, 2, 11, 2), (23, 5, 2, 2), (29, 3, 2, 2), (37, 7, 2, 2), (41, 2, 5, 2), (61, 2, 5, 2), (67, 5, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c96937a1_cert1 : certAll 1 1 1 (-170) 996 [(71, 5, 2, 2), (73, 2, 5, 2), (79, 3, 2, 2), (83, 2, 7, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c96937a1_gens : allOn 1 1 1 (-170) 996 [(6, 12, 1), ((-14), 36, 1), ((-24), 913, 27)] = true := by decide +kernel

-- 97111a1: 21 primes
set_option maxHeartbeats 0 in
theorem c97111a1_cert0 : certAll 1 (-1) 1 (-541) 4982 [(5, 2, 13, 2), (11, 5, 2, 2), (13, 2, 5, 2), (17, 2, 5, 2), (19, 2, 17, 2), (23, 5, 2, 2), (29, 23, 2, 2), (31, 2, 29, 2), (37, 11, 2, 2), (43, 5, 2, 2), (47, 2, 11, 2), (53, 11, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c97111a1_cert1 : certAll 1 (-1) 1 (-541) 4982 [(59, 2, 17, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 5, 2, 2), (73, 2, 5, 2), (79, 5, 2, 2), (83, 2, 11, 2), (89, 2, 5, 2), (97, 2, 5, 2)] = true := by decide +kernel
theorem c97111a1_gens : allOn 1 (-1) 1 (-541) 4982 [(24, 61, 1), (94, 47, 8), ((-25), 61, 1)] = true := by decide +kernel

-- 97345d1: 21 primes
set_option maxHeartbeats 0 in
theorem c97345d1_cert0 : certAll 1 (-1) 1 (-927) 10926 [(7, 13, 3, 3), (11, 3, 2, 2), (13, 2, 3, 2), (17, 2, 13, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 13, 2, 2), (41, 2, 11, 2), (43, 11, 2, 2), (47, 2, 11, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c97345d1_cert1 : certAll 1 (-1) 1 (-927) 10926 [(53, 3, 2, 2), (59, 2, 11, 2), (61, 2, 3, 2), (67, 11, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (83, 2, 13, 2), (89, 2, 11, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c97345d1_gens : allOn 1 (-1) 1 (-927) 10926 [(26, 49, 1), (1, 99, 1), (158, (-33), 8)] = true := by decide +kernel

-- 97389a1: 22 primes
set_option maxHeartbeats 0 in
theorem c97389a1_cert0 : certAll 0 0 1 (-93) 342 [(5, 7, 2, 7), (7, 2, 5, 5), (11, 2, 5, 7), (13, 5, 2, 5), (17, 7, 2, 5), (19, 2, 7, 7), (23, 2, 5, 5), (29, 5, 2, 5), (31, 2, 7, 5), (37, 5, 2, 5), (41, 5, 2, 5), (43, 2, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c97389a1_cert1 : certAll 0 0 1 (-93) 342 [(47, 2, 5, 5), (53, 5, 2, 5), (59, 2, 17, 5), (67, 2, 7, 5), (71, 2, 11, 5), (73, 11, 2, 5), (79, 2, 7, 5), (83, 2, 5, 5), (89, 5, 2, 5), (97, 5, 2, 5)] = true := by decide +kernel
theorem c97389a1_gens : allOn 0 0 1 (-93) 342 [(5, 1, 1), (8, 10, 1), (6, 0, 1)] = true := by decide +kernel

-- 97408a1: 23 primes
set_option maxHeartbeats 0 in
theorem c97408a1_cert0 : certAll 0 0 0 (-52) (-80) [(5, 3, 7, 3), (7, 5, 3, 3), (11, 3, 7, 3), (13, 7, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 7, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c97408a1_cert1 : certAll 0 0 0 (-52) (-80) [(47, 3, 17, 3), (53, 3, 5, 3), (59, 3, 7, 3), (61, 7, 3, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 5, 3, 3), (83, 3, 7, 3), (89, 3, 5, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c97408a1_gens : allOn 0 0 0 (-52) (-80) [((-2), 4, 1), ((-6), 4, 1), ((-4), 8, 1)] = true := by decide +kernel

-- 97423a1: 23 primes
set_option maxHeartbeats 0 in
theorem c97423a1_cert0 : certAll 1 0 0 (-4) 15 [(5, 2, 7, 2), (7, 3, 29, 3), (11, 5, 2, 2), (13, 2, 5, 2), (17, 2, 3, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 7, 2), (37, 3, 2, 2), (41, 2, 3, 2), (43, 5, 2, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c97423a1_cert1 : certAll 1 0 0 (-4) 15 [(47, 2, 11, 2), (53, 3, 2, 2), (59, 2, 3, 2), (61, 2, 5, 2), (67, 5, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 3, 2, 2), (83, 2, 3, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c97423a1_gens : allOn 1 0 0 (-4) 15 [(1, 3, 1), (2, 3, 1), ((-2), 5, 1)] = true := by decide +kernel

-- 97506a1: 22 primes
set_option maxHeartbeats 0 in
theorem c97506a1_cert0 : certAll 1 (-1) 0 (-51) 133 [(5, 7, 17, 7), (7, 5, 11, 5), (11, 7, 23, 7), (13, 5, 7, 5), (17, 5, 11, 5), (19, 5, 7, 5), (23, 7, 5, 5), (29, 5, 17, 7), (31, 11, 5, 5), (37, 11, 5, 5), (41, 5, 17, 5), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c97506a1_cert1 : certAll 1 (-1) 0 (-51) 133 [(47, 7, 5, 5), (53, 7, 5, 5), (59, 7, 5, 5), (61, 5, 7, 5), (67, 11, 5, 5), (71, 7, 5, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c97506a1_gens : allOn 1 (-1) 0 (-51) 133 [(2, 5, 1), (6, 1, 1), (3, (-2), 1)] = true := by decide +kernel

-- 97543a1: 20 primes
set_option maxHeartbeats 0 in
theorem c97543a1_cert0 : certAll 1 1 1 (-23) 30 [(7, 3, 31, 3), (11, 13, 2, 2), (13, 2, 19, 2), (19, 2, 13, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 7, 2, 2), (41, 2, 19, 2), (43, 3, 2, 2), (47, 2, 3, 2), (53, 13, 2, 2), (59, 2, 3, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c97543a1_cert1 : certAll 1 1 1 (-23) 30 [(61, 2, 13, 2), (67, 7, 2, 2), (71, 7, 2, 2), (73, 2, 7, 2), (79, 3, 2, 2), (83, 2, 7, 2), (89, 2, 3, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c97543a1_gens : allOn 1 1 1 (-23) 30 [(3, (-3), 1), (0, 5, 1), (6, 9, 1)] = true := by decide +kernel

-- 97668f1: 21 primes
set_option maxHeartbeats 0 in
theorem c97668f1_cert0 : certAll 0 0 0 (-117) 405 [(5, 11, 7, 17), (7, 5, 13, 5), (11, 5, 7, 7), (13, 7, 5, 5), (17, 13, 5, 5), (19, 5, 11, 5), (23, 5, 7, 5), (29, 7, 5, 5), (31, 5, 13, 5), (37, 7, 5, 5), (41, 7, 5, 7), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c97668f1_cert1 : certAll 0 0 0 (-117) 405 [(53, 7, 5, 5), (59, 5, 11, 5), (61, 11, 5, 5), (67, 5, 11, 5), (73, 17, 5, 5), (79, 5, 13, 5), (83, 5, 7, 5), (89, 7, 5, 5), (97, 7, 5, 5)] = true := by decide +kernel
theorem c97668f1_gens : allOn 0 0 0 (-117) 405 [(3, 9, 1), (9, 9, 1), ((-9), 27, 1)] = true := by decide +kernel

-- 97782a1: 21 primes
set_option maxHeartbeats 0 in
theorem c97782a1_cert0 : certAll 1 1 0 2 484 [(5, 7, 13, 7), (7, 11, 5, 5), (11, 7, 5, 7), (13, 5, 7, 5), (17, 7, 5, 5), (19, 13, 7, 7), (23, 7, 5, 5), (29, 5, 13, 5), (31, 5, 7, 5), (37, 5, 7, 5), (41, 5, 11, 5), (47, 7, 5, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c97782a1_cert1 : certAll 1 1 0 2 484 [(53, 5, 13, 5), (59, 5, 11, 5), (61, 11, 5, 5), (67, 5, 7, 5), (73, 19, 5, 5), (79, 5, 7, 5), (83, 7, 5, 5), (89, 5, 11, 5), (97, 5, 7, 5)] = true := by decide +kernel
theorem c97782a1_gens : allOn 1 1 0 2 484 [((-3), 23, 1), (40, 238, 1), (62, 227, 8)] = true := by decide +kernel

-- 97811a1: 20 primes
set_option maxHeartbeats 0 in
theorem c97811a1_cert0 : certAll 1 (-1) 1 (-963) 11748 [(5, 2, 13, 2), (11, 3, 2, 2), (13, 2, 3, 2), (17, 2, 5, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 5, 2, 2), (41, 2, 13, 2), (43, 13, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c97811a1_cert1 : certAll 1 (-1) 1 (-963) 11748 [(53, 3, 2, 2), (59, 2, 17, 2), (67, 5, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 5, 2, 2), (83, 2, 5, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c97811a1_gens : allOn 1 (-1) 1 (-963) 11748 [(6, 75, 1), (18, (-6), 1), (2320, (-673), 125)] = true := by decide +kernel

-- 97834c1: 21 primes
set_option maxHeartbeats 0 in
theorem c97834c1_cert0 : certAll 1 1 0 (-4912) 130880 [(5, 7, 3, 7), (7, 3, 19, 3), (13, 3, 5, 3), (17, 3, 5, 3), (19, 3, 7, 3), (23, 5, 3, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 17, 3, 3), (41, 3, 5, 3), (43, 3, 7, 3), (47, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c97834c1_cert1 : certAll 1 1 0 (-4912) 130880 [(53, 7, 3, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 7, 3), (83, 3, 17, 3), (97, 19, 3, 3)] = true := by decide +kernel
theorem c97834c1_gens : allOn 1 1 0 (-4912) 130880 [(32, 72, 1), ((-56), 512, 1), (40, 0, 1)] = true := by decide +kernel

-- 97877a1: 22 primes
set_option maxHeartbeats 0 in
theorem c97877a1_cert0 : certAll 1 (-1) 1 (-54) 174 [(5, 2, 7, 2), (7, 5, 3, 3), (11, 3, 2, 2), (17, 2, 19, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 7, 2, 2), (41, 2, 17, 2), (43, 5, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c97877a1_cert1 : certAll 1 (-1) 1 (-54) 174 [(53, 3, 2, 2), (59, 2, 5, 2), (61, 2, 3, 2), (67, 7, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 5, 2, 2), (83, 2, 7, 2), (89, 2, 5, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c97877a1_gens : allOn 1 (-1) 1 (-54) 174 [(6, 3, 1), ((-7), 16, 1), (22, 37, 8)] = true := by decide +kernel

-- 98081a1: 20 primes
set_option maxHeartbeats 0 in
theorem c98081a1_cert0 : certAll 1 (-1) 1 (-129) 594 [(5, 2, 13, 2), (7, 5, 3, 3), (11, 3, 2, 2), (13, 2, 3, 2), (17, 2, 11, 2), (19, 2, 3, 2), (23, 3, 2, 2), (31, 2, 3, 2), (37, 11, 2, 2), (41, 2, 11, 2), (43, 5, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c98081a1_cert1 : certAll 1 (-1) 1 (-129) 594 [(53, 3, 2, 2), (61, 2, 3, 2), (67, 17, 2, 2), (73, 2, 3, 2), (79, 5, 2, 2), (83, 2, 11, 2), (89, 2, 5, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c98081a1_gens : allOn 1 (-1) 1 (-129) 594 [(7, (-5), 1), (6, 0, 1), (4, 9, 1)] = true := by decide +kernel

-- 98231a1: 20 primes
set_option maxHeartbeats 0 in
theorem c98231a1_cert0 : certAll 1 (-1) 1 1080 420 [(11, 3, 2, 2), (13, 2, 3, 2), (17, 2, 13, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 17, 2, 2), (41, 2, 13, 2), (43, 13, 2, 2), (47, 2, 17, 2), (59, 2, 19, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c98231a1_cert1 : certAll 1 (-1) 1 1080 420 [(61, 2, 3, 2), (67, 13, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 13, 2, 2), (83, 2, 17, 2), (89, 2, 13, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c98231a1_gens : allOn 1 (-1) 1 1080 420 [(12, 116, 1), (110, 1145, 1), (5, 74, 1)] = true := by decide +kernel

-- 98597a1: 22 primes
set_option maxHeartbeats 0 in
theorem c98597a1_cert0 : certAll 0 1 1 (-255) 1485 [(5, 3, 37, 3), (7, 3, 29, 3), (11, 5, 3, 7), (17, 7, 3, 3), (19, 5, 3, 3), (23, 3, 11, 3), (29, 3, 5, 3), (31, 3, 7, 3), (37, 3, 5, 3), (41, 7, 3, 3), (43, 5, 3, 3), (47, 3, 23, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c98597a1_cert1 : certAll 0 1 1 (-255) 1485 [(53, 3, 5, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 11, 3), (73, 11, 3, 3), (79, 3, 7, 3), (83, 5, 3, 3), (89, 7, 3, 3), (97, 11, 3, 3)] = true := by decide +kernel
theorem c98597a1_gens : allOn 0 1 1 (-255) 1485 [(9, 0, 1), (11, 11, 1), (3, 27, 1)] = true := by decide +kernel

-- 98730d1: 22 primes
set_option maxHeartbeats 0 in
theorem c98730d1_cert0 : certAll 1 (-1) 0 (-240) 1556 [(7, 13, 11, 13), (11, 7, 17, 13), (13, 11, 7, 7), (17, 7, 11, 7), (19, 13, 7, 7), (23, 7, 11, 7), (29, 7, 13, 7), (31, 11, 7, 7), (37, 11, 7, 7), (41, 7, 13, 7), (43, 13, 7, 7), (47, 7, 11, 7)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c98730d1_cert1 : certAll 1 (-1) 0 (-240) 1556 [(53, 7, 13, 7), (59, 7, 23, 7), (61, 41, 7, 7), (67, 11, 7, 7), (71, 7, 23, 7), (73, 23, 7, 7), (79, 11, 7, 7), (83, 7, 11, 7), (89, 7, 13, 7), (97, 11, 7, 7)] = true := by decide +kernel
theorem c98730d1_gens : allOn 1 (-1) 0 (-240) 1556 [((-2), 46, 1), (13, 16, 1), (8, 6, 1)] = true := by decide +kernel

-- 98841c1: 22 primes
set_option maxHeartbeats 0 in
theorem c98841c1_cert0 : certAll 0 1 1 (-114) 488 [(5, 7, 2, 7), (7, 2, 19, 5), (11, 2, 17, 5), (13, 11, 2, 5), (17, 7, 2, 5), (19, 2, 7, 7), (23, 2, 11, 5), (29, 7, 2, 5), (31, 2, 7, 5), (37, 17, 2, 5), (41, 7, 2, 5), (43, 2, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c98841c1_cert1 : certAll 0 1 1 (-114) 488 [(53, 7, 2, 5), (59, 2, 19, 5), (61, 11, 2, 5), (67, 2, 7, 5), (71, 2, 11, 5), (73, 11, 2, 5), (79, 2, 7, 5), (83, 2, 17, 5), (89, 7, 2, 5), (97, 11, 2, 5)] = true := by decide +kernel
theorem c98841c1_gens : allOn 0 1 1 (-114) 488 [(3, 13, 1), (12, 31, 1), (6, 7, 1)] = true := by decide +kernel

-- 98891a1: 22 primes
set_option maxHeartbeats 0 in
theorem c98891a1_cert0 : certAll 1 (-1) 1 6 12 [(5, 2, 7, 2), (7, 5, 3, 3), (11, 3, 2, 2), (17, 2, 19, 2), (19, 2, 3, 2), (23, 3, 2, 2), (29, 3, 2, 2), (31, 2, 3, 2), (37, 7, 2, 2), (41, 2, 11, 2), (43, 5, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c98891a1_cert1 : certAll 1 (-1) 1 6 12 [(53, 3, 2, 2), (59, 2, 5, 2), (61, 2, 3, 2), (67, 7, 2, 2), (71, 3, 2, 2), (73, 2, 3, 2), (79, 5, 2, 2), (83, 2, 7, 2), (89, 2, 5, 2), (97, 2, 3, 2)] = true := by decide +kernel
theorem c98891a1_gens : allOn 1 (-1) 1 6 12 [((-1), 2, 1), (0, 3, 1), (2, 4, 1)] = true := by decide +kernel

-- 99153b1: 21 primes
set_option maxHeartbeats 0 in
theorem c99153b1_cert0 : certAll 1 (-1) 1 67 (-120) [(5, 2, 13, 2), (7, 13, 5, 5), (11, 7, 2, 2), (13, 2, 7, 2), (17, 2, 5, 2), (19, 2, 7, 2), (29, 5, 2, 2), (31, 2, 7, 2), (37, 5, 2, 2), (41, 2, 13, 2), (43, 13, 2, 2), (47, 2, 5, 2)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c99153b1_cert1 : certAll 1 (-1) 1 67 (-120) [(53, 5, 2, 2), (59, 2, 31, 2), (67, 5, 2, 2), (71, 5, 2, 2), (73, 2, 5, 2), (79, 5, 2, 2), (83, 2, 5, 2), (89, 2, 13, 2), (97, 2, 7, 2)] = true := by decide +kernel
theorem c99153b1_gens : allOn 1 (-1) 1 67 (-120) [(5, 15, 1), (2, 3, 1), (20, 84, 1)] = true := by decide +kernel

-- 99248d1: 23 primes
set_option maxHeartbeats 0 in
theorem c99248d1_cert0 : certAll 0 0 0 8 60 [(5, 17, 7, 17), (7, 5, 43, 5), (11, 5, 7, 7), (13, 7, 5, 5), (17, 7, 5, 5), (19, 5, 17, 5), (23, 5, 19, 5), (29, 17, 5, 5), (31, 5, 7, 5), (37, 7, 5, 5), (41, 7, 5, 7), (43, 5, 17, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c99248d1_cert1 : certAll 0 0 0 8 60 [(47, 5, 11, 5), (53, 11, 5, 5), (59, 5, 7, 5), (61, 7, 5, 5), (67, 5, 17, 5), (71, 5, 11, 5), (73, 19, 5, 5), (79, 5, 7, 5), (83, 5, 7, 5), (89, 7, 5, 5), (97, 19, 5, 5)] = true := by decide +kernel
theorem c99248d1_gens : allOn 0 0 0 8 60 [((-2), 6, 1), (6, 18, 1), ((-3), 3, 1)] = true := by decide +kernel

-- 99326a1: 23 primes
set_option maxHeartbeats 0 in
theorem c99326a1_cert0 : certAll 1 (-1) 1 (-174) 957 [(5, 3, 13, 3), (7, 5, 3, 3), (11, 3, 17, 3), (13, 5, 3, 3), (17, 3, 11, 3), (19, 5, 3, 3), (23, 3, 5, 3), (29, 3, 11, 3), (31, 11, 3, 3), (37, 11, 3, 3), (41, 3, 13, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c99326a1_cert1 : certAll 1 (-1) 1 (-174) 957 [(47, 3, 5, 3), (53, 3, 5, 3), (59, 3, 5, 3), (61, 5, 3, 3), (67, 11, 3, 3), (71, 3, 5, 3), (73, 5, 3, 3), (79, 5, 3, 3), (83, 3, 11, 3), (89, 3, 5, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c99326a1_gens : allOn 1 (-1) 1 (-174) 957 [(9, 3, 1), (1, 27, 1), (5, 11, 1)] = true := by decide +kernel

-- 99378d1: 23 primes
set_option maxHeartbeats 0 in
theorem c99378d1_cert0 : certAll 1 (-1) 0 (-153) 841 [(5, 7, 13, 7), (7, 5, 11, 5), (11, 5, 13, 5), (13, 11, 5, 5), (17, 7, 5, 5), (19, 5, 7, 7), (23, 5, 11, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 11, 5, 5), (41, 7, 5, 5), (43, 5, 7, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c99378d1_cert1 : certAll 1 (-1) 0 (-153) 841 [(47, 5, 11, 5), (53, 7, 5, 5), (59, 5, 41, 5), (61, 13, 5, 5), (67, 5, 7, 5), (71, 5, 13, 5), (73, 13, 5, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 11, 5, 5)] = true := by decide +kernel
theorem c99378d1_gens : allOn 1 (-1) 0 (-153) 841 [(8, 5, 1), (5, 11, 1), (14, 29, 1)] = true := by decide +kernel

-- 99572b1: 19 primes
set_option maxHeartbeats 0 in
theorem c99572b1_cert0 : certAll 0 1 0 (-2606) 50353 [(5, 3, 13, 3), (7, 3, 5, 3), (13, 3, 7, 3), (17, 7, 3, 3), (19, 13, 3, 3), (23, 3, 5, 3), (29, 3, 13, 3), (37, 3, 7, 3), (41, 5, 3, 3), (43, 13, 3, 3), (47, 3, 5, 3), (59, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c99572b1_cert1 : certAll 0 1 0 (-2606) 50353 [(61, 3, 5, 3), (67, 5, 3, 3), (71, 3, 19, 3), (79, 3, 7, 3), (83, 7, 3, 3), (89, 5, 3, 3), (97, 5, 3, 3)] = true := by decide +kernel
theorem c99572b1_gens : allOn 0 1 0 (-2606) 50353 [(28, 11, 1), (94, 803, 1), (3720, 803, 125)] = true := by decide +kernel

-- 99776q1: 23 primes
set_option maxHeartbeats 0 in
theorem c99776q1_cert0 : certAll 0 (-1) 0 (-121) 569 [(5, 7, 3, 7), (7, 3, 5, 3), (11, 7, 5, 7), (13, 3, 7, 3), (17, 3, 5, 3), (19, 3, 7, 3), (23, 7, 3, 3), (29, 3, 11, 3), (31, 5, 3, 3), (37, 5, 3, 3), (41, 3, 19, 3), (43, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c99776q1_cert1 : certAll 0 (-1) 0 (-121) 569 [(47, 7, 3, 3), (53, 5, 3, 3), (59, 5, 3, 3), (61, 3, 5, 3), (67, 5, 3, 3), (71, 5, 3, 3), (73, 3, 5, 3), (79, 3, 7, 3), (83, 3, 5, 3), (89, 5, 3, 3), (97, 5, 3, 3)] = true := by decide +kernel
theorem c99776q1_gens : allOn 0 (-1) 0 (-121) 569 [(5, 8, 1), (7, 4, 1), (13, 32, 1)] = true := by decide +kernel

-- 99966a1: 21 primes
set_option maxHeartbeats 0 in
theorem c99966a1_cert0 : certAll 1 1 0 (-186) 900 [(5, 11, 17, 37), (7, 5, 17, 5), (11, 5, 29, 5), (17, 7, 5, 5), (19, 5, 7, 7), (23, 5, 31, 5), (29, 7, 5, 5), (31, 5, 7, 5), (37, 11, 5, 5), (41, 7, 5, 5), (43, 5, 7, 5), (47, 5, 23, 5)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c99966a1_cert1 : certAll 1 1 0 (-186) 900 [(53, 7, 5, 5), (61, 11, 5, 5), (67, 5, 7, 5), (71, 5, 17, 5), (73, 17, 5, 5), (79, 5, 7, 5), (83, 5, 11, 5), (89, 7, 5, 5), (97, 17, 5, 5)] = true := by decide +kernel
theorem c99966a1_gens : allOn 1 1 0 (-186) 900 [(8, (-2), 1), (12, 18, 1), (0, 30, 1)] = true := by decide +kernel

-- 99968j1: 21 primes
set_option maxHeartbeats 0 in
theorem c99968j1_cert0 : certAll 0 0 0 (-196) 976 [(5, 3, 37, 3), (7, 5, 3, 3), (13, 23, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 29, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 17, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3), (47, 3, 17, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c99968j1_cert1 : certAll 0 0 0 (-196) 976 [(53, 3, 5, 3), (59, 3, 17, 3), (61, 31, 3, 3), (67, 5, 3, 3), (73, 17, 3, 3), (79, 5, 3, 3), (83, 3, 17, 3), (89, 3, 5, 3), (97, 17, 3, 3)] = true := by decide +kernel
theorem c99968j1_gens : allOn 0 0 0 (-196) 976 [((-6), 44, 1), (16, 44, 1), (5, 11, 1)] = true := by decide +kernel

#print axioms c30064c1_cert0
#print axioms c30064c1_cert1
#print axioms c30064c1_gens
#print axioms c30148b1_cert0
#print axioms c30148b1_cert1
#print axioms c30148b1_gens
#print axioms c30376a1_cert0
#print axioms c30376a1_cert1
#print axioms c30376a1_gens
#print axioms c30446a1_cert0
#print axioms c30446a1_cert1
#print axioms c30446a1_gens
#print axioms c30487a1_cert0
#print axioms c30487a1_cert1
#print axioms c30487a1_gens
#print axioms c30767d1_cert0
#print axioms c30767d1_cert1
#print axioms c30767d1_gens
#print axioms c30815a1_cert0
#print axioms c30815a1_cert1
#print axioms c30815a1_gens
#print axioms c31478b1_cert0
#print axioms c31478b1_cert1
#print axioms c31478b1_gens
#print axioms c31737a1_cert0
#print axioms c31737a1_cert1
#print axioms c31737a1_gens
#print axioms c31814a1_cert0
#print axioms c31814a1_cert1
#print axioms c31814a1_gens
#print axioms c32192e1_cert0
#print axioms c32192e1_cert1
#print axioms c32192e1_gens
#print axioms c32244c1_cert0
#print axioms c32244c1_cert1
#print axioms c32244c1_gens
#print axioms c32276b1_cert0
#print axioms c32276b1_cert1
#print axioms c32276b1_gens
#print axioms c32336b1_cert0
#print axioms c32336b1_cert1
#print axioms c32336b1_gens
#print axioms c33424o1_cert0
#print axioms c33424o1_cert1
#print axioms c33424o1_gens
#print axioms c33428a1_cert0
#print axioms c33428a1_cert1
#print axioms c33428a1_gens
#print axioms c33509a1_cert0
#print axioms c33509a1_cert1
#print axioms c33509a1_gens
#print axioms c33609a1_cert0
#print axioms c33609a1_cert1
#print axioms c33609a1_gens
#print axioms c33709a1_cert0
#print axioms c33709a1_cert1
#print axioms c33709a1_gens
#print axioms c33914a1_cert0
#print axioms c33914a1_cert1
#print axioms c33914a1_gens
#print axioms c34415a1_cert0
#print axioms c34415a1_cert1
#print axioms c34415a1_gens
#print axioms c34862a1_cert0
#print axioms c34862a1_cert1
#print axioms c34862a1_gens
#print axioms c35003a1_cert0
#print axioms c35003a1_cert1
#print axioms c35003a1_gens
#print axioms c35083c1_cert0
#print axioms c35083c1_cert1
#print axioms c35083c1_gens
#print axioms c35234a1_cert0
#print axioms c35234a1_cert1
#print axioms c35234a1_gens
#print axioms c35243b1_cert0
#print axioms c35243b1_cert1
#print axioms c35243b1_gens
#print axioms c35882b1_cert0
#print axioms c35882b1_cert1
#print axioms c35882b1_gens
#print axioms c36094c1_cert0
#print axioms c36094c1_cert1
#print axioms c36094c1_gens
#print axioms c36739a1_cert0
#print axioms c36739a1_cert1
#print axioms c36739a1_gens
#print axioms c37229a1_cert0
#print axioms c37229a1_cert1
#print axioms c37229a1_gens
#print axioms c37544c1_cert0
#print axioms c37544c1_cert1
#print axioms c37544c1_gens
#print axioms c38439b1_cert0
#print axioms c38439b1_cert1
#print axioms c38439b1_gens
#print axioms c38600m1_cert0
#print axioms c38600m1_cert1
#print axioms c38600m1_gens
#print axioms c38601a1_cert0
#print axioms c38601a1_cert1
#print axioms c38601a1_gens
#print axioms c39023a1_cert0
#print axioms c39023a1_cert1
#print axioms c39023a1_gens
#print axioms c39077c1_cert0
#print axioms c39077c1_cert1
#print axioms c39077c1_gens
#print axioms c39289a1_cert0
#print axioms c39289a1_cert1
#print axioms c39289a1_gens
#print axioms c39883a1_cert0
#print axioms c39883a1_cert1
#print axioms c39883a1_gens
#print axioms c40331c1_cert0
#print axioms c40331c1_cert1
#print axioms c40331c1_gens
#print axioms c40929a1_cert0
#print axioms c40929a1_cert1
#print axioms c40929a1_gens
#print axioms c41001a1_cert0
#print axioms c41001a1_cert1
#print axioms c41001a1_gens
#print axioms c41107a1_cert0
#print axioms c41107a1_cert1
#print axioms c41107a1_gens
#print axioms c41406b1_cert0
#print axioms c41406b1_cert1
#print axioms c41406b1_gens
#print axioms c41775k1_cert0
#print axioms c41775k1_cert1
#print axioms c41775k1_gens
#print axioms c41785a1_cert0
#print axioms c41785a1_cert1
#print axioms c41785a1_gens
#print axioms c41933a1_cert0
#print axioms c41933a1_cert1
#print axioms c41933a1_gens
#print axioms c42093a1_cert0
#print axioms c42093a1_cert1
#print axioms c42093a1_gens
#print axioms c42153a1_cert0
#print axioms c42153a1_cert1
#print axioms c42153a1_gens
#print axioms c42190a1_cert0
#print axioms c42190a1_cert1
#print axioms c42190a1_gens
#print axioms c42264a1_cert0
#print axioms c42264a1_cert1
#print axioms c42264a1_gens
#print axioms c42384a1_cert0
#print axioms c42384a1_cert1
#print axioms c42384a1_gens
#print axioms c42526b1_cert0
#print axioms c42526b1_cert1
#print axioms c42526b1_gens
#print axioms c42528c1_cert0
#print axioms c42528c1_cert1
#print axioms c42528c1_gens
#print axioms c42584c1_cert0
#print axioms c42584c1_cert1
#print axioms c42584c1_gens
#print axioms c43556b1_cert0
#print axioms c43556b1_cert1
#print axioms c43556b1_gens
#print axioms c43669a1_cert0
#print axioms c43669a1_cert1
#print axioms c43669a1_gens
#print axioms c43730e1_cert0
#print axioms c43730e1_cert1
#print axioms c43730e1_gens
#print axioms c43976f1_cert0
#print axioms c43976f1_cert1
#print axioms c43976f1_gens
#print axioms c44012b1_cert0
#print axioms c44012b1_cert1
#print axioms c44012b1_gens
#print axioms c44233a1_cert0
#print axioms c44233a1_cert1
#print axioms c44233a1_gens
#print axioms c44409b1_cert0
#print axioms c44409b1_cert1
#print axioms c44409b1_gens
#print axioms c44755a1_cert0
#print axioms c44755a1_cert1
#print axioms c44755a1_gens
#print axioms c44755b1_cert0
#print axioms c44755b1_cert1
#print axioms c44755b1_gens
#print axioms c44794c1_cert0
#print axioms c44794c1_cert1
#print axioms c44794c1_gens
#print axioms c44860b1_cert0
#print axioms c44860b1_cert1
#print axioms c44860b1_gens
#print axioms c44869b1_cert0
#print axioms c44869b1_cert1
#print axioms c44869b1_gens
#print axioms c45123h1_cert0
#print axioms c45123h1_cert1
#print axioms c45123h1_gens
#print axioms c45352a1_cert0
#print axioms c45352a1_cert1
#print axioms c45352a1_gens
#print axioms c45985a1_cert0
#print axioms c45985a1_cert1
#print axioms c45985a1_gens
#print axioms c46024a1_cert0
#print axioms c46024a1_cert1
#print axioms c46024a1_gens
#print axioms c46222a1_cert0
#print axioms c46222a1_cert1
#print axioms c46222a1_gens
#print axioms c46307a1_cert0
#print axioms c46307a1_cert1
#print axioms c46307a1_gens
#print axioms c46462d1_cert0
#print axioms c46462d1_cert1
#print axioms c46462d1_gens
#print axioms c46672g1_cert0
#print axioms c46672g1_cert1
#print axioms c46672g1_gens
#print axioms c46896d1_cert0
#print axioms c46896d1_cert1
#print axioms c46896d1_gens
#print axioms c47087a1_cert0
#print axioms c47087a1_cert1
#print axioms c47087a1_gens
#print axioms c47440a1_cert0
#print axioms c47440a1_cert1
#print axioms c47440a1_gens
#print axioms c47453a1_cert0
#print axioms c47453a1_cert1
#print axioms c47453a1_gens
#print axioms c47696h1_cert0
#print axioms c47696h1_cert1
#print axioms c47696h1_gens
#print axioms c47976d1_cert0
#print axioms c47976d1_cert1
#print axioms c47976d1_gens
#print axioms c48272b1_cert0
#print axioms c48272b1_cert1
#print axioms c48272b1_gens
#print axioms c48434c1_cert0
#print axioms c48434c1_cert1
#print axioms c48434c1_gens
#print axioms c48444a1_cert0
#print axioms c48444a1_cert1
#print axioms c48444a1_gens
#print axioms c48734b1_cert0
#print axioms c48734b1_cert1
#print axioms c48734b1_gens
#print axioms c48746a1_cert0
#print axioms c48746a1_cert1
#print axioms c48746a1_gens
#print axioms c48856a1_cert0
#print axioms c48856a1_cert1
#print axioms c48856a1_gens
#print axioms c49183a1_cert0
#print axioms c49183a1_cert1
#print axioms c49183a1_gens
#print axioms c49259a1_cert0
#print axioms c49259a1_cert1
#print axioms c49259a1_gens
#print axioms c49411a1_cert0
#print axioms c49411a1_cert1
#print axioms c49411a1_gens
#print axioms c49626a1_cert0
#print axioms c49626a1_cert1
#print axioms c49626a1_gens
#print axioms c49648d1_cert0
#print axioms c49648d1_cert1
#print axioms c49648d1_gens
#print axioms c49831a1_cert0
#print axioms c49831a1_cert1
#print axioms c49831a1_gens
#print axioms c50029c1_cert0
#print axioms c50029c1_cert1
#print axioms c50029c1_gens
#print axioms c50121a1_cert0
#print axioms c50121a1_cert1
#print axioms c50121a1_gens
#print axioms c50360a1_cert0
#print axioms c50360a1_cert1
#print axioms c50360a1_gens
#print axioms c50382f1_cert0
#print axioms c50382f1_cert1
#print axioms c50382f1_gens
#print axioms c50744c1_cert0
#print axioms c50744c1_cert1
#print axioms c50744c1_gens
#print axioms c50862a1_cert0
#print axioms c50862a1_cert1
#print axioms c50862a1_gens
#print axioms c51034a1_cert0
#print axioms c51034a1_cert1
#print axioms c51034a1_gens
#print axioms c51052a1_cert0
#print axioms c51052a1_cert1
#print axioms c51052a1_gens
#print axioms c51065c1_cert0
#print axioms c51065c1_cert1
#print axioms c51065c1_gens
#print axioms c51094a1_cert0
#print axioms c51094a1_cert1
#print axioms c51094a1_gens
#print axioms c51317a1_cert0
#print axioms c51317a1_cert1
#print axioms c51317a1_gens
#print axioms c51536b1_cert0
#print axioms c51536b1_cert1
#print axioms c51536b1_gens
#print axioms c51822d1_cert0
#print axioms c51822d1_cert1
#print axioms c51822d1_gens
#print axioms c51962a1_cert0
#print axioms c51962a1_cert1
#print axioms c51962a1_gens
#print axioms c52013a1_cert0
#print axioms c52013a1_cert1
#print axioms c52013a1_gens
#print axioms c52158a1_cert0
#print axioms c52158a1_cert1
#print axioms c52158a1_gens
#print axioms c52277b1_cert0
#print axioms c52277b1_cert1
#print axioms c52277b1_gens
#print axioms c52396b1_cert0
#print axioms c52396b1_cert1
#print axioms c52396b1_gens
#print axioms c53022b1_cert0
#print axioms c53022b1_cert1
#print axioms c53022b1_gens
#print axioms c53083a1_cert0
#print axioms c53083a1_cert1
#print axioms c53083a1_gens
#print axioms c53122a1_cert0
#print axioms c53122a1_cert1
#print axioms c53122a1_gens
#print axioms c53237b1_cert0
#print axioms c53237b1_cert1
#print axioms c53237b1_gens
#print axioms c53238e1_cert0
#print axioms c53238e1_cert1
#print axioms c53238e1_gens
#print axioms c53461b1_cert0
#print axioms c53461b1_cert1
#print axioms c53461b1_gens
#print axioms c53486d1_cert0
#print axioms c53486d1_cert1
#print axioms c53486d1_gens
#print axioms c53916a1_cert0
#print axioms c53916a1_cert1
#print axioms c53916a1_gens
#print axioms c53926e1_cert0
#print axioms c53926e1_cert1
#print axioms c53926e1_gens
#print axioms c53957b1_cert0
#print axioms c53957b1_cert1
#print axioms c53957b1_gens
#print axioms c54489b1_cert0
#print axioms c54489b1_cert1
#print axioms c54489b1_gens
#print axioms c54512b1_cert0
#print axioms c54512b1_cert1
#print axioms c54512b1_gens
#print axioms c55064b1_cert0
#print axioms c55064b1_cert1
#print axioms c55064b1_gens
#print axioms c55783e1_cert0
#print axioms c55783e1_cert1
#print axioms c55783e1_gens
#print axioms c55846a1_cert0
#print axioms c55846a1_cert1
#print axioms c55846a1_gens
#print axioms c55935g1_cert0
#print axioms c55935g1_cert1
#print axioms c55935g1_gens
#print axioms c56052g1_cert0
#print axioms c56052g1_cert1
#print axioms c56052g1_gens
#print axioms c56441b1_cert0
#print axioms c56441b1_cert1
#print axioms c56441b1_gens
#print axioms c56982a1_cert0
#print axioms c56982a1_cert1
#print axioms c56982a1_gens
#print axioms c56982b1_cert0
#print axioms c56982b1_cert1
#print axioms c56982b1_gens
#print axioms c58397c1_cert0
#print axioms c58397c1_cert1
#print axioms c58397c1_gens
#print axioms c58739a1_cert0
#print axioms c58739a1_cert1
#print axioms c58739a1_gens
#print axioms c58774b1_cert0
#print axioms c58774b1_cert1
#print axioms c58774b1_gens
#print axioms c58939a1_cert0
#print axioms c58939a1_cert1
#print axioms c58939a1_gens
#print axioms c59111a1_cert0
#print axioms c59111a1_cert1
#print axioms c59111a1_gens
#print axioms c59450i1_cert0
#print axioms c59450i1_cert1
#print axioms c59450i1_gens
#print axioms c59614a1_cert0
#print axioms c59614a1_cert1
#print axioms c59614a1_gens
#print axioms c59704d1_cert0
#print axioms c59704d1_cert1
#print axioms c59704d1_gens
#print axioms c59936b1_cert0
#print axioms c59936b1_cert1
#print axioms c59936b1_gens
#print axioms c60055b1_cert0
#print axioms c60055b1_cert1
#print axioms c60055b1_gens
#print axioms c60128a1_cert0
#print axioms c60128a1_cert1
#print axioms c60128a1_gens
#print axioms c60215b1_cert0
#print axioms c60215b1_cert1
#print axioms c60215b1_gens
#print axioms c60296a1_cert0
#print axioms c60296a1_cert1
#print axioms c60296a1_gens
#print axioms c60803a1_cert0
#print axioms c60803a1_cert1
#print axioms c60803a1_gens
#print axioms c60892b1_cert0
#print axioms c60892b1_cert1
#print axioms c60892b1_gens
#print axioms c61025b1_cert0
#print axioms c61025b1_cert1
#print axioms c61025b1_gens
#print axioms c61075a1_cert0
#print axioms c61075a1_cert1
#print axioms c61075a1_gens
#print axioms c61229a1_cert0
#print axioms c61229a1_cert1
#print axioms c61229a1_gens
#print axioms c61376c1_cert0
#print axioms c61376c1_cert1
#print axioms c61376c1_gens
#print axioms c61504cg1_cert0
#print axioms c61504cg1_cert1
#print axioms c61504cg1_gens
#print axioms c61598c1_cert0
#print axioms c61598c1_cert1
#print axioms c61598c1_gens
#print axioms c61651a1_cert0
#print axioms c61651a1_cert1
#print axioms c61651a1_gens
#print axioms c61672b1_cert0
#print axioms c61672b1_cert1
#print axioms c61672b1_gens
#print axioms c61805c1_cert0
#print axioms c61805c1_cert1
#print axioms c61805c1_gens
#print axioms c61826a1_cert0
#print axioms c61826a1_cert1
#print axioms c61826a1_gens
#print axioms c61839b1_cert0
#print axioms c61839b1_cert1
#print axioms c61839b1_gens
#print axioms c61886d1_cert0
#print axioms c61886d1_cert1
#print axioms c61886d1_gens
#print axioms c61995a1_cert0
#print axioms c61995a1_cert1
#print axioms c61995a1_gens
#print axioms c62078c1_cert0
#print axioms c62078c1_cert1
#print axioms c62078c1_gens
#print axioms c62168c1_cert0
#print axioms c62168c1_cert1
#print axioms c62168c1_gens
#print axioms c62246b1_cert0
#print axioms c62246b1_cert1
#print axioms c62246b1_gens
#print axioms c62282a1_cert0
#print axioms c62282a1_cert1
#print axioms c62282a1_gens
#print axioms c62319c1_cert0
#print axioms c62319c1_cert1
#print axioms c62319c1_gens
#print axioms c62546a1_cert0
#print axioms c62546a1_cert1
#print axioms c62546a1_gens
#print axioms c62576b1_cert0
#print axioms c62576b1_cert1
#print axioms c62576b1_gens
#print axioms c62592c1_cert0
#print axioms c62592c1_cert1
#print axioms c62592c1_gens
#print axioms c62823b1_cert0
#print axioms c62823b1_cert1
#print axioms c62823b1_gens
#print axioms c63002h1_cert0
#print axioms c63002h1_cert1
#print axioms c63002h1_gens
#print axioms c63213b1_cert0
#print axioms c63213b1_cert1
#print axioms c63213b1_gens
#print axioms c63298c1_cert0
#print axioms c63298c1_cert1
#print axioms c63298c1_gens
#print axioms c63422h1_cert0
#print axioms c63422h1_cert1
#print axioms c63422h1_gens
#print axioms c63437a1_cert0
#print axioms c63437a1_cert1
#print axioms c63437a1_gens
#print axioms c63447a1_cert0
#print axioms c63447a1_cert1
#print axioms c63447a1_gens
#print axioms c63472g1_cert0
#print axioms c63472g1_cert1
#print axioms c63472g1_gens
#print axioms c63574d1_cert0
#print axioms c63574d1_cert1
#print axioms c63574d1_gens
#print axioms c63789c1_cert0
#print axioms c63789c1_cert1
#print axioms c63789c1_gens
#print axioms c63936o1_cert0
#print axioms c63936o1_cert1
#print axioms c63936o1_gens
#print axioms c64018h1_cert0
#print axioms c64018h1_cert1
#print axioms c64018h1_gens
#print axioms c64432d1_cert0
#print axioms c64432d1_cert1
#print axioms c64432d1_gens
#print axioms c64522c1_cert0
#print axioms c64522c1_cert1
#print axioms c64522c1_gens
#print axioms c64672h1_cert0
#print axioms c64672h1_cert1
#print axioms c64672h1_gens
#print axioms c64763a1_cert0
#print axioms c64763a1_cert1
#print axioms c64763a1_gens
#print axioms c64776a1_cert0
#print axioms c64776a1_cert1
#print axioms c64776a1_gens
#print axioms c65122e1_cert0
#print axioms c65122e1_cert1
#print axioms c65122e1_gens
#print axioms c65283c1_cert0
#print axioms c65283c1_cert1
#print axioms c65283c1_gens
#print axioms c65424a1_cert0
#print axioms c65424a1_cert1
#print axioms c65424a1_gens
#print axioms c65428d1_cert0
#print axioms c65428d1_cert1
#print axioms c65428d1_gens
#print axioms c65481c1_cert0
#print axioms c65481c1_cert1
#print axioms c65481c1_gens
#print axioms c65509a1_cert0
#print axioms c65509a1_cert1
#print axioms c65509a1_gens
#print axioms c65515a1_cert0
#print axioms c65515a1_cert1
#print axioms c65515a1_gens
#print axioms c65563a1_cert0
#print axioms c65563a1_cert1
#print axioms c65563a1_gens
#print axioms c65710b1_cert0
#print axioms c65710b1_cert1
#print axioms c65710b1_gens
#print axioms c66170b1_cert0
#print axioms c66170b1_cert1
#print axioms c66170b1_gens
#print axioms c66387a1_cert0
#print axioms c66387a1_cert1
#print axioms c66387a1_gens
#print axioms c66531a1_cert0
#print axioms c66531a1_cert1
#print axioms c66531a1_gens
#print axioms c66848j1_cert0
#print axioms c66848j1_cert1
#print axioms c66848j1_gens
#print axioms c66993d1_cert0
#print axioms c66993d1_cert1
#print axioms c66993d1_gens
#print axioms c67037b1_cert0
#print axioms c67037b1_cert1
#print axioms c67037b1_gens
#print axioms c67042a1_cert0
#print axioms c67042a1_cert1
#print axioms c67042a1_gens
#print axioms c67064a1_cert0
#print axioms c67064a1_cert1
#print axioms c67064a1_gens
#print axioms c67119a1_cert0
#print axioms c67119a1_cert1
#print axioms c67119a1_gens
#print axioms c67194e1_cert0
#print axioms c67194e1_cert1
#print axioms c67194e1_gens
#print axioms c67244a1_cert0
#print axioms c67244a1_cert1
#print axioms c67244a1_gens
#print axioms c67302f1_cert0
#print axioms c67302f1_cert1
#print axioms c67302f1_gens
#print axioms c67418a1_cert0
#print axioms c67418a1_cert1
#print axioms c67418a1_gens
#print axioms c67484b1_cert0
#print axioms c67484b1_cert1
#print axioms c67484b1_gens
#print axioms c67520z1_cert0
#print axioms c67520z1_cert1
#print axioms c67520z1_gens
#print axioms c67926b1_cert0
#print axioms c67926b1_cert1
#print axioms c67926b1_gens
#print axioms c68309a1_cert0
#print axioms c68309a1_cert1
#print axioms c68309a1_gens
#print axioms c68499j1_cert0
#print axioms c68499j1_cert1
#print axioms c68499j1_gens
#print axioms c68594b1_cert0
#print axioms c68594b1_cert1
#print axioms c68594b1_gens
#print axioms c68672c1_cert0
#print axioms c68672c1_cert1
#print axioms c68672c1_gens
#print axioms c68751d1_cert0
#print axioms c68751d1_cert1
#print axioms c68751d1_gens
#print axioms c68773a1_cert0
#print axioms c68773a1_cert1
#print axioms c68773a1_gens
#print axioms c68802d1_cert0
#print axioms c68802d1_cert1
#print axioms c68802d1_gens
#print axioms c68811b1_cert0
#print axioms c68811b1_cert1
#print axioms c68811b1_gens
#print axioms c68890d1_cert0
#print axioms c68890d1_cert1
#print axioms c68890d1_gens
#print axioms c69158c1_cert0
#print axioms c69158c1_cert1
#print axioms c69158c1_gens
#print axioms c69232a1_cert0
#print axioms c69232a1_cert1
#print axioms c69232a1_gens
#print axioms c69309c1_cert0
#print axioms c69309c1_cert1
#print axioms c69309c1_gens
#print axioms c69321a1_cert0
#print axioms c69321a1_cert1
#print axioms c69321a1_gens
#print axioms c69359a1_cert0
#print axioms c69359a1_cert1
#print axioms c69359a1_gens
#print axioms c69402e1_cert0
#print axioms c69402e1_cert1
#print axioms c69402e1_gens
#print axioms c69477a1_cert0
#print axioms c69477a1_cert1
#print axioms c69477a1_gens
#print axioms c69668b1_cert0
#print axioms c69668b1_cert1
#print axioms c69668b1_gens
#print axioms c69850m1_cert0
#print axioms c69850m1_cert1
#print axioms c69850m1_gens
#print axioms c69966t1_cert0
#print axioms c69966t1_cert1
#print axioms c69966t1_gens
#print axioms c70022b1_cert0
#print axioms c70022b1_cert1
#print axioms c70022b1_gens
#print axioms c70363a1_cert0
#print axioms c70363a1_cert1
#print axioms c70363a1_gens
#print axioms c70397b1_cert0
#print axioms c70397b1_cert1
#print axioms c70397b1_gens
#print axioms c70436b1_cert0
#print axioms c70436b1_cert1
#print axioms c70436b1_gens
#print axioms c70449a1_cert0
#print axioms c70449a1_cert1
#print axioms c70449a1_gens
#print axioms c70449b1_cert0
#print axioms c70449b1_cert1
#print axioms c70449b1_gens
#print axioms c70535a1_cert0
#print axioms c70535a1_cert1
#print axioms c70535a1_gens
#print axioms c70802b1_cert0
#print axioms c70802b1_cert1
#print axioms c70802b1_gens
#print axioms c71145a1_cert0
#print axioms c71145a1_cert1
#print axioms c71145a1_gens
#print axioms c71215a1_cert0
#print axioms c71215a1_cert1
#print axioms c71215a1_gens
#print axioms c71234a1_cert0
#print axioms c71234a1_cert1
#print axioms c71234a1_gens
#print axioms c71288i1_cert0
#print axioms c71288i1_cert1
#print axioms c71288i1_gens
#print axioms c71374d1_cert0
#print axioms c71374d1_cert1
#print axioms c71374d1_gens
#print axioms c71642b1_cert0
#print axioms c71642b1_cert1
#print axioms c71642b1_gens
#print axioms c71688a1_cert0
#print axioms c71688a1_cert1
#print axioms c71688a1_gens
#print axioms c72091a1_cert0
#print axioms c72091a1_cert1
#print axioms c72091a1_gens
#print axioms c72098a1_cert0
#print axioms c72098a1_cert1
#print axioms c72098a1_gens
#print axioms c72266a1_cert0
#print axioms c72266a1_cert1
#print axioms c72266a1_gens
#print axioms c72379a1_cert0
#print axioms c72379a1_cert1
#print axioms c72379a1_gens
#print axioms c72382a1_cert0
#print axioms c72382a1_cert1
#print axioms c72382a1_gens
#print axioms c72410a1_cert0
#print axioms c72410a1_cert1
#print axioms c72410a1_gens
#print axioms c72471b1_cert0
#print axioms c72471b1_cert1
#print axioms c72471b1_gens
#print axioms c72578a1_cert0
#print axioms c72578a1_cert1
#print axioms c72578a1_gens
#print axioms c72683a1_cert0
#print axioms c72683a1_cert1
#print axioms c72683a1_gens
#print axioms c72701a1_cert0
#print axioms c72701a1_cert1
#print axioms c72701a1_gens
#print axioms c72751b1_cert0
#print axioms c72751b1_cert1
#print axioms c72751b1_gens
#print axioms c73132a1_cert0
#print axioms c73132a1_cert1
#print axioms c73132a1_gens
#print axioms c73136b1_cert0
#print axioms c73136b1_cert1
#print axioms c73136b1_gens
#print axioms c73334a1_cert0
#print axioms c73334a1_cert1
#print axioms c73334a1_gens
#print axioms c73397c1_cert0
#print axioms c73397c1_cert1
#print axioms c73397c1_gens
#print axioms c73401a1_cert0
#print axioms c73401a1_cert1
#print axioms c73401a1_gens
#print axioms c73434b1_cert0
#print axioms c73434b1_cert1
#print axioms c73434b1_gens
#print axioms c73931a1_cert0
#print axioms c73931a1_cert1
#print axioms c73931a1_gens
#print axioms c74015a1_cert0
#print axioms c74015a1_cert1
#print axioms c74015a1_gens
#print axioms c74174a1_cert0
#print axioms c74174a1_cert1
#print axioms c74174a1_gens
#print axioms c74179b1_cert0
#print axioms c74179b1_cert1
#print axioms c74179b1_gens
#print axioms c74216a1_cert0
#print axioms c74216a1_cert1
#print axioms c74216a1_gens
#print axioms c74350c1_cert0
#print axioms c74350c1_cert1
#print axioms c74350c1_gens
#print axioms c74434a1_cert0
#print axioms c74434a1_cert1
#print axioms c74434a1_gens
#print axioms c74451a1_cert0
#print axioms c74451a1_cert1
#print axioms c74451a1_gens
#print axioms c74560p1_cert0
#print axioms c74560p1_cert1
#print axioms c74560p1_gens
#print axioms c74639b1_cert0
#print axioms c74639b1_cert1
#print axioms c74639b1_gens
#print axioms c74864b1_cert0
#print axioms c74864b1_cert1
#print axioms c74864b1_gens
#print axioms c74921g1_cert0
#print axioms c74921g1_cert1
#print axioms c74921g1_gens
#print axioms c74999a1_cert0
#print axioms c74999a1_cert1
#print axioms c74999a1_gens
#print axioms c75159h1_cert0
#print axioms c75159h1_cert1
#print axioms c75159h1_gens
#print axioms c75692a1_cert0
#print axioms c75692a1_cert1
#print axioms c75692a1_gens
#print axioms c75729a1_cert0
#print axioms c75729a1_cert1
#print axioms c75729a1_gens
#print axioms c75765c1_cert0
#print axioms c75765c1_cert1
#print axioms c75765c1_gens
#print axioms c75772a1_cert0
#print axioms c75772a1_cert1
#print axioms c75772a1_gens
#print axioms c75781a1_cert0
#print axioms c75781a1_cert1
#print axioms c75781a1_gens
#print axioms c76074b1_cert0
#print axioms c76074b1_cert1
#print axioms c76074b1_gens
#print axioms c76119a1_cert0
#print axioms c76119a1_cert1
#print axioms c76119a1_gens
#print axioms c76136c1_cert0
#print axioms c76136c1_cert1
#print axioms c76136c1_gens
#print axioms c76338h1_cert0
#print axioms c76338h1_cert1
#print axioms c76338h1_gens
#print axioms c76358e1_cert0
#print axioms c76358e1_cert1
#print axioms c76358e1_gens
#print axioms c76599a1_cert0
#print axioms c76599a1_cert1
#print axioms c76599a1_gens
#print axioms c76626e1_cert0
#print axioms c76626e1_cert1
#print axioms c76626e1_gens
#print axioms c76644c1_cert0
#print axioms c76644c1_cert1
#print axioms c76644c1_gens
#print axioms c76784h1_cert0
#print axioms c76784h1_cert1
#print axioms c76784h1_gens
#print axioms c76784i1_cert0
#print axioms c76784i1_cert1
#print axioms c76784i1_gens
#print axioms c76962e1_cert0
#print axioms c76962e1_cert1
#print axioms c76962e1_gens
#print axioms c77063a1_cert0
#print axioms c77063a1_cert1
#print axioms c77063a1_gens
#print axioms c77336d1_cert0
#print axioms c77336d1_cert1
#print axioms c77336d1_gens
#print axioms c77346a1_cert0
#print axioms c77346a1_cert1
#print axioms c77346a1_gens
#print axioms c77346d1_cert0
#print axioms c77346d1_cert1
#print axioms c77346d1_gens
#print axioms c77496f1_cert0
#print axioms c77496f1_cert1
#print axioms c77496f1_gens
#print axioms c77555d1_cert0
#print axioms c77555d1_cert1
#print axioms c77555d1_gens
#print axioms c77709a1_cert0
#print axioms c77709a1_cert1
#print axioms c77709a1_gens
#print axioms c77725c1_cert0
#print axioms c77725c1_cert1
#print axioms c77725c1_gens
#print axioms c77790a1_cert0
#print axioms c77790a1_cert1
#print axioms c77790a1_gens
#print axioms c78185b1_cert0
#print axioms c78185b1_cert1
#print axioms c78185b1_gens
#print axioms c78242a1_cert0
#print axioms c78242a1_cert1
#print axioms c78242a1_gens
#print axioms c78287b1_cert0
#print axioms c78287b1_cert1
#print axioms c78287b1_gens
#print axioms c78344a1_cert0
#print axioms c78344a1_cert1
#print axioms c78344a1_gens
#print axioms c78361a1_cert0
#print axioms c78361a1_cert1
#print axioms c78361a1_gens
#print axioms c78830a1_cert0
#print axioms c78830a1_cert1
#print axioms c78830a1_gens
#print axioms c78923b1_cert0
#print axioms c78923b1_cert1
#print axioms c78923b1_gens
#print axioms c79077f1_cert0
#print axioms c79077f1_cert1
#print axioms c79077f1_gens
#print axioms c79110c1_cert0
#print axioms c79110c1_cert1
#print axioms c79110c1_gens
#print axioms c79198d1_cert0
#print axioms c79198d1_cert1
#print axioms c79198d1_gens
#print axioms c79317b1_cert0
#print axioms c79317b1_cert1
#print axioms c79317b1_gens
#print axioms c79555a1_cert0
#print axioms c79555a1_cert1
#print axioms c79555a1_gens
#print axioms c79675b1_cert0
#print axioms c79675b1_cert1
#print axioms c79675b1_gens
#print axioms c79934b1_cert0
#print axioms c79934b1_cert1
#print axioms c79934b1_gens
#print axioms c80212b1_cert0
#print axioms c80212b1_cert1
#print axioms c80212b1_gens
#print axioms c80222a1_cert0
#print axioms c80222a1_cert1
#print axioms c80222a1_gens
#print axioms c80256a1_cert0
#print axioms c80256a1_cert1
#print axioms c80256a1_gens
#print axioms c80351d1_cert0
#print axioms c80351d1_cert1
#print axioms c80351d1_gens
#print axioms c80559b1_cert0
#print axioms c80559b1_cert1
#print axioms c80559b1_gens
#print axioms c80615d1_cert0
#print axioms c80615d1_cert1
#print axioms c80615d1_gens
#print axioms c80674a1_cert0
#print axioms c80674a1_cert1
#print axioms c80674a1_gens
#print axioms c80721b1_cert0
#print axioms c80721b1_cert1
#print axioms c80721b1_gens
#print axioms c80913a1_cert0
#print axioms c80913a1_cert1
#print axioms c80913a1_gens
#print axioms c80965a1_cert0
#print axioms c80965a1_cert1
#print axioms c80965a1_gens
#print axioms c81063c1_cert0
#print axioms c81063c1_cert1
#print axioms c81063c1_gens
#print axioms c81162c1_cert0
#print axioms c81162c1_cert1
#print axioms c81162c1_gens
#print axioms c81234h1_cert0
#print axioms c81234h1_cert1
#print axioms c81234h1_gens
#print axioms c81328c1_cert0
#print axioms c81328c1_cert1
#print axioms c81328c1_gens
#print axioms c81494a1_cert0
#print axioms c81494a1_cert1
#print axioms c81494a1_gens
#print axioms c81524c1_cert0
#print axioms c81524c1_cert1
#print axioms c81524c1_gens
#print axioms c81939e1_cert0
#print axioms c81939e1_cert1
#print axioms c81939e1_gens
#print axioms c82093a1_cert0
#print axioms c82093a1_cert1
#print axioms c82093a1_gens
#print axioms c82146a1_cert0
#print axioms c82146a1_cert1
#print axioms c82146a1_gens
#print axioms c82174c1_cert0
#print axioms c82174c1_cert1
#print axioms c82174c1_gens
#print axioms c82288q1_cert0
#print axioms c82288q1_cert1
#print axioms c82288q1_gens
#print axioms c82296i1_cert0
#print axioms c82296i1_cert1
#print axioms c82296i1_gens
#print axioms c82480a1_cert0
#print axioms c82480a1_cert1
#print axioms c82480a1_gens
#print axioms c82538a1_cert0
#print axioms c82538a1_cert1
#print axioms c82538a1_gens
#print axioms c82539e1_cert0
#print axioms c82539e1_cert1
#print axioms c82539e1_gens
#print axioms c82547b1_cert0
#print axioms c82547b1_cert1
#print axioms c82547b1_gens
#print axioms c82701f1_cert0
#print axioms c82701f1_cert1
#print axioms c82701f1_gens
#print axioms c82763a1_cert0
#print axioms c82763a1_cert1
#print axioms c82763a1_gens
#print axioms c82808c1_cert0
#print axioms c82808c1_cert1
#print axioms c82808c1_gens
#print axioms c83016f1_cert0
#print axioms c83016f1_cert1
#print axioms c83016f1_gens
#print axioms c83105a1_cert0
#print axioms c83105a1_cert1
#print axioms c83105a1_gens
#print axioms c83111c1_cert0
#print axioms c83111c1_cert1
#print axioms c83111c1_gens
#print axioms c83262a1_cert0
#print axioms c83262a1_cert1
#print axioms c83262a1_gens
#print axioms c83350a1_cert0
#print axioms c83350a1_cert1
#print axioms c83350a1_gens
#print axioms c83582g1_cert0
#print axioms c83582g1_cert1
#print axioms c83582g1_gens
#print axioms c83718d1_cert0
#print axioms c83718d1_cert1
#print axioms c83718d1_gens
#print axioms c83798c1_cert0
#print axioms c83798c1_cert1
#print axioms c83798c1_gens
#print axioms c83806a1_cert0
#print axioms c83806a1_cert1
#print axioms c83806a1_gens
#print axioms c83876a1_cert0
#print axioms c83876a1_cert1
#print axioms c83876a1_gens
#print axioms c83928b1_cert0
#print axioms c83928b1_cert1
#print axioms c83928b1_gens
#print axioms c84176a1_cert0
#print axioms c84176a1_cert1
#print axioms c84176a1_gens
#print axioms c84341a1_cert0
#print axioms c84341a1_cert1
#print axioms c84341a1_gens
#print axioms c84470b1_cert0
#print axioms c84470b1_cert1
#print axioms c84470b1_gens
#print axioms c84534a1_cert0
#print axioms c84534a1_cert1
#print axioms c84534a1_gens
#print axioms c84650g1_cert0
#print axioms c84650g1_cert1
#print axioms c84650g1_gens
#print axioms c84746a1_cert0
#print axioms c84746a1_cert1
#print axioms c84746a1_gens
#print axioms c85174a1_cert0
#print axioms c85174a1_cert1
#print axioms c85174a1_gens
#print axioms c85222a1_cert0
#print axioms c85222a1_cert1
#print axioms c85222a1_gens
#print axioms c85295a1_cert0
#print axioms c85295a1_cert1
#print axioms c85295a1_gens
#print axioms c85318e1_cert0
#print axioms c85318e1_cert1
#print axioms c85318e1_gens
#print axioms c85863a1_cert0
#print axioms c85863a1_cert1
#print axioms c85863a1_gens
#print axioms c85970a1_cert0
#print axioms c85970a1_cert1
#print axioms c85970a1_gens
#print axioms c86007a1_cert0
#print axioms c86007a1_cert1
#print axioms c86007a1_gens
#print axioms c86321a1_cert0
#print axioms c86321a1_cert1
#print axioms c86321a1_gens
#print axioms c86487a1_cert0
#print axioms c86487a1_cert1
#print axioms c86487a1_gens
#print axioms c86534e1_cert0
#print axioms c86534e1_cert1
#print axioms c86534e1_gens
#print axioms c86611a1_cert0
#print axioms c86611a1_cert1
#print axioms c86611a1_gens
#print axioms c86786a1_cert0
#print axioms c86786a1_cert1
#print axioms c86786a1_gens
#print axioms c86802i1_cert0
#print axioms c86802i1_cert1
#print axioms c86802i1_gens
#print axioms c86895f1_cert0
#print axioms c86895f1_cert1
#print axioms c86895f1_gens
#print axioms c86903b1_cert0
#print axioms c86903b1_cert1
#print axioms c86903b1_gens
#print axioms c87116c1_cert0
#print axioms c87116c1_cert1
#print axioms c87116c1_gens
#print axioms c87130a1_cert0
#print axioms c87130a1_cert1
#print axioms c87130a1_gens
#print axioms c87194a1_cert0
#print axioms c87194a1_cert1
#print axioms c87194a1_gens
#print axioms c87228c1_cert0
#print axioms c87228c1_cert1
#print axioms c87228c1_gens
#print axioms c87289b1_cert0
#print axioms c87289b1_cert1
#print axioms c87289b1_gens
#print axioms c87336g1_cert0
#print axioms c87336g1_cert1
#print axioms c87336g1_gens
#print axioms c87398b1_cert0
#print axioms c87398b1_cert1
#print axioms c87398b1_gens
#print axioms c87634a1_cert0
#print axioms c87634a1_cert1
#print axioms c87634a1_gens
#print axioms c87763b1_cert0
#print axioms c87763b1_cert1
#print axioms c87763b1_gens
#print axioms c87837a1_cert0
#print axioms c87837a1_cert1
#print axioms c87837a1_gens
#print axioms c87855a1_cert0
#print axioms c87855a1_cert1
#print axioms c87855a1_gens
#print axioms c87866a1_cert0
#print axioms c87866a1_cert1
#print axioms c87866a1_gens
#print axioms c87914e1_cert0
#print axioms c87914e1_cert1
#print axioms c87914e1_gens
#print axioms c88022a1_cert0
#print axioms c88022a1_cert1
#print axioms c88022a1_gens
#print axioms c88024a1_cert0
#print axioms c88024a1_cert1
#print axioms c88024a1_gens
#print axioms c88208c1_cert0
#print axioms c88208c1_cert1
#print axioms c88208c1_gens
#print axioms c88264h1_cert0
#print axioms c88264h1_cert1
#print axioms c88264h1_gens
#print axioms c88337a1_cert0
#print axioms c88337a1_cert1
#print axioms c88337a1_gens
#print axioms c88362e1_cert0
#print axioms c88362e1_cert1
#print axioms c88362e1_gens
#print axioms c88460a1_cert0
#print axioms c88460a1_cert1
#print axioms c88460a1_gens
#print axioms c88492a1_cert0
#print axioms c88492a1_cert1
#print axioms c88492a1_gens
#print axioms c88502f1_cert0
#print axioms c88502f1_cert1
#print axioms c88502f1_gens
#print axioms c88582e1_cert0
#print axioms c88582e1_cert1
#print axioms c88582e1_gens
#print axioms c88705c1_cert0
#print axioms c88705c1_cert1
#print axioms c88705c1_gens
#print axioms c88754a1_cert0
#print axioms c88754a1_cert1
#print axioms c88754a1_gens
#print axioms c88765d1_cert0
#print axioms c88765d1_cert1
#print axioms c88765d1_gens
#print axioms c88883a1_cert0
#print axioms c88883a1_cert1
#print axioms c88883a1_gens
#print axioms c88975c1_cert0
#print axioms c88975c1_cert1
#print axioms c88975c1_gens
#print axioms c89098a1_cert0
#print axioms c89098a1_cert1
#print axioms c89098a1_gens
#print axioms c89294a1_cert0
#print axioms c89294a1_cert1
#print axioms c89294a1_gens
#print axioms c89421b1_cert0
#print axioms c89421b1_cert1
#print axioms c89421b1_gens
#print axioms c89428b1_cert0
#print axioms c89428b1_cert1
#print axioms c89428b1_gens
#print axioms c89475a1_cert0
#print axioms c89475a1_cert1
#print axioms c89475a1_gens
#print axioms c89574a1_cert0
#print axioms c89574a1_cert1
#print axioms c89574a1_gens
#print axioms c89576d1_cert0
#print axioms c89576d1_cert1
#print axioms c89576d1_gens
#print axioms c89687a1_cert0
#print axioms c89687a1_cert1
#print axioms c89687a1_gens
#print axioms c89738b1_cert0
#print axioms c89738b1_cert1
#print axioms c89738b1_gens
#print axioms c89992a1_cert0
#print axioms c89992a1_cert1
#print axioms c89992a1_gens
#print axioms c90297b1_cert0
#print axioms c90297b1_cert1
#print axioms c90297b1_gens
#print axioms c90312i1_cert0
#print axioms c90312i1_cert1
#print axioms c90312i1_gens
#print axioms c90459o1_cert0
#print axioms c90459o1_cert1
#print axioms c90459o1_gens
#print axioms c90568e1_cert0
#print axioms c90568e1_cert1
#print axioms c90568e1_gens
#print axioms c90644b1_cert0
#print axioms c90644b1_cert1
#print axioms c90644b1_gens
#print axioms c90704c1_cert0
#print axioms c90704c1_cert1
#print axioms c90704c1_gens
#print axioms c90840a1_cert0
#print axioms c90840a1_cert1
#print axioms c90840a1_gens
#print axioms c90935a1_cert0
#print axioms c90935a1_cert1
#print axioms c90935a1_gens
#print axioms c90953a1_cert0
#print axioms c90953a1_cert1
#print axioms c90953a1_gens
#print axioms c91031c1_cert0
#print axioms c91031c1_cert1
#print axioms c91031c1_gens
#print axioms c91055a1_cert0
#print axioms c91055a1_cert1
#print axioms c91055a1_gens
#print axioms c91248s1_cert0
#print axioms c91248s1_cert1
#print axioms c91248s1_gens
#print axioms c91270c1_cert0
#print axioms c91270c1_cert1
#print axioms c91270c1_gens
#print axioms c91341d1_cert0
#print axioms c91341d1_cert1
#print axioms c91341d1_gens
#print axioms c91388b1_cert0
#print axioms c91388b1_cert1
#print axioms c91388b1_gens
#print axioms c91506a1_cert0
#print axioms c91506a1_cert1
#print axioms c91506a1_gens
#print axioms c91607a1_cert0
#print axioms c91607a1_cert1
#print axioms c91607a1_gens
#print axioms c91744d1_cert0
#print axioms c91744d1_cert1
#print axioms c91744d1_gens
#print axioms c91775c1_cert0
#print axioms c91775c1_cert1
#print axioms c91775c1_gens
#print axioms c91958a1_cert0
#print axioms c91958a1_cert1
#print axioms c91958a1_gens
#print axioms c91963a1_cert0
#print axioms c91963a1_cert1
#print axioms c91963a1_gens
#print axioms c91985b1_cert0
#print axioms c91985b1_cert1
#print axioms c91985b1_gens
#print axioms c92096d1_cert0
#print axioms c92096d1_cert1
#print axioms c92096d1_gens
#print axioms c92144a1_cert0
#print axioms c92144a1_cert1
#print axioms c92144a1_gens
#print axioms c92437a1_cert0
#print axioms c92437a1_cert1
#print axioms c92437a1_gens
#print axioms c92437b1_cert0
#print axioms c92437b1_cert1
#print axioms c92437b1_gens
#print axioms c92480bb1_cert0
#print axioms c92480bb1_cert1
#print axioms c92480bb1_gens
#print axioms c92553b1_cert0
#print axioms c92553b1_cert1
#print axioms c92553b1_gens
#print axioms c92601a1_cert0
#print axioms c92601a1_cert1
#print axioms c92601a1_gens
#print axioms c92651a1_cert0
#print axioms c92651a1_cert1
#print axioms c92651a1_gens
#print axioms c92869d1_cert0
#print axioms c92869d1_cert1
#print axioms c92869d1_gens
#print axioms c93087a1_cert0
#print axioms c93087a1_cert1
#print axioms c93087a1_gens
#print axioms c93376c1_cert0
#print axioms c93376c1_cert1
#print axioms c93376c1_gens
#print axioms c93508b1_cert0
#print axioms c93508b1_cert1
#print axioms c93508b1_gens
#print axioms c93545e1_cert0
#print axioms c93545e1_cert1
#print axioms c93545e1_gens
#print axioms c93783a1_cert0
#print axioms c93783a1_cert1
#print axioms c93783a1_gens
#print axioms c93814a1_cert0
#print axioms c93814a1_cert1
#print axioms c93814a1_gens
#print axioms c93904a1_cert0
#print axioms c93904a1_cert1
#print axioms c93904a1_gens
#print axioms c94064a1_cert0
#print axioms c94064a1_cert1
#print axioms c94064a1_gens
#print axioms c94259d1_cert0
#print axioms c94259d1_cert1
#print axioms c94259d1_gens
#print axioms c94281b1_cert0
#print axioms c94281b1_cert1
#print axioms c94281b1_gens
#print axioms c94659a1_cert0
#print axioms c94659a1_cert1
#print axioms c94659a1_gens
#print axioms c94715b1_cert0
#print axioms c94715b1_cert1
#print axioms c94715b1_gens
#print axioms c94739a1_cert0
#print axioms c94739a1_cert1
#print axioms c94739a1_gens
#print axioms c95134d1_cert0
#print axioms c95134d1_cert1
#print axioms c95134d1_gens
#print axioms c95227g1_cert0
#print axioms c95227g1_cert1
#print axioms c95227g1_gens
#print axioms c95323b1_cert0
#print axioms c95323b1_cert1
#print axioms c95323b1_gens
#print axioms c95887b1_cert0
#print axioms c95887b1_cert1
#print axioms c95887b1_gens
#print axioms c95954c1_cert0
#print axioms c95954c1_cert1
#print axioms c95954c1_gens
#print axioms c96153a1_cert0
#print axioms c96153a1_cert1
#print axioms c96153a1_gens
#print axioms c96163a1_cert0
#print axioms c96163a1_cert1
#print axioms c96163a1_gens
#print axioms c96266d1_cert0
#print axioms c96266d1_cert1
#print axioms c96266d1_gens
#print axioms c96376b1_cert0
#print axioms c96376b1_cert1
#print axioms c96376b1_gens
#print axioms c96466b1_cert0
#print axioms c96466b1_cert1
#print axioms c96466b1_gens
#print axioms c96544a1_cert0
#print axioms c96544a1_cert1
#print axioms c96544a1_gens
#print axioms c96873a1_cert0
#print axioms c96873a1_cert1
#print axioms c96873a1_gens
#print axioms c96937a1_cert0
#print axioms c96937a1_cert1
#print axioms c96937a1_gens
#print axioms c97111a1_cert0
#print axioms c97111a1_cert1
#print axioms c97111a1_gens
#print axioms c97345d1_cert0
#print axioms c97345d1_cert1
#print axioms c97345d1_gens
#print axioms c97389a1_cert0
#print axioms c97389a1_cert1
#print axioms c97389a1_gens
#print axioms c97408a1_cert0
#print axioms c97408a1_cert1
#print axioms c97408a1_gens
#print axioms c97423a1_cert0
#print axioms c97423a1_cert1
#print axioms c97423a1_gens
#print axioms c97506a1_cert0
#print axioms c97506a1_cert1
#print axioms c97506a1_gens
#print axioms c97543a1_cert0
#print axioms c97543a1_cert1
#print axioms c97543a1_gens
#print axioms c97668f1_cert0
#print axioms c97668f1_cert1
#print axioms c97668f1_gens
#print axioms c97782a1_cert0
#print axioms c97782a1_cert1
#print axioms c97782a1_gens
#print axioms c97811a1_cert0
#print axioms c97811a1_cert1
#print axioms c97811a1_gens
#print axioms c97834c1_cert0
#print axioms c97834c1_cert1
#print axioms c97834c1_gens
#print axioms c97877a1_cert0
#print axioms c97877a1_cert1
#print axioms c97877a1_gens
#print axioms c98081a1_cert0
#print axioms c98081a1_cert1
#print axioms c98081a1_gens
#print axioms c98231a1_cert0
#print axioms c98231a1_cert1
#print axioms c98231a1_gens
#print axioms c98597a1_cert0
#print axioms c98597a1_cert1
#print axioms c98597a1_gens
#print axioms c98730d1_cert0
#print axioms c98730d1_cert1
#print axioms c98730d1_gens
#print axioms c98841c1_cert0
#print axioms c98841c1_cert1
#print axioms c98841c1_gens
#print axioms c98891a1_cert0
#print axioms c98891a1_cert1
#print axioms c98891a1_gens
#print axioms c99153b1_cert0
#print axioms c99153b1_cert1
#print axioms c99153b1_gens
#print axioms c99248d1_cert0
#print axioms c99248d1_cert1
#print axioms c99248d1_gens
#print axioms c99326a1_cert0
#print axioms c99326a1_cert1
#print axioms c99326a1_gens
#print axioms c99378d1_cert0
#print axioms c99378d1_cert1
#print axioms c99378d1_gens
#print axioms c99572b1_cert0
#print axioms c99572b1_cert1
#print axioms c99572b1_gens
#print axioms c99776q1_cert0
#print axioms c99776q1_cert1
#print axioms c99776q1_gens
#print axioms c99966a1_cert0
#print axioms c99966a1_cert1
#print axioms c99966a1_gens
#print axioms c99968j1_cert0
#print axioms c99968j1_cert1
#print axioms c99968j1_gens
