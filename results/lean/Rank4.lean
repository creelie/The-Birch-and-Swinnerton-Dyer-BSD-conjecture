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

/-- All certificates of one curve: a list of `(p, q1, q2, q3)`. -/
def certAll (a1 a2 a3 a4 a6 : Int) (l : List (Nat × Nat × Nat × Nat)) : Bool :=
  l.all (fun ⟨p, q1, q2, q3⟩ => certP a1 a2 a3 a4 a6 p q1 q2 q3)

/-- All points `[x : y : z]` lie on the curve. -/
def allOn (a1 a2 a3 a4 a6 : Int) (l : List (Int × Int × Int)) : Bool :=
  l.all (fun ⟨x, y, z⟩ => onCurve a1 a2 a3 a4 a6 x y z)

end BSDCert

open BSDCert

-- 234446a1: 163 primes
set_option maxHeartbeats 0 in
theorem c234446a1_cert0 : certAll 1 (-1) 0 (-79) 289 [(5, 3, 13, 3), (7, 5, 3, 3), (11, 3, 17, 3), (13, 11, 3, 3), (17, 3, 5, 3), (19, 5, 3, 3), (23, 3, 29, 3), (29, 3, 5, 3), (31, 5, 3, 3), (37, 11, 3, 3), (41, 3, 5, 3), (43, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c234446a1_cert1 : certAll 1 (-1) 0 (-79) 289 [(47, 3, 29, 3), (53, 3, 5, 3), (61, 11, 3, 3), (67, 5, 3, 3), (71, 3, 23, 3), (73, 23, 3, 3), (79, 5, 3, 3), (83, 3, 11, 3), (89, 3, 5, 3), (97, 23, 3, 3), (103, 5, 3, 3), (107, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c234446a1_cert2 : certAll 1 (-1) 0 (-79) 289 [(109, 11, 3, 3), (113, 3, 5, 3), (127, 5, 3, 3), (131, 3, 11, 3), (137, 3, 5, 3), (139, 5, 3, 3), (149, 3, 5, 3), (151, 5, 3, 3), (157, 11, 3, 3), (163, 5, 3, 3), (167, 3, 29, 3), (173, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c234446a1_cert3 : certAll 1 (-1) 0 (-79) 289 [(179, 3, 11, 3), (181, 11, 3, 3), (191, 3, 23, 3), (193, 29, 3, 3), (197, 3, 5, 3), (199, 5, 3, 3), (211, 5, 3, 3), (223, 5, 3, 3), (227, 3, 11, 3), (229, 11, 3, 3), (233, 3, 5, 3), (239, 3, 23, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c234446a1_cert4 : certAll 1 (-1) 0 (-79) 289 [(241, 23, 3, 3), (251, 3, 11, 3), (257, 3, 5, 3), (263, 3, 23, 3), (269, 3, 5, 3), (271, 5, 3, 3), (277, 11, 3, 3), (281, 3, 5, 3), (283, 5, 3, 3), (293, 3, 5, 3), (307, 5, 3, 3), (311, 3, 47, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c234446a1_cert5 : certAll 1 (-1) 0 (-79) 289 [(313, 23, 3, 3), (317, 3, 5, 3), (331, 5, 3, 3), (347, 3, 11, 3), (349, 11, 3, 3), (353, 3, 5, 3), (359, 3, 23, 3), (367, 5, 3, 3), (373, 11, 3, 3), (379, 5, 3, 3), (383, 3, 29, 3), (389, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c234446a1_cert6 : certAll 1 (-1) 0 (-79) 289 [(397, 11, 3, 3), (401, 3, 5, 3), (409, 23, 3, 3), (419, 3, 11, 3), (421, 11, 3, 3), (431, 3, 23, 3), (433, 23, 3, 3), (439, 5, 3, 3), (443, 3, 11, 3), (449, 3, 5, 3), (457, 29, 3, 3), (461, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c234446a1_cert7 : certAll 1 (-1) 0 (-79) 289 [(463, 5, 3, 3), (467, 3, 11, 3), (479, 3, 41, 3), (487, 5, 3, 3), (491, 3, 11, 3), (499, 5, 3, 3), (503, 3, 29, 3), (509, 3, 5, 3), (521, 3, 5, 3), (523, 5, 3, 3), (541, 11, 3, 3), (547, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c234446a1_cert8 : certAll 1 (-1) 0 (-79) 289 [(557, 3, 5, 3), (563, 3, 11, 3), (569, 3, 5, 3), (571, 5, 3, 3), (577, 23, 3, 3), (587, 3, 11, 3), (593, 3, 5, 3), (599, 3, 23, 3), (601, 23, 3, 3), (607, 5, 3, 3), (613, 11, 3, 3), (617, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c234446a1_cert9 : certAll 1 (-1) 0 (-79) 289 [(619, 5, 3, 3), (631, 5, 3, 3), (641, 3, 5, 3), (643, 5, 3, 3), (647, 3, 29, 3), (653, 3, 5, 3), (659, 3, 11, 3), (661, 11, 3, 3), (673, 29, 3, 3), (677, 3, 5, 3), (683, 3, 11, 3), (691, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c234446a1_cert10 : certAll 1 (-1) 0 (-79) 289 [(701, 3, 5, 3), (709, 11, 3, 3), (719, 3, 67, 3), (727, 5, 3, 3), (733, 11, 3, 3), (739, 5, 3, 3), (743, 3, 23, 3), (751, 5, 3, 3), (757, 11, 3, 3), (761, 3, 5, 3), (769, 23, 3, 3), (773, 3, 5, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c234446a1_cert11 : certAll 1 (-1) 0 (-79) 289 [(787, 5, 3, 3), (797, 3, 5, 3), (809, 3, 5, 3), (811, 5, 3, 3), (821, 3, 5, 3), (823, 5, 3, 3), (827, 3, 11, 3), (829, 11, 3, 3), (839, 3, 41, 3), (853, 11, 3, 3), (857, 3, 5, 3), (859, 5, 3, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c234446a1_cert12 : certAll 1 (-1) 0 (-79) 289 [(863, 3, 23, 3), (877, 11, 3, 3), (881, 3, 5, 3), (883, 5, 3, 3), (887, 3, 29, 3), (907, 5, 3, 3), (911, 3, 23, 3), (919, 5, 3, 3), (929, 3, 5, 3), (937, 23, 3, 3), (941, 3, 5, 3), (947, 3, 11, 3)] = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c234446a1_cert13 : certAll 1 (-1) 0 (-79) 289 [(953, 3, 5, 3), (967, 5, 3, 3), (971, 3, 11, 3), (977, 3, 5, 3), (983, 3, 29, 3), (991, 5, 3, 3), (997, 11, 3, 3)] = true := by decide +kernel
theorem c234446a1_gens : allOn 1 (-1) 0 (-79) 289 [(6, (-1), 1), (4, 3, 1), (5, (-2), 1), (8, 7, 1)] = true := by decide +kernel

#print axioms c234446a1_cert0
