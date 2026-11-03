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
