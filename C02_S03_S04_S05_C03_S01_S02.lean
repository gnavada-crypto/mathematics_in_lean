import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic


variable (a b c d e : ℝ)
open Real

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

section
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)

end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  · apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁

example (x : ℝ) : x ≤ x := by
  apply le_refl

example (x : ℝ) : x ≤ x :=
  le_refl x

#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)

-- Try this.
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  have h₄: a<c:= by
    apply lt_of_le_of_lt h₀ h₁
  have h₅: a< d:= by
    apply lt_of_lt_of_le h₄ h₂
  apply lt_trans h₅ h₃


example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith

section

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith

end

example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']

#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_right : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_left : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_right : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_left : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_right

example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  exact h

example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.mpr h₁
  apply le_refl

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  apply add_le_add_right
  apply exp_le_exp.mpr
  apply add_le_add_right
  exact h₀



example : (0 : ℝ) < 1 := by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by
    apply add_pos_of_pos_of_nonneg
    · linarith
    apply le_of_lt
    apply exp_pos a

  apply log_le_log h₀
  apply add_le_add_right
  apply exp_le_exp.mpr h

example : 0 ≤ a ^ 2 := by
  -- apply?
  exact sq_nonneg a

example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  apply add_le_add_right
  apply neg_le_neg
  exact exp_le_exp.mpr h


example : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg

  calc
    2*a*b = 2*a*b + 0 := by ring
    _ ≤ 2*a*b + (a^2 - 2*a*b + b^2) := add_le_add (le_refl _) h
    _ = a^2 + b^2 := by ring

example : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

example : |a*b| ≤ (a^2 + b^2)/2 := by
 have h₀: 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith
 have h₁: a*b≤ (a^2 + b^2)/2:=by
    linarith[h₀]
 have h₃: -2*a*b ≤ a^2 + b^2 := by
  have h₄ : 0 ≤ a^2 +2*a*b + b^2
  calc
    a^2 +2*a*b + b^2 = (a +b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith
 have h₂: -(a*b)≤ (a^2 + b^2)/2 :=by
    linarith[h₃]
 exact abs_le'.mpr ⟨h₁, h₂⟩
#check abs_le'

S04

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  · show max a b ≤ max b a
    apply max_le
    · apply le_max_right
    apply le_max_left
  · show max b a ≤ max a b
    apply max_le
    · apply le_max_right
    apply le_max_left

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · show min (min a b) c ≤  min a (min b c)
    have h₁: min (min a b) c ≤ a:= by
        apply le_trans
        apply min_le_left (min a b) c
        apply min_le_left a b
    have h₂: min (min a b) c ≤ b:= by
        apply le_trans
        apply min_le_left (min a b) c
        apply min_le_right a b
    have h₃: min (min a b) c ≤ c:= by
        apply min_le_right (min a b) c
    have h₄: min (min a b) c ≤ min b c:= by
      apply le_min h₂ h₃
    apply le_min h₁ h₄

  · show min a (min b c) ≤ min (min a b) c
    have g₁: min a (min b c)≤ a:= by
        apply min_le_left a (min b c)
    have g₂: min a (min b c) ≤ b:= by
        apply le_trans
        apply min_le_right a (min b c)
        apply min_le_left b c
    have g₃: min a (min b c) ≤ c:= by
        apply le_trans
        apply min_le_right a (min b c)
        apply min_le_right b c
    have g₄: min a (min b c) ≤ min a b := by
      apply le_min g₁ g₂
    apply le_min g₄ g₃

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · show (min a b) + c ≤ a + c
    apply add_le_add_left
    apply min_le_left a b
  · show (min a b) + c ≤ b + c
    apply add_le_add_left
    apply min_le_right a b


example : min a b + c = min (a + c) (b + c) := by
 apply le_antisymm
 · exact aux a b c
 show min (a + c) (b + c)≤ min a b + c
 have h: (min a b) +c ≤ a+c:= by
    apply add_le_add_left
    exact min_le_left a b
 have g₁:(min (a+c) (b+c))-c ≤ a := by
    rw[sub_le_iff_le_add]
    exact min_le_left (a+c) (b+c)
 have g₂:(min (a+c) (b+c))-c ≤ b := by
    rw[sub_le_iff_le_add]
    exact min_le_right (a+c) (b+c)
 have g₃: (min (a+c) (b+c))-c ≤ min a b := by
    exact le_min g₁ g₂
 rw[sub_le_iff_le_add] at g₃
 exact g₃



#check (abs_add_le : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  rw[sub_le_iff_le_add]
  nth_rw 1[← add_zero a]
  rw[← neg_add_cancel b]
  rw[← add_assoc]
 -- rw[sub_eq_add_neg]
  exact abs_add_le (a-b) b

end
section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  rw[← mul_assoc]
  have h₁ : x ∣ y * x * z := by
    apply dvd_mul_of_dvd_left
    apply dvd_mul_left
  have h₂ : x ∣ x^2 := by
    apply dvd_mul_left
  have h₃ : w ∣ w^2 := by
    apply dvd_mul_left
  have h₃ : x ∣ w^2 :=
   dvd_trans  h h₃
  have h₄ : x ∣ y * x * z +x^2 := by
    apply dvd_add h₁ h₂
  have h₅ : x ∣ y * x * z +x^2 +w^2 := by
    apply dvd_add h₄ h₃
  exact h₅

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  rw[Nat.gcd_comm]


end

S05


import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
   apply le_antisymm
   show  x ⊓ y ≤ y ⊓ x
   apply le_inf
   apply inf_le_right
   apply inf_le_left
   show  y ⊓ x ≤ x ⊓ y
   apply le_inf
   apply inf_le_right
   apply inf_le_left


example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · show  (x ⊓ y) ⊓ z ≤  x ⊓ (y ⊓ z)
    have h₁: (x ⊓ y) ⊓ z ≤ x:= by
      apply le_trans
      apply inf_le_left
      apply inf_le_left
    have h₂: (x ⊓ y) ⊓ z ≤ y:= by
      apply le_trans
      apply inf_le_left
      apply inf_le_right
    have h₃: (x ⊓ y) ⊓ z ≤ z:= by
      apply inf_le_right
    have h₄: (x ⊓ y) ⊓ z ≤  y ⊓ z:= by
      apply le_inf h₂ h₃
    apply le_inf h₁ h₄

  · show x ⊓ (y ⊓ z)≤ (x ⊓ y) ⊓ z
    have g₁: x ⊓ (y ⊓ z)≤ x:= by
      apply inf_le_left
    have g₂: x ⊓ (y ⊓ z) ≤ y:= by
      apply le_trans
      apply inf_le_right
      apply inf_le_left
    have g₃: x ⊓ (y ⊓ z) ≤ z:= by
      apply le_trans
      apply inf_le_right
      apply inf_le_right
    have g₄:  x ⊓ (y ⊓ z)≤ x ⊓ y:= by
      apply le_inf g₁ g₂
    apply le_inf g₄ g₃


example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  · show x ⊔ y ≤  y ⊔ x
    apply sup_le
    · apply le_sup_right
    apply le_sup_left
  · show y ⊔ x ≤  x ⊔ y
    apply sup_le
    · apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · show x ⊔ y ⊔ z ≤  x ⊔ (y ⊔ z)
    have h₁: x≤x ⊔ (y ⊔ z):=
    le_sup_left
    have h₂: y ≤ x ⊔ (y ⊔ z):= by
      apply le_trans
      rotate_left
      apply le_sup_right
      apply le_sup_left
    have h₃: x ⊔ y ≤ x ⊔ (y ⊔ z):= by
      apply sup_le h₁ h₂
    have h₄: z ≤ x ⊔ (y ⊔ z):= by
      apply le_trans
      rotate_left
      apply le_sup_right
      apply le_sup_right
    apply sup_le h₃ h₄
  · show x ⊔ (y ⊔ z) ≤  x ⊔ y ⊔ z
    have h₅: x ≤ (x ⊔ y) ⊔ z:= by
      apply le_trans
      rotate_left
      apply le_sup_left
      apply le_sup_left
    have h₆: y ≤ (x ⊔ y) ⊔ z:= by
      apply le_trans
      rotate_left
      apply le_sup_left
      apply le_sup_right
    have h₇: z ≤ (x ⊔ y) ⊔ z:= by
      apply le_sup_right
    have h₈: y ⊔ z ≤ (x ⊔ y) ⊔ z:= by
      apply sup_le h₆ h₇
    have h₉:x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z:= by
      apply sup_le h₅ h₈
    exact h₉




theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · show x ⊓ (x ⊔ y) ≤ x
    apply inf_le_left
  · show x ≤ x ⊓ (x ⊔ y)
    apply le_inf
    apply le_refl
    apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
    apply le_antisymm
    apply sup_le
    apply le_refl
    apply inf_le_left
    apply le_sup_left


end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  apply le_antisymm
  · show a ⊔ b ⊓ c ≤ (a ⊔ b) ⊓ (a ⊔ c)
    apply sup_le
    apply le_inf
    apply le_sup_left
    apply le_sup_left
    apply le_inf
    apply le_trans
    apply inf_le_left
    apply le_sup_right
    apply le_trans
    apply inf_le_right
    apply le_sup_right
  · show (a ⊔ b) ⊓ (a ⊔ c) ≤ a ⊔ b ⊓ c
    rw[h (a ⊔ b) a c]
    apply sup_le
    rw[inf_comm (a ⊔ b) a]
    rw[absorb1 a b]
    apply le_sup_left
    rw[inf_comm (a⊔ b) c]
    rw[h c a b]
    apply sup_le
    apply le_trans
    apply inf_le_right
    apply le_sup_left
    rw[inf_comm c b]
    apply le_sup_right



example (h : ∀ x y z : α, x ⊔ y ⊓ z =  (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  apply le_antisymm
  · show  a ⊓ (b ⊔ c) ≤  a ⊓ b ⊔ a ⊓ c
    rw[h (a ⊓ b) a c]
    apply le_inf
    rw[sup_comm (a ⊓ b) a]
    rw[absorb2]
    apply inf_le_left
    rw[sup_comm (a ⊓ b) c]
    rw[h c a b]
    apply le_inf
    apply le_trans
    apply inf_le_left
    apply le_sup_right
    apply le_trans
    apply inf_le_right
    rw[sup_comm b c]

  · show  a ⊓ b ⊔ a ⊓ c ≤ a ⊓ (b ⊔ c)
    rw[h (a ⊓ b) a c]
    apply le_inf
    rw[sup_comm (a ⊓ b) a]
    rw[absorb2]
    apply inf_le_left
    apply le_trans
    apply inf_le_right
    apply sup_le
    apply le_trans
    apply inf_le_right
    apply le_sup_left
    apply le_sup_right

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_right : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  exact sub_nonneg.mpr h

-- dont know how to use add_le_add_left or right to solve this

  --apply add_le_add_right ( c:= -a) at h

  --rw[← sub_self a]
  --rw[sub_self]

  --another way to solve it:
example (h : a ≤ b) : 0 ≤ b - a := by
 calc
    0 = a - a := (sub_self a).symm
    _ ≤ b - a := sub_le_sub_right h a

--example (h : a ≤ b) : 0 ≤ b - a := by
 --apply sub_le_sub_left h a
 --apply sub_self.mp


example (h: 0 ≤ b - a) : a ≤ b := by
  calc
     a = 0+a := (zero_add a).symm
     _≤ b-a+a := add_le_add_left h a
     _=b+-a+a := congrArg (· + a) (sub_eq_add_neg b a)
     _=b+(-a+a):= add_assoc b (-a) a
     _= b+0 := congrArg (b+.) (neg_add_cancel a)
     _=b:= add_zero b


example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h₁: 0 ≤ b - a := by
    exact sub_nonneg.mpr h
  rw[← sub_nonneg]
  rw[← sub_mul]
  exact mul_nonneg  h₁ h'

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
 exact nonneg_of_mul_nonneg_right
  (calc
     0 = dist x x := (dist_self x).symm
     _≤ dist x y + dist y x:= dist_triangle x y x
     _=dist x y + dist x y:=congrArg (dist x y + .) (dist_comm y x)
     _=2* dist x y:= by
      rw[two_mul (dist x y)])
  zero_lt_two

end

Logic S01

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import Mathlib.Order.Lattice
namespace C03S01

#check ∀ x : ℝ, 0 ≤ x → |x| = x

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end

theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro
  apply my_lemma


section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁ ha hb

end

theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  apply my_lemma2 epos ele1 xlt ylt


theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := abs_mul x y
    _ ≤  |x| * ε := by
      have h_yle_eps:= le_of_lt ylt
      apply mul_le_mul_of_nonneg_left  h_yle_eps (abs_nonneg x)
    _ <  1 * ε := by
      have h₁: |x| < 1 := lt_of_lt_of_le xlt ele1
      exact mul_lt_mul_of_pos_right h₁ epos
    _ = ε := one_mul ε


def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

section
variable (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add (hfa x) (hgb x)
  --apply hfa
  --apply hgb

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  dsimp
  apply mul_nonneg
  apply nnf
  apply nng




example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
  intro x
  dsimp
  apply mul_le_mul (hfa x) (hgb x) (nng x) nna

def fnIn (f : ℝ → ℝ) : Prop :=
  ∀ ⦃x y⦄, (y< x→ f y< f x)
def fnDc (f : ℝ → ℝ) : Prop :=
  ∀ ⦃x y⦄, (y<x→ f x < f y)

example  (hfIn: fnIn f)(hgDc :  fnDc g) : fnDc (fun x ↦ f (g x)):= by
  intro x y  (h: y < x)
  dsimp
  have h₁:g x < g y:= by
    apply (hgDc h)
  exact (hfIn h₁)

end

section
variable {α : Type*} {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedCancelAddMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)

end

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h

section
variable (f g : ℝ → ℝ)

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb
  apply add_le_add
  apply mf aleb
  apply mg aleb

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun _a _b aleb ↦ add_le_add (mf aleb) (mg aleb)

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
 intro x y xley
 apply mul_le_mul_of_nonneg_left (mf xley) nnc

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  intro x y xley
  exact mf (mg xley)


def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]


example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  intro x
  calc
    (fun x ↦ f x * g x) x = f x * g x := rfl
    _ = (-f (-x)) *( -g (-x)) := by rw [of, og]
    _ = (f (-x) ) * (g (-x)):= neg_mul_neg (f (-x )) (g (-x))

#check neg_mul_neg

example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro x
  calc
    (fun x ↦ f x * g x) x = f x * g x := rfl
    _ = f (-x) * -g (-x) := by rw [ef, og]
    _ = -(f (-x)  * g (-x)):= mul_neg (f (-x )) (g (-x))

#check mul_neg

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  calc
    (fun x ↦ f ( g x)) x = f (g x) := rfl
    _ = f (-g (-x)) := by rw[og]
    _ = f (g (-x)) := by rw[← ef]
    _ = (fun x↦ f (g x)) (-x) := rfl

end

section

variable {α : Type*} (r s t : Set α)

example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s := fun _x xs ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  intro h₁ h₂ x xr
  have h₃: x∈ s:= by
    apply  h₁ xr
  have h₄: x∈ t:= h₂ h₃
  exact h₄

end

section
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
  intro x xs
  have h₁: x≤ a := h x xs
  apply le_trans h₁
  exact  h'

end

section

open Function

example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
   intro x₁ x₂ h'
   exact mul_left_cancel₀ h h'

#check mul_left_cancel₀

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro x y h
  exact injf (injg h)

end

/-
import Mathlib.Tactic
import Mathlib.Order.Lattice

variable {α : Type*} [Lattice α]
variable (a b c : α)


example (h : ∀ x y z : α, x ⊓  y ⊔  z = (x ⊓  y) ⊔  (x ⊓  z)) :
    a ⊔  (b ⊓  c) = a ⊔  b ⊓  a ⊔  c := by
  symm
  calc
    a ⊔  b ⊓  a ⊔ c = ((a ⊓ b) ⊔ a) ⊓ ((a ⊓ b) ⊔ c) := by rw [h]
    _ = a ⊓ ((a ⊓ b) ⊔ c) := by rw [sup_comm (a ⊓ b) a, sup_inf_self]
    _ = a ⊓ (c ⊔ a ⊓ b) := by rw [sup_comm]
    _ = a ⊓ ((c ⊔ a) ⊓ (c ⊔ b)) := by rw [h]
    _ = (a ⊓ (c ⊔ a)) ⊓ (c ⊔ b) := by rw [inf_assoc]
    _ = a ⊓ (c ⊔ b) := by rw [inf_sup_self]
    _ = a ⊓ (b ⊔ c) := by rw [sup_comm c b]
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option autoImplicit true

namespace C03S02

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h1 : 2 < (5 : ℝ) / 2 := by norm_num
  have h2 : (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2, h1, h2

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  ⟨5 / 2, h⟩

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  ⟨5 / 2, by norm_num⟩

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) :=
      fun x↦ add_le_add (hfa x) (hgb x)

theorem fnLb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnLb f a) (hgb : FnLb g b) :
    FnLb (fun x ↦ f x + g x) (a + b) :=
      fun x↦ add_le_add (hfa x) (hgb x)

section

variable {f g : ℝ → ℝ}

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  use a + b
  apply fnUb_add ubfa ubgb

example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  rcases lbf with ⟨a, lbfa⟩
  rcases lbg with ⟨b, lbgb⟩
  use a + b
  apply fnLb_add lbfa lbgb

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  rcases ubf with ⟨a, ubfa⟩
  use c * a
  intro x
  --have h₁: (fun x ↦ c * f x) x= c* f x := rfl
  apply mul_le_mul_of_nonneg_left (ubfa x) h



example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

--rintro makes rcases of the given hypothesis (wich do not have names) It doesnt need to name the hypothesis unlike in the previous example, ubf. Or  else, we can use intro to name the hypothesis, and then rcases.

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x :=
  fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, fnUb_add ubfa ubgb⟩

end

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  obtain ⟨a, ubfa⟩ := ubf
  obtain ⟨b, ubgb⟩ := ubg
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  case intro a ubfa =>
    cases ubg
    case intro b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  next a ubfa =>
    cases ubg
    next b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x :=
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      ⟨a + b, fnUb_add ubfa ubgb⟩

section

variable {α : Type*} [CommRing α]

def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq⟩
  rcases sosy with ⟨c, d, yeq⟩
  rw [xeq, yeq]
  use a * c - b * d, a * d + b * c
  ring

theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, rfl⟩
  rcases sosy with ⟨c, d, rfl⟩
  use a * c - b * d, a * d + b * c
  ring

end

section
variable {a b c : ℕ}

example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, beq⟩
  rcases divbc with ⟨e, ceq⟩
  rw [ceq, beq]
  use d * e; ring

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨d, beq⟩
  rcases divac with ⟨e, ceq⟩
  rw [ceq, beq]
  use d + e; ring

end

section

open Function

example {c : ℝ} : Surjective fun x ↦ x + c := by
  intro y
  use y - c
  dsimp; ring

example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro y
  use c⁻¹ * y
  dsimp; ring_nf
  rw[mul_inv_cancel₀ h]
  exact one_mul y
 -- field_simp[h] (this on eline can replace all calculations here)

#check inv_mul_cancel

example (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  field_simp [h]
  ring

example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  rcases h 2 with ⟨x, hx⟩
  use x
  rw [hx]
  norm_num

end

section
open Function
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  intro z
  rcases surjg z with ⟨y, surjgy⟩
  rcases surjf y with ⟨x, surjfx⟩
  use x
  simp[surjfx, surjgy]


end
#check congrArg


import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith


example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnlb
  rcases fnlb with ⟨ a, fnlba⟩
  rcases h a with ⟨x, hx⟩
  linarith [fnlba x]



example : ¬FnHasUb fun x ↦ x := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  linarith [fnuba (a+1)]



#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro h₁
  have h₂: f b≤ f a:= h h₁
  linarith [h', h₂]

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro h₁
  have h₂: f a ≤ f b:= h₁ h
  linarith [h₂, h']

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro a b h₁
    apply le_refl 0
   --use h f 1 0
  have hf: f 1 ≤ f 0:= le_refl 0
  have hf01 : (1 : ℝ) ≤ (0 : ℝ) := h monof  hf
   --h (f := f) monof (a := 1) (b := 0) hf
  have h01: ¬ (1:ℝ) ≤ (0:ℝ):= not_le_of_gt zero_lt_one
  --linarith [monof, hf, h01]
  --exact h01 hf01 (In the exact statement the order of h01 and hf01 cannot be interchanged.)(either of these two lines can replace the last line here. Bu)
  contradiction



example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro h'
  linarith  [h x h']

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x h'
  push Not at h
  have h₂: ¬ P x := h x
  --specialize h x
  contradiction
--Same problem without use of push Not

  example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
    intro x h'
    apply h
    exact ⟨x, h'⟩





example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro h'
  rcases h' with ⟨x, h'x⟩
  exact (h x h'x)


example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  push Not at h
  rcases h with ⟨x, hx⟩
  use x


example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  push Not
  exact h

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra h'
  exact h h'

example (h : Q) : ¬¬Q := by
  intro h'
  exact h' h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  push Not at h'
  have h₂: FnUb f a:= h'
  have h₃: FnHasUb f:=by
    use a
  contradiction





example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  by_contra h'
  push Not at h'
  have h₁: Monotone f:=h'
  contradiction



example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic

namespace C03S04

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  intro h
  apply h₁
  rw [h]

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  ⟨h₀, h⟩

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  exact h₁ (le_antisymm h₀ h')

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  match h with
    | ⟨h₀, h₁⟩ =>
        contrapose! h₁
        exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  apply h.right
  exact le_antisymm h.left h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  constructor
  · exact h.left
  intro h'
  have h₁: m=n := by
    exact dvd_antisymm h.left h'
  exact h.right h₁

/- Same example: the harder proof without dvd_antisymm-/

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  constructor
  · exact h.left
  intro h'
  have h₁: m ≠ 0:= by
    by_contra h₂
    have h₃: ∃ (k:ℕ ), n=m*k:= h.left
    rcases h₃ with ⟨k, h1k⟩
    have h₄: n=0:= by
      rw[h₂] at h1k
      rw[zero_mul k] at h1k
      exact h1k
    have h₅:n=m:= by
       linarith
    exact h.right.symm h₅
  apply h.right
  have h₆: ∃ (k:ℕ ), n=m*k:= h.left
  have h₇ : ∃ (l:ℕ), m=n*l:= h'
  rcases h₆ with ⟨k, h6k⟩
  rcases h₇ with ⟨l, h7l⟩
  rw[h6k] at h7l
  rw[mul_assoc] at h7l
  nth_rw 1[← mul_one m] at h7l
  have h₈:1=k*l:= by
    rw[mul_left_cancel₀ h₁ h7l]
  have h₉: k=1 := by
    exact Nat.eq_one_of_mul_eq_one_right h₈.symm
  rw[h₉] at h6k
  rw[mul_one] at h6k
  exact h6k.symm


#check Nat.eq_one_of_mul_eq_one_right
#check mul_left_cancel₀
#check mul_self_eq_zero
#check zero_mul
#check dvd_antisymm


example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  ⟨5 / 2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

/- the same example without rintro-/
example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  intro h                 -- h : ∃ z, x < z ∧ z < y
  rcases h with ⟨z, h_and⟩ -- z : ℝ, h_and : x < z ∧ z < y
  rcases h_and with ⟨xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨_z, xltz, zlty⟩ ↦ lt_trans xltz zlty

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num

example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩
  use h₀
  exact fun h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose
    rintro rfl
    --(the above line introduces the hypothesis x=y and also because of "rfl" in rintro, it replaces every y with x. So that the goal y≤ x now becomes x≤ x.)
    rfl
    --(the above line is using le_rfl to x≤ x,  to finish the proof. It need not specify le_rfl, lean 4 knows how to look at a stement and decide which rfl to use)
  contrapose
  exact le_antisymm h

/- my proof of the same example-/

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · intro h'
    apply lt_of_not_ge at h'
    linarith
  intro h' h₁
  exact h' (le_antisymm h h₁)

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · exact h₁
    intro h₃
    have h₄: y≤ x:= by
     linarith
    exact h₂ h₄
  rintro ⟨h₁, h₂⟩
  constructor
  · exact h₁
  contrapose h₂
  exact le_antisymm h₁ h₂



theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 := by
  have h' : x ^ 2 = 0 := by
    have h₁: x^2≥ 0:= sq_nonneg x
    have h₂: y^2≥ 0:= sq_nonneg y
    linarith [h₁, h₂]
  exact eq_zero_of_pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · have h₁: x^2≥ 0:= sq_nonneg x
      have h₂: y^2≥ 0:= sq_nonneg y
      have hx : x ^ 2 = 0 := by
        linarith [h₁, h]
      exact eq_zero_of_pow_eq_zero hx

    · have h₁: x^2≥ 0:= sq_nonneg x
      have h₂: y^2≥ 0:= sq_nonneg y
      have hy : y ^ 2 = 0 := by
        linarith [h₂, h]
      exact eq_zero_of_pow_eq_zero hy

  · rintro ⟨h₁, h₂⟩
    rw[h₁]
    norm_num
    exact h₂

/-very difficult because of indentation. Should be very careful where I start the line where to place dots. I think constructor is very sensitive to indentation -/




section

example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num

end

theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl

example : ¬Monotone fun x : ℝ ↦ -x := by
  rw[not_monotone_iff]
  use 1, 2
  --constructor <;> linarith
  norm_num

/- constructor line also works, above-/

section
variable {α : Type*} [PartialOrder α]
variable (a b : α)

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_ge]
  constructor
  · intro h
    constructor
    · exact h.left
    · have hr:¬ b≤ a:= h.right
      rw[le_iff_lt_or_eq ] at hr
      push Not at hr
      exact hr.right.symm
  · intro h
    constructor
    · exact h.left
    · by_contra h₁
      have h₂: a = b := le_antisymm h.left h₁
      exact h.right h₂




#check lt_of_not_ge
#check le_antisymm_iff
#check le_antisymm

end

section
variable {α : Type*} [Preorder α]
variable (a b c : α)

example : ¬a < a := by
  rw [lt_iff_le_not_ge]
  by_contra h
  exact h.right h.left



example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_ge]
  intro h₁ h₂
  constructor
  · exact le_trans h₁.left h₂.left
  · by_contra h₃
    have h₄: b≤ a:= le_trans h₂.left h₃
    exact h₁.right h₄

C03 S05



import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_iff_left₀ _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h
  /-convert lets you apply theorems without having the assumptions necessary for the conditions, It will give you those goals one by one, to prove later .2 is used to the reverse direction for an iff conditon just like ← but you cant use ← inside convert. Also the names of the goals e'_3, convert_2 are given by the system we can change it manutally -/

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  simp
  intro n h₁ h₂
  specialize  hs n
  specialize  ht n
  --ring_nf
  have h₃: |s n + t n - (a + b)|≤  |s n  - a| + |t n - b|:=
    calc
      |s n + t n - (a + b)| = |(s n - a) + (t n - b)|:= by
       --(ring_nf will do)
        congr 1
        ring

      _                    ≤ |s n - a| + |t n - b| := abs_add_le (s n - a) (t n - b)

  have hsn:|s n - a| < ε / 2:= by
    exact (hs h₁)
  have htn:|t n - b| < ε / 2:= by
    exact (ht h₂)
  linarith [h₃, hsn, htn]


#check abs_add_le






theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  push Not at h
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have εcpos : 0 < ε / |c| := by positivity
   --aesop also works
  rcases cs (ε / |c|) εcpos with ⟨N, hc⟩

  use N
  simp
  intro n hn
  rw[← mul_sub_left_distrib]
  rw[abs_mul c (s n -a)]
  apply hc at hn
  have h3: |c| * |s n - a| < |c| * (ε / |c|) := by
    apply (mul_lt_mul_iff_right₀ acpos).2 hn
  field_simp at h3
  exact h3




  --apply aesop

#check abs_mul
#check div_lt_div_of_pos_left

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) : ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n h₁
  specialize h n h₁
  have h₂: |s n| = |a + (s n -a)|:= by ring_nf
  have h₃: |s n|≤ |a|+|(s n-a)|:= by
    rw[h₂]
    exact abs_add_le a (s n - a)
  have h₄: |a| + |(s n-a)| < |a| + 1 := by
    exact add_lt_add_right h |a|
  exact lt_of_le_of_lt h₃ h₄

#check add_lt_add_right

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  --can fill the first _ by s N₀ and the second _ by N₀ in the line above
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  simp at h₁
  simp
  use max N₀ N₁
  intro n h₂
  have h₃: |s n| * |t n|< B* (ε/B):= by
    have h₄: N₀≤ n:= le_trans (le_max_left N₀ N₁) h₂
    have h₅: N₁≤ n:= le_trans (le_max_right N₀ N₁) h₂
      --exact [h₀, le_trans (_ h₂)]
    --apply le_of_lt at h₀
    exact mul_lt_mul_of_nonneg_of_pos (h₀ n h₄) (h₁ n h₅).le (abs_nonneg _) pos₀
  field_simp at h₃
  exact h₃


#check mul_lt_mul_of_lt_of_lt
#check mul_lt_mul
#check lt_of_le_of_lt
#check mul_lt_mul_of_pos_of_nonneg
#check mul_lt_mul_of_nonneg_of_pos

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have h₁: |a - b| > 0 := by
    by_contra h
    push Not at h
    have h₂:|a-b| = 0 := by
      exact le_antisymm  h (abs_nonneg (a-b))
    have h₃: a = b := by
      rw[abs_eq_zero] at h₂
      linarith
    exact abne h₃
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    have h₁: Na ≤ N:= le_max_left Na Nb
    exact hNa N h₁
  have absb : |s N - b| < ε := by
    have h₂: Nb ≤ N:= le_max_right Na Nb
    exact hNb N h₂
  have : |a - b| < |a - b| := by
    --have h₃: a-b = (s N-b)-(s N-a):= by linarith
    calc
      |a-b| ≤  |a - s N| + |s N-b| := abs_sub_le a (s N) b
      _     =  |s N - a| + |s N-b| := by rw[abs_sub_comm a (s N)]
      _     <     ε      +    ε    := by linarith
--the last "by linarith" ca, be replaced by add_lt_add absa absb (without by)
      _     =  |a-b|               := by dsimp[ε ]; ring

  exact lt_irrefl _ this


#check sub_eq_zero_of_eq
#check abs_nonneg
#check abs_eq_zero
#check abs_add_le
#check abs_sub_abs_le_abs_add
#check abs_sub_le
#check abs_sub_comm
section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
