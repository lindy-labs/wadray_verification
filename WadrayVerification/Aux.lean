import CorelibVerification.Aux.ZMod
import Aegis.Aux.Bool
import Aegis.Aux.ZMod.DivMod

open Sierra

theorem ZMod.cast_rat_nonneg [NeZero n] (a : ZMod n) : 0 ≤ (a.cast : ℚ) := by
  cases n; cases NeZero.ne 0 rfl
  rcases a with ⟨a, ha⟩
  simp only [ZMod.cast, ZMod.val, Nat.cast_eq_zero]
  exact Nat.cast_nonneg a

@[simp]
theorem ZMod.zero_eq_cast_rat_iff [NeZero n] (a : ZMod n) : (0 = (a.cast : ℚ)) ↔ a = 0 := by
 rw [eq_comm, ZMod.cast_rat_eq_zero_iff]

theorem ZMod.cast_rat_injective [NeZero n] : Function.Injective (ZMod.cast : ZMod n → ℚ) := by
  cases n; cases NeZero.ne 0 rfl
  intro a b
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  simp only [cast, val, Nat.cast_inj]
  rintro rfl
  rfl

theorem ZMod.cast_rat_of_cast_nat {m : ℕ} [NeZero m] (n : ℕ) : ((n : ZMod m) : ℚ) = n % m := by
  cases m; cases NeZero.ne 0 rfl
  rfl

attribute [simp] ZMod.cast_rat_eq_zero_iff

theorem ZMod.cast_rat_le_cast_rat_of_val_le_val {m : ℕ} [NeZero m] {a b : ZMod m}
    (h : a.val ≤ b.val) : (a : ℚ) ≤ b := by
  cases m; cases NeZero.ne 0 rfl
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  simp [cast, val] at *
  assumption

theorem ZMod.cast_rat_lt_cast_rat_of_val_lt_val {m : ℕ} [NeZero m] {a b : ZMod m}
    (h : a.val < b.val) : (a : ℚ) < b := by
  cases m; cases NeZero.ne 0 rfl
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  simp [cast, val] at *
  assumption

theorem ZMod.cast_nat_cast_of_lt {m k : ℕ} [NeZero m] {R : Type u_1} [Ring R] (h : k < m) :
    ((k : ZMod m) : R) = k := by
  cases m; cases NeZero.ne 0 rfl
  simp only [cast, Nat.cast, NatCast.natCast, val, Nat.add_eq, Nat.add_zero, Fin.ofNat_eq_val,
    Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt h]

def Wad : Type := UInt128

namespace Wad

def WAD_SCALE : ℕ := 1000000000000000000

theorem WAD_SCALE_pos : 0 < WAD_SCALE := by norm_num[WAD_SCALE]

theorem WAD_SCALE_lt_U128_MOD : WAD_SCALE < U128_MOD := by norm_num [WAD_SCALE, U128_MOD]

variable (w w' : Wad)

protected def toZMod : UInt128 := w

protected def ofZMod (a : UInt128) : Wad := a

protected def toRat : ℚ := w.toZMod.val / WAD_SCALE

theorem toRat_le_toRat_of_val_le_val (h : @ZMod.val U128_MOD w ≤ @ZMod.val U128_MOD w') :
    w.toRat ≤ w'.toRat := by
  simp only [Wad.toRat]
  apply div_le_div
  · exact Nat.cast_nonneg (ZMod.val (Wad.toZMod w'))
  · rwa [Nat.cast_le]
  · norm_num[WAD_SCALE]
  · apply le_of_eq; rfl

theorem toRat_lt_toRat_of_val_lt_val (h : @ZMod.val U128_MOD w < @ZMod.val U128_MOD w') :
    w.toRat < w'.toRat := by
  simp only [Wad.toRat]
  apply div_lt_div
  · rwa [Nat.cast_lt, Wad.toZMod, Wad.toZMod]
  · apply le_of_eq; rfl
  · apply Nat.cast_nonneg
  · norm_num[WAD_SCALE]

theorem toRat_injective : Function.Injective Wad.toRat := by
  intro a b h
  by_contra hne
  have : a.toZMod.val ≠ b.toZMod.val
  · intro h'; have := ZMod.val_injective _ h'; simp_all [Wad.toZMod]
  have : a.toZMod.val < b.toZMod.val ∨ b.toZMod.val < a.toZMod.val
  · aesop
  rcases this with (h'|h')
  <;> · have := toRat_lt_toRat_of_val_lt_val _ _ h'
        simp only [toZMod._eq_1] at this
        linarith

theorem toRat_nonneg : 0 ≤ w.toRat := by
  simp [Wad.toRat]
  rw [le_div_iff (by norm_num [WAD_SCALE]), zero_mul]
  exact ZMod.cast_rat_nonneg (Wad.toZMod w)

protected def mul : Wad := (w.toZMod.val * w'.toZMod.val / WAD_SCALE  : UInt128)

instance : Mul Wad := ⟨Wad.mul⟩

protected theorem mul_def :
    w * w' = (w.toZMod.val * w'.toZMod.val / WAD_SCALE  : UInt128) :=
  rfl

protected def div : Wad := (w.toZMod.val * WAD_SCALE / w'.toZMod.val : UInt128)

instance : Div Wad := ⟨Wad.div⟩

protected theorem div_def :
    w / w' = (w.toZMod.val * WAD_SCALE / w'.toZMod.val : UInt128) :=
  rfl

protected def sub : Wad := w.toZMod - w'.toZMod

instance : Sub Wad := ⟨Wad.sub⟩

protected theorem sub_def :
    w - w' = w.toZMod - w'.toZMod :=
  rfl

protected def add : Wad := w.toZMod + w'.toZMod

instance : Add Wad := ⟨Wad.add⟩

protected theorem add_def :
    w + w' = w.toZMod + w'.toZMod :=
  rfl

protected def zero : Wad := (0 : UInt128)

instance : Zero Wad := ⟨Wad.zero⟩

@[simp]
protected theorem zero_toZMod :
    (0 : Wad).toZMod = 0 :=
  rfl

@[simp]
theorem toRat_zero : (0 : Wad).toRat = 0 := by simp [Wad.toRat]

end Wad

def Ray : Type := UInt128

namespace Ray

def RAY_SCALE : ℕ := 1000000000000000000000000000

theorem RAY_SCALE_pos : 0 < RAY_SCALE := by norm_num[RAY_SCALE]

theorem RAY_SCALE_lt_U128_MOD : RAY_SCALE < U128_MOD := by norm_num [RAY_SCALE, U128_MOD]

variable (r r' : Ray)

protected def toZMod : UInt128 := r

protected def ofZMod (a : UInt128) : Ray := a

protected def toRat : ℚ := r.toZMod.val / RAY_SCALE

protected def mul : Ray := (r.toZMod.val * r'.toZMod.val / RAY_SCALE  : UInt128)

instance : Mul Ray := ⟨Ray.mul⟩

protected theorem mul_def :
    r * r' = (r.toZMod.val * r'.toZMod.val / RAY_SCALE  : UInt128) :=
  rfl

protected def div : Ray := (r.toZMod.val * RAY_SCALE / r'.toZMod.val : UInt128)

instance : Div Ray := ⟨Ray.div⟩

protected theorem div_def :
    r / r' = (r.toZMod.val * RAY_SCALE / r'.toZMod.val : UInt128) :=
  rfl

def DIFF : ℕ := 1000000000

def toWad : Wad := r.toZMod.ndiv DIFF

protected def add : Ray := r.toZMod + r'.toZMod

instance : Add Ray := ⟨Ray.add⟩

protected theorem add_def :
    r + r' = r.toZMod + r'.toZMod :=
  rfl

protected def sub : Ray := r.toZMod - r'.toZMod

instance : Sub Ray := ⟨Ray.sub⟩

protected theorem sub_def :
    r - r' = r.toZMod - r'.toZMod :=
  rfl

theorem toRat_le_toRat_of_val_le_val (h : @ZMod.val U128_MOD r ≤ @ZMod.val U128_MOD r') :
    r.toRat ≤ r'.toRat := by
  simp only [Ray.toRat]
  apply div_le_div
  · exact Nat.cast_nonneg (ZMod.val (Wad.toZMod r'))
  · rwa [Nat.cast_le]
  · norm_num[RAY_SCALE]
  · apply le_of_eq; rfl

theorem toRat_lt_toRat_of_val_lt_val (h : @ZMod.val U128_MOD r < @ZMod.val U128_MOD r') :
    r.toRat < r'.toRat := by
  simp only [Ray.toRat]
  apply div_lt_div
  · rwa [Nat.cast_lt, Ray.toZMod, Ray.toZMod]
  · apply le_of_eq; rfl
  · apply Nat.cast_nonneg
  · norm_num[RAY_SCALE]

theorem toRat_injective : Function.Injective Ray.toRat := by
  intro a b h
  by_contra hne
  have : a.toZMod.val ≠ b.toZMod.val
  · intro h'; have := ZMod.val_injective _ h'; simp_all [Ray.toZMod]
  have : a.toZMod.val < b.toZMod.val ∨ b.toZMod.val < a.toZMod.val
  · aesop
  rcases this with (h'|h')
  <;> · have := toRat_lt_toRat_of_val_lt_val _ _ h'
        simp only [toZMod._eq_1] at this
        linarith

theorem toRat_nonneg : 0 ≤ r.toRat := by
  simp [Ray.toRat]
  rw [le_div_iff (by norm_num [RAY_SCALE]), zero_mul]
  exact ZMod.cast_rat_nonneg (Ray.toZMod r)

protected def zero : Ray := (0 : UInt128)

instance : Zero Ray := ⟨Ray.zero⟩

@[simp]
protected theorem zero_toZMod :
    (0 : Ray).toZMod = 0 :=
  rfl

 @[simp]
theorem toRat_zero : (0 : Ray).toRat = 0 := by simp [Ray.toRat]


end Ray

def Wad.toRay (w : Wad) : Ray := w.toZMod * (Ray.DIFF : UInt128)

def Wad.MAX_CONVERTIBLE_WAD : ℕ := 340282366920938463463374607431

/- Signed Wad -/

def SignedWad := UInt128 × (Unit ⊕ Unit)

namespace SignedWad

instance : Inhabited SignedWad := ⟨default, default⟩

variable (w w₁ w₂ : SignedWad)

def sign := SierraBool.toBool w.2

instance : Zero SignedWad := ⟨(0, false.toSierraBool)⟩

theorem zero_def : (0 : SignedWad) = (0, false.toSierraBool) := rfl

@[simp]
theorem zero_val : (0 : SignedWad).1 = 0 := rfl

@[simp]
theorem zero_sign : (0 : SignedWad).2 = .inl () := rfl

instance : One SignedWad := ⟨(Wad.WAD_SCALE, false.toSierraBool)⟩

theorem one_def : (1 : SignedWad) = ((Wad.WAD_SCALE : UInt128), false.toSierraBool) := rfl

@[simp]
theorem one_val : (1 : SignedWad).1 = (Wad.WAD_SCALE : UInt128) := rfl

@[simp]
theorem one_sign : (1 : SignedWad).2 = .inl () := rfl

/-- Give `SignedWad` a meaning by mapping it to the rationals. -/
def toRat : ℚ := if w.2 then -(Wad.toRat w.1) else Wad.toRat w.1

theorem toRat_eq_zero_iff : w.toRat = 0 ↔ w.1 = 0 := by
  have := Wad.WAD_SCALE_pos
  rcases w with ⟨w, (s|s)⟩ <;> cases s
  <;> simp only [SignedWad.toRat, Wad.toRat, Wad.toZMod]
  <;> aesop (add simp ZMod.cast_rat_eq_zero_iff)

@[simp]
theorem toRat_zero : (0 : SignedWad).toRat = 0 := by
  rfl

@[simp]
theorem toRat_zero_val : SignedWad.toRat ((0, s) : SignedWad) = 0 := by
  cases s <;> simp [toRat, Wad.toRat]

@[simp]
theorem toRat_one : (1 : SignedWad).toRat = 1 := by
  have : (Wad.WAD_SCALE : ℚ) ≠ 0
  · norm_num [Wad.WAD_SCALE]
  simp_all [toRat, Wad.toRat, Wad.toZMod, ZMod.cast_rat_of_cast_nat,
    Nat.mod_eq_of_lt Wad.WAD_SCALE_lt_U128_MOD]

theorem val_eq_of_toRat_eq : w₁.toRat = w₂.toRat → w₁.1 = w₂.1 := by
  rcases w₁ with ⟨w₁, s₁⟩
  rcases w₂ with ⟨w₂, s₂⟩
  intro h
  cases s₁ <;> cases s₂
  · have := Wad.toRat_injective h
    cases this
    rfl
  · simp only [toRat, SierraBool_toBool_inl, ite_false, SierraBool_toBool_inr, ite_true] at *
    have h' : Wad.toRat w₁ = 0
    · apply Rat.le_antisymm _ _
      · rw [h, Left.neg_nonpos_iff]
        apply Wad.toRat_nonneg
      · apply Wad.toRat_nonneg
    rw [h', zero_eq_neg, ← Wad.toRat_zero] at h
    have := Wad.toRat_injective h; cases this
    rw [← Wad.toRat_zero] at h'
    have := Wad.toRat_injective h'; cases this
    rfl
  · simp only [toRat, SierraBool_toBool_inr, ite_true, SierraBool_toBool_inl, ite_false] at *
    have h' : Wad.toRat w₂ = 0
    · apply Rat.le_antisymm _ _
      · rw [← h, Left.neg_nonpos_iff]
        apply Wad.toRat_nonneg
      · apply Wad.toRat_nonneg
    rw [h', eq_comm, zero_eq_neg, ← Wad.toRat_zero] at h
    have := Wad.toRat_injective h; cases this
    rw [← Wad.toRat_zero] at h'
    have := Wad.toRat_injective h'; cases this
    rfl
  · simp only [toRat, SierraBool_toBool_inr, ite_true, neg_inj] at h
    have := Wad.toRat_injective h
    cases this
    rfl

theorem val_eq_zero_of_toRat_neg (x : Wad) (p q : Unit)
  (h : SignedWad.toRat ((x, .inl p) : SignedWad) = SignedWad.toRat ((x, .inr q) : SignedWad)) :
    x = 0 := by
  simp only [toRat, SierraBool_toBool_inl, ite_false, SierraBool_toBool_inr, ite_true,
    eq_neg_self_iff] at h
  rw [← Wad.toRat_zero] at h
  exact Wad.toRat_injective h

theorem val_eq_zero_of_toRat_neg' (x : Wad) (p q : Unit)
  (h : SignedWad.toRat ((x, .inr p) : SignedWad) = SignedWad.toRat ((x, .inl q) : SignedWad)) :
    x = 0 := by
  simp only [toRat, SierraBool_toBool_inr, ite_true, SierraBool_toBool_inl, ite_false,
    neg_eq_self_iff] at h
  rw [← Wad.toRat_zero] at h
  exact Wad.toRat_injective h

theorem toRat_le_toRat_of_val_le_val_inl {x y : Wad} (h : x.toZMod.val ≤ y.toZMod.val) :
    SignedWad.toRat (x, .inl ()) ≤ SignedWad.toRat (y, .inl ()) := by
  simp only [Wad.toZMod] at h
  simp [SignedWad.toRat, Wad.toRat_le_toRat_of_val_le_val _ _ h]

theorem toRat_le_toRat_of_val_ge_val_inr {x y : Wad} (h : y.toZMod.val ≤ x.toZMod.val) :
    SignedWad.toRat (x, .inr ()) ≤ SignedWad.toRat (y, .inr ()) := by
  simp only [Wad.toZMod] at h
  simp [SignedWad.toRat, Wad.toRat_le_toRat_of_val_le_val _ _ h]

theorem toRat_inr_le_toRat_inl {x y : Wad} :
    SignedWad.toRat (x, .inr ()) ≤ SignedWad.toRat (y, .inl ()) := by
  apply le_trans (b := 0)
  · simp [toRat, Wad.toRat_nonneg]
  · apply Wad.toRat_nonneg

end SignedWad

def SignedRay := UInt128 × (Unit ⊕ Unit)

namespace SignedRay

instance : Inhabited SignedRay := ⟨default, default⟩

variable (w w₁ w₂ : SignedRay)

def sign := SierraBool.toBool w.2

instance : Zero SignedRay := ⟨(0, false.toSierraBool)⟩

theorem zero_def : (0 : SignedRay) = (0, false.toSierraBool) := rfl

@[simp]
theorem zero_val : (0 : SignedRay).1 = 0 := rfl

@[simp]
theorem zero_sign : (0 : SignedRay).2 = .inl () := rfl

instance : One SignedRay := ⟨(Ray.RAY_SCALE, false.toSierraBool)⟩

theorem one_def : (1 : SignedRay) = ((Ray.RAY_SCALE : UInt128), false.toSierraBool) := rfl

@[simp]
theorem one_val : (1 : SignedRay).1 = (Ray.RAY_SCALE : UInt128) := rfl

@[simp]
theorem one_sign : (1 : SignedRay).2 = .inl () := rfl

/-- Give `SignedWad` a meaning by mapping it to the rationals. -/
def toRat : ℚ := if SierraBool.toBool w.2 then -(Ray.toRat w.1) else Ray.toRat w.1

theorem toRat_eq_zero_iff : w.toRat = 0 ↔ w.1 = 0 := by
  have := Ray.RAY_SCALE_pos
  rcases w with ⟨w, (s|s)⟩ <;> cases s
  <;> simp only [SignedRay.toRat, Ray.toRat, Ray.toZMod]
  <;> aesop (add simp ZMod.cast_rat_eq_zero_iff)

@[simp]
theorem toRat_zero : (0 : SignedRay).toRat = 0 := by
  rfl

@[simp]
theorem toRat_zero_val : SignedRay.toRat ((0, s) : SignedRay) = 0 := by
  cases s <;> simp [toRat, Ray.toRat]

@[simp]
theorem toRat_one : (1 : SignedRay).toRat = 1 := by
  have : (Ray.RAY_SCALE : ℚ) ≠ 0
  · norm_num [Ray.RAY_SCALE]
  simp_all [toRat, Ray.toRat, Ray.toZMod, ZMod.cast_rat_of_cast_nat,
    Nat.mod_eq_of_lt Ray.RAY_SCALE_lt_U128_MOD]

theorem val_eq_of_toRat_eq : w₁.toRat = w₂.toRat → w₁.1 = w₂.1 := by
  rcases w₁ with ⟨w₁, s₁⟩
  rcases w₂ with ⟨w₂, s₂⟩
  intro h
  cases s₁ <;> cases s₂
  · have := Ray.toRat_injective h
    cases this
    rfl
  · simp only [toRat, SierraBool_toBool_inl, ite_false, SierraBool_toBool_inr, ite_true] at *
    have h' : Ray.toRat w₁ = 0
    · apply Rat.le_antisymm _ _
      · rw [h, Left.neg_nonpos_iff]
        apply Ray.toRat_nonneg
      · apply Ray.toRat_nonneg
    rw [h', zero_eq_neg, ← Ray.toRat_zero] at h
    have := Ray.toRat_injective h; cases this
    rw [← Ray.toRat_zero] at h'
    have := Ray.toRat_injective h'; cases this
    rfl
  · simp only [toRat, SierraBool_toBool_inr, ite_true, SierraBool_toBool_inl, ite_false] at *
    have h' : Ray.toRat w₂ = 0
    · apply Rat.le_antisymm _ _
      · rw [← h, Left.neg_nonpos_iff]
        apply Ray.toRat_nonneg
      · apply Ray.toRat_nonneg
    rw [h', eq_comm, zero_eq_neg, ← Ray.toRat_zero] at h
    have := Ray.toRat_injective h; cases this
    rw [← Ray.toRat_zero] at h'
    have := Ray.toRat_injective h'; cases this
    rfl
  · simp only [toRat, SierraBool_toBool_inr, ite_true, neg_inj] at h
    have := Ray.toRat_injective h
    cases this
    rfl

theorem val_eq_zero_of_toRat_neg (x : Ray) (p q : Unit)
  (h : SignedRay.toRat (x, .inl p) = SignedRay.toRat (x, .inr q)) :
    x = 0 := by
  simp only [toRat, SierraBool_toBool_inl, ite_false, SierraBool_toBool_inr, ite_true,
    eq_neg_self_iff] at h
  rw [← Ray.toRat_zero] at h
  exact Ray.toRat_injective h

theorem val_eq_zero_of_toRat_neg' (x : Ray) (p q : Unit)
  (h : SignedRay.toRat (x, .inr p) = SignedRay.toRat (x, .inl q)) :
    x = 0 := by
  simp only [toRat, SierraBool_toBool_inr, ite_true, SierraBool_toBool_inl, ite_false,
    neg_eq_self_iff] at h
  rw [← Ray.toRat_zero] at h
  exact Ray.toRat_injective h

theorem toRat_le_toRat_of_val_le_val_inl {x y : Ray} (h : x.toZMod.val ≤ y.toZMod.val) :
    SignedRay.toRat (x, .inl ()) ≤ SignedRay.toRat (y, .inl ()) := by
  simp only [Ray.toZMod] at h
  simp [SignedRay.toRat, Ray.toRat_le_toRat_of_val_le_val _ _ h]

theorem toRat_le_toRat_of_val_ge_val_inr {x y : Ray} (h : y.toZMod.val ≤ x.toZMod.val) :
    SignedRay.toRat (x, .inr ()) ≤ SignedRay.toRat (y, .inr ()) := by
  simp only [Ray.toZMod] at h
  simp [SignedRay.toRat, Ray.toRat_le_toRat_of_val_le_val _ _ h]

theorem toRat_inr_le_toRat_inl {x y : Ray} :
    SignedRay.toRat (x, .inr ()) ≤ SignedRay.toRat (y, .inl ()) := by
  apply le_trans (b := 0)
  · simp [toRat, Ray.toRat_nonneg]
  · apply Ray.toRat_nonneg

end SignedRay
