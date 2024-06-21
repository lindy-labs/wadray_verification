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

theorem ZMod.cast_rat_of_cast_nat {m : ℕ} [NeZero m] (n : ℕ) : ((n : ZMod m).cast : ℚ) = ↑(n % m) := by
  cases m; cases NeZero.ne 0 rfl
  rfl

attribute [simp] ZMod.cast_rat_eq_zero_iff

theorem ZMod.cast_rat_le_cast_rat_of_val_le_val {m : ℕ} [NeZero m] {a b : ZMod m}
    (h : a.val ≤ b.val) : (a.cast : ℚ) ≤ b.cast := by
  cases m; cases NeZero.ne 0 rfl
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  simp [cast, val] at *
  assumption

theorem ZMod.cast_rat_lt_cast_rat_of_val_lt_val {m : ℕ} [NeZero m] {a b : ZMod m}
    (h : a.val < b.val) : (a.cast : ℚ) < b.cast := by
  cases m; cases NeZero.ne 0 rfl
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  simp [cast, val] at *
  assumption

theorem ZMod.cast_nat_cast_of_lt {m k : ℕ} [NeZero m] {R : Type u_1} [Ring R] (h : k < m) :
    ((k : ZMod m).cast : R) = k := by
  cases m; cases NeZero.ne 0 rfl
  simp only [cast, Nat.cast, NatCast.natCast, val, Nat.add_eq, Nat.add_zero,
    Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt h, Fin.ofNat'']

theorem ZMod.cast_add_of_lt_half' {m n : ℕ} [NeZero m] [NeZero n] (a b : ZMod m)
    (h: a.val + b.val < m) : (a.cast : ZMod n) + (b.cast : ZMod n) = (a + b).cast := by
  cases m; cases NeZero.ne 0 rfl
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  simp only [cast, val, Nat.add_eq, Nat.add_zero]
  simp only [val] at h
  rw [Fin.val_add, Nat.mod_eq_of_lt h, Nat.cast_add]

theorem ZMod.valMinAbs_cast_of_lt_of_le [NeZero m] (hm : m < n) {a : ZMod m}
    (ham : a.val ≤ m / 2) : (a.cast : ZMod n).valMinAbs = a.valMinAbs := by
  rcases m with (⟨⟩|⟨m⟩); · cases NeZero.ne 0 rfl
  rcases n with (⟨⟩|⟨n⟩); · simp at hm
  rcases a with ⟨a, ha⟩
  simp only [val] at ham
  simp only [valMinAbs, val, Nat.add_eq, Nat.add_zero, cast, Nat.cast_succ, ham, ↓reduceIte]
  have : a ≤ n.succ / 2 := by
    apply le_trans ham
    apply Nat.div_le_div_right (le_of_lt hm)
  rw [Fin.val_cast_of_lt (lt_trans ha hm)]
  simp [this]

theorem ZMod.valMinAbs_cast_of_lt_half [NeZero m] (hm : 2 * m < n) (a : ZMod m) :
  (a.cast : ZMod n).valMinAbs = a.val := by
  rcases m with (⟨⟩|⟨m⟩); · cases NeZero.ne 0 rfl
  rcases n with (⟨⟩|⟨n⟩); · simp at hm
  rcases a with ⟨a, ha⟩
  simp only [cast, val, valMinAbs_natCast_eq_self]
  apply le_of_lt (lt_of_lt_of_le ha (le_trans _ (Nat.div_le_div_right (le_of_lt hm))))
  simp

theorem ZMod.valMinAbs_add_of_two_lt [NeZero m] {a b : ZMod m}
    (h : 2 * (a.valMinAbs.natAbs + b.valMinAbs.natAbs) < m) :
    (a + b).valMinAbs = a.valMinAbs + b.valMinAbs := by
  rcases m with (⟨⟩|⟨m⟩); · cases NeZero.ne 0 rfl
  refine' (valMinAbs_spec _ _).2 ⟨_, _, _⟩
  · simp [Int.cast_add]
  · rw [← Nat.cast_lt (α := ℤ), ← neg_lt_neg_iff] at h
    apply lt_of_lt_of_le h
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Int.natCast_natAbs]
    rw [mul_comm, ← neg_mul, mul_le_mul_right two_pos, neg_add]
    apply add_le_add (neg_abs_le (valMinAbs a)) (neg_abs_le (valMinAbs b))
  · rw [← Nat.cast_lt (α := ℤ)] at h
    apply le_of_lt (lt_of_le_of_lt _ h)
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Int.natCast_natAbs]
    rw [mul_comm, mul_add, mul_add]
    apply add_le_add <;> simp only [gt_iff_lt, zero_lt_two, mul_le_mul_left, le_abs_self]

theorem ZMod.valMinAbs_add_of_four_lt [NeZero m] {a b : ZMod m}
    (ha : 4 * a.valMinAbs.natAbs < m) (hb : 4 * b.valMinAbs.natAbs < m) :
    (a + b).valMinAbs = a.valMinAbs + b.valMinAbs := by
  apply valMinAbs_add_of_two_lt
  rw [← mul_lt_mul_left two_pos, ← mul_assoc, mul_add, two_mul m]
  exact add_lt_add ha hb

theorem ZMod.valMinAbs_sub_of_two_lt [NeZero m] {a b : ZMod m}
    (h : 2 * (a.valMinAbs.natAbs + b.valMinAbs.natAbs) < m) :
    (a - b).valMinAbs = a.valMinAbs - b.valMinAbs := by
  rcases m with (⟨⟩|⟨m⟩); · cases NeZero.ne 0 rfl
  refine' (valMinAbs_spec _ _).2 ⟨_, _, _⟩
  · simp [Int.cast_add]
  · rw [← Nat.cast_lt (α := ℤ), ← neg_lt_neg_iff] at h
    apply lt_of_lt_of_le h
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Int.natCast_natAbs]
    rw [mul_comm, ← neg_mul, mul_le_mul_right two_pos, neg_add, ← sub_eq_add_neg]
    apply sub_le_sub (neg_abs_le (valMinAbs a)) (le_abs_self (valMinAbs b))
  · rw [← Nat.cast_lt (α := ℤ)] at h
    apply le_of_lt (lt_of_le_of_lt _ h)
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Int.natCast_natAbs]
    rw [mul_comm, mul_le_mul_left two_pos, sub_eq_add_neg]
    apply add_le_add (le_abs_self (valMinAbs a)) (neg_le_abs (valMinAbs b))

theorem ZMod.valMinAbs_sub_of_four_lt [NeZero m] {a b : ZMod m}
    (ha : 4 * a.valMinAbs.natAbs < m) (hb : 4 * b.valMinAbs.natAbs < m) :
    (a - b).valMinAbs = a.valMinAbs - b.valMinAbs := by
  apply valMinAbs_sub_of_two_lt
  rw [← mul_lt_mul_left two_pos, ← mul_assoc, mul_add, two_mul m]
  exact add_lt_add ha hb

theorem ZMod.val_cast_lt [NeZero m] (n : ℕ) [NeZero n] (a : ZMod m) : (a.cast : ZMod n).val < m := by
  rcases m with (⟨⟩|⟨m⟩); · cases NeZero.ne 0 rfl
  by_cases h : m < n
  · rcases n with (⟨⟩|⟨n⟩); · simp at h
    erw [ZMod.val_cast_of_lt]
    apply ZMod.val_lt a
    apply lt_of_le_of_lt (Nat.le_of_lt_succ (ZMod.val_lt a)) h
  · rw [not_lt] at h
    apply lt_of_lt_of_le (ZMod.val_lt _)
    apply le_trans h
    exact Nat.le_succ m

@[simp]
theorem Option.get!_some [Inhabited α] (a : α) : (Option.some a).get! = a := by rfl

@[simp]
theorem Option.get!_none [Inhabited α] : (.none : Option α).get! = default := by rfl

theorem Rat.nat_cast_div_eq {a b : ℕ} :
    ↑(a / b) = (a : ℚ) / (b : ℚ) - ↑(a % b) / (b : ℚ) := by
  by_cases hb : b = 0
  · subst hb; simp
  · rw [Nat.div_eq_sub_mod_div, Nat.cast_div (Nat.dvd_sub_mod a) (Nat.cast_ne_zero.mpr hb),
      Nat.cast_sub (Nat.mod_le a b), sub_div]


def Wad : Type := UInt128

namespace Wad

instance : Inhabited Wad := ⟨default (α := UInt128)⟩

def WAD_SCALE : ℕ := 1000000000000000000

theorem WAD_SCALE_pos : 0 < WAD_SCALE := by norm_num [WAD_SCALE]

theorem WAD_SCALE_rat_pos : 0 < (WAD_SCALE : ℚ) := by norm_num [WAD_SCALE]

theorem WAD_SCALE_rat_ne_zero : (WAD_SCALE : ℚ) ≠ 0 := by norm_num [WAD_SCALE]

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
  · exact WAD_SCALE_rat_pos
  · apply le_of_eq; rfl

theorem toRat_lt_toRat_of_val_lt_val (h : @ZMod.val U128_MOD w < @ZMod.val U128_MOD w') :
    w.toRat < w'.toRat := by
  simp only [Wad.toRat]
  apply div_lt_div
  · rwa [Nat.cast_lt, Wad.toZMod, Wad.toZMod]
  · apply le_of_eq; rfl
  · apply Nat.cast_nonneg
  · exact WAD_SCALE_rat_pos

theorem toRat_injective : Function.Injective Wad.toRat := by
  intro a b h
  by_contra hne
  have : a.toZMod.val ≠ b.toZMod.val := by
    intro h'; have := ZMod.val_injective _ h'; simp_all [Wad.toZMod]
  have : a.toZMod.val < b.toZMod.val ∨ b.toZMod.val < a.toZMod.val := by
    aesop
  rcases this with (h'|h')
  · apply ne_of_lt (toRat_lt_toRat_of_val_lt_val _ _ h') h
  · apply ne_of_lt (toRat_lt_toRat_of_val_lt_val _ _ h') h.symm

theorem toRat_nonneg : 0 ≤ w.toRat := by
  simp [Wad.toRat]
  rw [le_div_iff WAD_SCALE_rat_pos, zero_mul]
  exact ZMod.cast_rat_nonneg (Wad.toZMod w)

protected def mul : Wad := (w.toZMod.val * w'.toZMod.val / WAD_SCALE : UInt128)

instance : Mul Wad := ⟨Wad.mul⟩

protected theorem mul_def :
    w * w' = (w.toZMod.val * w'.toZMod.val / WAD_SCALE  : UInt128) :=
  rfl

-- TODO use this lemma to clean up proofs downstream
theorem toRat_mul (h : w.toZMod.val * w'.toZMod.val / WAD_SCALE < U128_MOD) :
    |(w * w').toRat - w.toRat * w'.toRat| < 1 / WAD_SCALE := by
  simp only [Wad.toRat, Wad.toZMod, Wad.mul_def, Int.natCast_natAbs] at *
  simp only [ZMod.val_natCast, ZMod.natCast_val] at *
  rw [Nat.mod_eq_of_lt h, div_mul_div_comm, ← div_div, ← sub_div, abs_div,
    Nat.abs_cast, div_lt_div_right WAD_SCALE_rat_pos, Rat.nat_cast_div_eq]
  simp only [Nat.cast_mul, ZMod.natCast_val, sub_sub_cancel_left, abs_neg]
  rw [abs_div, Nat.abs_cast, Nat.abs_cast, div_lt_one WAD_SCALE_rat_pos,
    Nat.cast_lt]
  apply Nat.mod_lt _ WAD_SCALE_pos

protected def div : Wad := (w.toZMod.val * WAD_SCALE / w'.toZMod.val : UInt128)

instance : Div Wad := ⟨Wad.div⟩

protected theorem div_def :
    w / w' = (w.toZMod.val * WAD_SCALE / w'.toZMod.val : UInt128) :=
  rfl

-- TODO use this lemma to clean up proofs downstream
theorem toRat_div (h : w.toZMod.val * WAD_SCALE / w'.toZMod.val < U128_MOD)
    (h' : w'.toZMod.val ≠ 0) :
    |(w / w').toRat - w.toRat / w'.toRat| < 1 / WAD_SCALE := by
  have h'' : 0 < w'.toZMod.val := Nat.pos_of_ne_zero h'
  have h''' : (0 : ℚ) < w'.toZMod.val := Nat.cast_pos.mpr h''
  simp only [Wad.toRat, Wad.toZMod, Wad.div_def, ZMod.val_natCast] at *
  rw [Nat.mod_eq_of_lt h, Rat.nat_cast_div_eq, sub_div, Nat.cast_mul,
    div_div, mul_div_mul_right _ _ WAD_SCALE_rat_ne_zero,
    div_div_div_cancel_right _ WAD_SCALE_rat_ne_zero, sub_sub_cancel_left,
    abs_neg, abs_div, Nat.abs_cast, div_lt_div_right WAD_SCALE_rat_pos,
    abs_div, Nat.abs_cast, Nat.abs_cast, div_lt_one h''', Nat.cast_lt]
  apply Nat.mod_lt _ h''

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

protected def one : Wad := (1000000000000000000 : UInt128)

instance : One Wad := ⟨Wad.one⟩

@[simp]
protected theorem one_toZMod :
    (1 : Wad).toZMod = 1000000000000000000 :=
  rfl

@[simp]
theorem one_val : (1 : Wad).toZMod.val = WAD_SCALE := by
  rfl

theorem one_def : (1 : Wad) = (1000000000000000000 : UInt128) := rfl

end Wad

def Ray : Type := UInt128

namespace Ray

instance : Inhabited Ray := ⟨default (α := UInt128)⟩

def RAY_SCALE : ℕ := 1000000000000000000000000000

theorem RAY_SCALE_pos : 0 < RAY_SCALE := by norm_num[RAY_SCALE]

theorem RAY_SCALE_rat_pos : 0 < (RAY_SCALE : ℚ) := by norm_num [RAY_SCALE]

theorem RAY_SCALE_rat_ne_zero : (RAY_SCALE : ℚ) ≠ 0 := by norm_num [RAY_SCALE]

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

theorem toRat_mul (h : r.toZMod.val * r'.toZMod.val / RAY_SCALE < U128_MOD) :
    |(r * r').toRat - r.toRat * r'.toRat| < 1 / RAY_SCALE := by
  simp only [Ray.toRat, Ray.toZMod, Ray.mul_def] at *
  simp only [ZMod.val_natCast]
  rw [Nat.mod_eq_of_lt h, div_mul_div_comm, ← div_div, ← sub_div, abs_div,
    Nat.abs_cast, div_lt_div_right RAY_SCALE_rat_pos, Rat.nat_cast_div_eq]
  simp only [Nat.cast_mul, ZMod.val_natCast, sub_sub_cancel_left, abs_neg]
  rw [abs_div, Nat.abs_cast, Nat.abs_cast, div_lt_one RAY_SCALE_rat_pos,
    Nat.cast_lt]
  apply Nat.mod_lt _ RAY_SCALE_pos

protected def div : Ray := (r.toZMod.val * RAY_SCALE / r'.toZMod.val : UInt128)

instance : Div Ray := ⟨Ray.div⟩

protected theorem div_def :
    r / r' = (r.toZMod.val * RAY_SCALE / r'.toZMod.val : UInt128) :=
  rfl

-- TODO use this lemma to clean up proofs downstream
theorem toRat_div (h : r.toZMod.val * RAY_SCALE / r'.toZMod.val < U128_MOD)
    (h' : r'.toZMod.val ≠ 0) :
    |(r / r').toRat - r.toRat / r'.toRat| < 1 / RAY_SCALE := by
  have h'' : 0 < r'.toZMod.val := Nat.pos_of_ne_zero h'
  have h''' : (0 : ℚ) < r'.toZMod.val := Nat.cast_pos.mpr h''
  simp only [Ray.toRat, Ray.toZMod, Ray.div_def, ZMod.val_natCast] at *
  rw [Nat.mod_eq_of_lt h, Rat.nat_cast_div_eq, sub_div, Nat.cast_mul,
    div_div, mul_div_mul_right _ _ RAY_SCALE_rat_ne_zero,
    div_div_div_cancel_right _ RAY_SCALE_rat_ne_zero, sub_sub_cancel_left,
    abs_neg, abs_div, Nat.abs_cast, div_lt_div_right RAY_SCALE_rat_pos,
    abs_div, Nat.abs_cast, Nat.abs_cast, div_lt_one h''', Nat.cast_lt]
  apply Nat.mod_lt _ h''

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
  · exact RAY_SCALE_rat_pos
  · apply le_of_eq; rfl

theorem toRat_lt_toRat_of_val_lt_val (h : @ZMod.val U128_MOD r < @ZMod.val U128_MOD r') :
    r.toRat < r'.toRat := by
  simp only [Ray.toRat]
  apply div_lt_div
  · rwa [Nat.cast_lt, Ray.toZMod, Ray.toZMod]
  · apply le_of_eq; rfl
  · apply Nat.cast_nonneg
  · exact RAY_SCALE_rat_pos

theorem toRat_injective : Function.Injective Ray.toRat := by
  intro a b h
  by_contra hne
  have : a.toZMod.val ≠ b.toZMod.val := by
    intro h'; have := ZMod.val_injective _ h'; simp_all [Ray.toZMod]
  have : a.toZMod.val < b.toZMod.val ∨ b.toZMod.val < a.toZMod.val := by
    aesop
  rcases this with (h'|h')
  · apply ne_of_lt (toRat_lt_toRat_of_val_lt_val _ _ h') h
  · apply ne_of_lt (toRat_lt_toRat_of_val_lt_val _ _ h') h.symm

theorem toRat_nonneg : 0 ≤ r.toRat := by
  simp [Ray.toRat]
  rw [le_div_iff RAY_SCALE_rat_pos, zero_mul]
  exact ZMod.cast_rat_nonneg (Ray.toZMod r)

protected def zero : Ray := (0 : UInt128)

instance : Zero Ray := ⟨Ray.zero⟩

@[simp]
protected theorem zero_toZMod :
    (0 : Ray).toZMod = 0 :=
  rfl

 @[simp]
theorem toRat_zero : (0 : Ray).toRat = 0 := by simp [Ray.toRat]

protected def one : Wad := (1000000000000000000000000000 : UInt128)

instance : One Ray := ⟨Ray.one⟩

@[simp]
protected theorem one_toZMod :
    (1 : Ray).toZMod = 1000000000000000000000000000 :=
  rfl

@[simp]
theorem one_val : (1 : Ray).toZMod.val = RAY_SCALE := by
  rfl

theorem one_def : (1 : Ray) = (1000000000000000000000000000 : UInt128) := rfl

end Ray

def Wad.toRay (w : Wad) : Ray := w.toZMod * (Ray.DIFF : UInt128)

def Wad.MAX_CONVERTIBLE_WAD : ℕ := 340282366920938463463374607431

/- Signed Wad -/

def SignedWad := UInt128 × (Unit ⊕ Unit)

namespace SignedWad

instance : Inhabited SignedWad := ⟨default, default⟩

variable (w w₁ w₂ : SignedWad)

def sign : ℤ := if SierraBool.toBool w.2 then -1 else 1

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
  have := Wad.WAD_SCALE_rat_ne_zero
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
    have h' : Wad.toRat w₁ = 0 := by
      apply le_antisymm _ _
      · rw [h, Left.neg_nonpos_iff]
        apply Wad.toRat_nonneg
      · apply Wad.toRat_nonneg
    rw [h', zero_eq_neg, ← Wad.toRat_zero] at h
    have := Wad.toRat_injective h; cases this
    rw [← Wad.toRat_zero] at h'
    have := Wad.toRat_injective h'; cases this
    rfl
  · simp only [toRat, SierraBool_toBool_inr, ite_true, SierraBool_toBool_inl, ite_false] at *
    have h' : Wad.toRat w₂ = 0 := by
      apply le_antisymm _ _
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

theorem toRat_eq_sign_mul : w.toRat = (w.sign : ℚ) * Wad.toRat w.1 := by
  rcases w with ⟨w, s⟩
  simp [toRat, sign, Wad.toRat]

protected def mul : SignedWad :=
⟨Wad.mul (w₁.1 : Wad) (w₂.1 : Wad), Bool.toSierraBool (Bool.xor (SierraBool.toBool w₁.2) (SierraBool.toBool w₂.2))⟩

instance : Mul SignedWad := ⟨SignedWad.mul⟩

theorem mul_def :
    w₁ * w₂ = ⟨Wad.mul (w₁.1 : Wad) (w₂.1 : Wad), Bool.toSierraBool (Bool.xor (SierraBool.toBool w₁.2) (SierraBool.toBool w₂.2))⟩ :=
rfl

theorem toRat_mul (h₁ : w₁.1.val * w₂.1.val / Wad.WAD_SCALE < U128_MOD ):
    |SignedWad.toRat (w₁ * w₂) - SignedWad.toRat w₁ * SignedWad.toRat w₂| < 1 / Wad.WAD_SCALE := by
  rcases w₁ with ⟨w₁, s₁⟩
  rcases w₂ with ⟨w₂, s₂⟩
  rcases s₁ with (⟨⟨⟩⟩|⟨⟨⟩⟩) <;> rcases s₂ with (⟨⟨⟩⟩|⟨⟨⟩⟩)
    <;> dsimp only at h₁
    <;> simp [mul_def, toRat, Wad.mul, Wad.toRat, Wad.toZMod, Nat.mod_eq_of_lt h₁, -one_div]
    <;> rw [Rat.nat_cast_div_eq, Nat.cast_mul, ZMod.natCast_val, ZMod.natCast_val, mul_div_assoc,
      sub_div, div_mul_eq_mul_div]
    <;> [rw [sub_right_comm, sub_self, zero_sub, abs_neg];
       rw [neg_sub, sub_add_cancel];
       rw [neg_sub, sub_add_cancel];
       rw [sub_right_comm, sub_self, zero_sub, abs_neg]]
    <;> rw [abs_div,
      Nat.abs_cast, div_lt_div_right Wad.WAD_SCALE_rat_pos, abs_div, Nat.abs_cast,
      Nat.abs_cast, div_lt_one Wad.WAD_SCALE_rat_pos, Nat.cast_lt]
    <;> apply Nat.mod_lt _ Wad.WAD_SCALE_pos

protected def div : SignedWad :=
⟨Wad.div (w₁.1 : Wad) (w₂.1 : Wad), Bool.toSierraBool (Bool.xor (SierraBool.toBool w₁.2) (SierraBool.toBool w₂.2))⟩

instance : Div SignedWad := ⟨SignedWad.div⟩

theorem div_def :
    w₁ / w₂ = ⟨Wad.div (w₁.1 : Wad) (w₂.1 : Wad), Bool.toSierraBool (Bool.xor (SierraBool.toBool w₁.2) (SierraBool.toBool w₂.2))⟩ :=
rfl

theorem toRat_div (h₁ : w₁.1.val * Wad.WAD_SCALE / w₂.1.val < U128_MOD)
    (h₂ : w₂.1.val ≠ 0):
    |SignedWad.toRat (w₁ / w₂) - SignedWad.toRat w₁ / SignedWad.toRat w₂| < 1 / Wad.WAD_SCALE := by
  rcases w₁ with ⟨w₁, s₁⟩
  rcases w₂ with ⟨w₂, s₂⟩
  rcases s₁ with (⟨⟨⟩⟩|⟨⟨⟩⟩) <;> rcases s₂ with (⟨⟨⟩⟩|⟨⟨⟩⟩)
    <;> dsimp only at h₁ h₂
    <;> simp [div_def, toRat, Wad.div, Wad.toRat, Wad.toZMod, Nat.mod_eq_of_lt h₁, -one_div]
    <;> rw [Rat.nat_cast_div_eq, Nat.cast_mul, ZMod.natCast_val, ZMod.natCast_val, sub_div]
    <;> [rw [div_div_div_cancel_right _ Wad.WAD_SCALE_rat_ne_zero, div_div,
         mul_div_mul_right _ _ Wad.WAD_SCALE_rat_ne_zero,
         sub_right_comm, sub_self, zero_sub, abs_neg];
       rw [neg_sub, div_neg, sub_neg_eq_add, div_div_div_cancel_right _ Wad.WAD_SCALE_rat_ne_zero,
         div_div (w₁.cast * _), mul_div_mul_right _ _ Wad.WAD_SCALE_rat_ne_zero, sub_add_cancel];
       rw [neg_sub, neg_div, sub_neg_eq_add, div_div_div_cancel_right _ Wad.WAD_SCALE_rat_ne_zero,
         div_div (w₁.cast * _), mul_div_mul_right _ _ Wad.WAD_SCALE_rat_ne_zero, sub_add_cancel];
       rw [div_div_div_cancel_right _ Wad.WAD_SCALE_rat_ne_zero, div_div,
         mul_div_mul_right _ _ Wad.WAD_SCALE_rat_ne_zero,
         sub_right_comm, sub_self, zero_sub, abs_neg]]
    <;> rw [abs_div,
      Nat.abs_cast, div_lt_div_right Wad.WAD_SCALE_rat_pos, abs_div, ← ZMod.natCast_val, Nat.abs_cast,
      Nat.abs_cast, div_lt_one (by rw [← Nat.cast_zero, Nat.cast_lt]; apply Nat.pos_of_ne_zero h₂), Nat.cast_lt]
    <;> apply Nat.mod_lt _ (Nat.pos_of_ne_zero h₂)

end SignedWad

def SignedRay := UInt128 × (Unit ⊕ Unit)

namespace SignedRay

instance : Inhabited SignedRay := ⟨default, default⟩

variable (w w₁ w₂ : SignedRay)

def sign : ℤ := if SierraBool.toBool w.2 then -1 else 1

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
  have := Ray.RAY_SCALE_rat_ne_zero
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
    have h' : Ray.toRat w₁ = 0 := by
      apply le_antisymm _ _
      · rw [h, Left.neg_nonpos_iff]
        apply Ray.toRat_nonneg
      · apply Ray.toRat_nonneg
    rw [h', zero_eq_neg, ← Ray.toRat_zero] at h
    have := Ray.toRat_injective h; cases this
    rw [← Ray.toRat_zero] at h'
    have := Ray.toRat_injective h'; cases this
    rfl
  · simp only [toRat, SierraBool_toBool_inr, ite_true, SierraBool_toBool_inl, ite_false] at *
    have h' : Ray.toRat w₂ = 0 := by
      apply le_antisymm _ _
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

theorem toRat_eq_sign_mul : w.toRat = (w.sign : ℚ) * Ray.toRat w.1 := by
  rcases w with ⟨w, s⟩
  simp [toRat, sign, Ray.toRat]

protected def mul : SignedRay :=
⟨Ray.mul w₁.1 w₂.1, Bool.toSierraBool (Bool.xor (SierraBool.toBool w₁.2) (SierraBool.toBool w₂.2))⟩

instance : Mul SignedRay := ⟨SignedRay.mul⟩

theorem mul_def :
    w₁ * w₂ = ⟨Ray.mul w₁.1 w₂.1, Bool.toSierraBool (Bool.xor (SierraBool.toBool w₁.2) (SierraBool.toBool w₂.2))⟩ :=
rfl

theorem toRat_mul (h₁ : w₁.1.val * w₂.1.val / Ray.RAY_SCALE < U128_MOD ):
    |SignedRay.toRat (w₁ * w₂) - SignedRay.toRat w₁ * SignedRay.toRat w₂| < 1 / Ray.RAY_SCALE := by
  rcases w₁ with ⟨w₁, s₁⟩
  rcases w₂ with ⟨w₂, s₂⟩
  rcases s₁ with (⟨⟨⟩⟩|⟨⟨⟩⟩) <;> rcases s₂ with (⟨⟨⟩⟩|⟨⟨⟩⟩)
    <;> dsimp only at h₁
    <;> simp [mul_def, toRat, Ray.mul, Ray.toRat, Ray.toZMod, Nat.mod_eq_of_lt h₁, -one_div]
    <;> rw [Rat.nat_cast_div_eq, Nat.cast_mul, ZMod.natCast_val, ZMod.natCast_val, mul_div_assoc,
      sub_div, div_mul_eq_mul_div]
    <;> [rw [sub_right_comm, sub_self, zero_sub, abs_neg];
       rw [neg_sub, sub_add_cancel];
       rw [neg_sub, sub_add_cancel];
       rw [sub_right_comm, sub_self, zero_sub, abs_neg]]
    <;> rw [abs_div,
      Nat.abs_cast, div_lt_div_right Ray.RAY_SCALE_rat_pos, abs_div, Nat.abs_cast,
      Nat.abs_cast, div_lt_one Ray.RAY_SCALE_rat_pos, Nat.cast_lt]
    <;> apply Nat.mod_lt _ Ray.RAY_SCALE_pos

protected def div : SignedRay :=
⟨Ray.div (w₁.1 : Ray) (w₂.1 : Ray), Bool.toSierraBool (Bool.xor (SierraBool.toBool w₁.2) (SierraBool.toBool w₂.2))⟩

instance : Div SignedRay := ⟨SignedRay.div⟩

theorem div_def :
    w₁ / w₂ = ⟨Ray.div (w₁.1 : Ray) (w₂.1 : Ray), Bool.toSierraBool (Bool.xor (SierraBool.toBool w₁.2) (SierraBool.toBool w₂.2))⟩ :=
rfl

theorem toRat_div (h₁ : w₁.1.val * Ray.RAY_SCALE / w₂.1.val < U128_MOD)
    (h₂ : w₂.1.val ≠ 0):
    |SignedRay.toRat (w₁ / w₂) - SignedRay.toRat w₁ / SignedRay.toRat w₂| < 1 / Ray.RAY_SCALE := by
  rcases w₁ with ⟨w₁, s₁⟩
  rcases w₂ with ⟨w₂, s₂⟩
  rcases s₁ with (⟨⟨⟩⟩|⟨⟨⟩⟩) <;> rcases s₂ with (⟨⟨⟩⟩|⟨⟨⟩⟩)
    <;> dsimp only at h₁ h₂
    <;> simp [div_def, toRat, Ray.div, Ray.toRat, Ray.toZMod, Nat.mod_eq_of_lt h₁, -one_div]
    <;> rw [Rat.nat_cast_div_eq, Nat.cast_mul, ZMod.natCast_val, ZMod.natCast_val, sub_div]
    <;> [rw [div_div_div_cancel_right _ Ray.RAY_SCALE_rat_ne_zero, div_div,
         mul_div_mul_right _ _ Ray.RAY_SCALE_rat_ne_zero,
         sub_right_comm, sub_self, zero_sub, abs_neg];
       rw [neg_sub, div_neg, sub_neg_eq_add, div_div_div_cancel_right _ Ray.RAY_SCALE_rat_ne_zero,
         div_div (w₁.cast * _), mul_div_mul_right _ _ Ray.RAY_SCALE_rat_ne_zero, sub_add_cancel];
       rw [neg_sub, neg_div, sub_neg_eq_add, div_div_div_cancel_right _ Ray.RAY_SCALE_rat_ne_zero,
         div_div (w₁.cast * _), mul_div_mul_right _ _ Ray.RAY_SCALE_rat_ne_zero, sub_add_cancel];
       rw [div_div_div_cancel_right _ Ray.RAY_SCALE_rat_ne_zero, div_div,
         mul_div_mul_right _ _ Ray.RAY_SCALE_rat_ne_zero,
         sub_right_comm, sub_self, zero_sub, abs_neg]]
    <;> rw [abs_div,
      Nat.abs_cast, div_lt_div_right Ray.RAY_SCALE_rat_pos, abs_div, ← ZMod.natCast_val, Nat.abs_cast,
      Nat.abs_cast, div_lt_one (by rw [← Nat.cast_zero, Nat.cast_lt]; apply Nat.pos_of_ne_zero h₂), Nat.cast_lt]
    <;> apply Nat.mod_lt _ (Nat.pos_of_ne_zero h₂)

end SignedRay
