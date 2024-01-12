import CorelibVerification.Aux.ZMod
import Aegis.Aux.Bool
import Aegis.Aux.ZMod.DivMod

open Sierra

def Wad : Type := UInt128

namespace Wad

def WAD_SCALE : ℕ := 1000000000000000000

theorem WAD_SCALE_pos : 0 < WAD_SCALE := by norm_num[WAD_SCALE]

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

end Wad

def Ray : Type := UInt128

namespace Ray

def RAY_SCALE : ℕ := 1000000000000000000000000000

theorem RAY_SCALE_pos : 0 < RAY_SCALE := by norm_num[RAY_SCALE]

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

protected def zero : Ray := (0 : UInt128)

instance : Zero Ray := ⟨Ray.zero⟩

@[simp]
protected theorem zero_toZMod :
    (0 : Ray).toZMod = 0 :=
  rfl

end Ray

def Wad.toRay (w : Wad) : Ray := w.toZMod * (Ray.DIFF : UInt128)

def Wad.MAX_CONVERTIBLE_WAD : ℕ := 340282366920938463463374607431

/- Signed Wad -/

def SignedWad := UInt128 × (Unit ⊕ Unit)

namespace SignedWad

variable (w : SignedWad)

def sign := SierraBool.toBool w.2

instance : Zero SignedWad := ⟨(0, false.toSierraBool)⟩

theorem zero_def : (0 : SignedWad) = (0, false.toSierraBool) := rfl

@[simp]
theorem zero_val : (0 : SignedWad).1 = 0 := rfl

@[simp]
theorem zero_sign : (0 : SignedWad).2 = .inl () := rfl



end SignedWad
