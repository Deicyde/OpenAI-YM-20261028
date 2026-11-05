import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Musical
import YM.Push.LOCAL_SPLITTING.Reanchor

/-! # Size prices on full coverage. Never on the accidental nonzero queries. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Lattice Wilson Pressure RG Tree Next Next.Fluctuations Exterior Bloch
    AnalyticBridge.LocalGaussian.Moments
open scoped Matrix.Norms.Frobenius BigOperators Classical
namespace Lute
variable {G : Gauge} {f : Side} {X : Support f} {L : Side} {P B : BudgetPoint} {x u t : ℝ} {n r : ℕ} {C : Libretto G n} {D : Record}

def bulk (d r : ℕ) (x : ℝ) := ((r+48:ℝ)*(1+(radiusB x:ℝ)))*(1+(d:ℝ))
lemma bulk_one (d r : ℕ) (x : ℝ) : 1 ≤ bulk d r x := by
  unfold bulk; have hr := Nat.cast_nonneg (α:=ℝ) r; have hd := Nat.cast_nonneg (α:=ℝ) d
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) (by simp)) (by simp)
lemma covers (h : B.B≤2*radiusB x) : let p := bulk (coverNumber B.B X) r x
    (1+(reach x:ℝ) ≤ p) ∧ (2+(breadth B X:ℝ) ≤ p) ∧ (1+(scope B X r x:ℝ) ≤ p) := by
  intro p
  have h : (B.B:ℝ) ≤ 2*(radiusB x:ℝ) := by exact_mod_cast h
  let b : ℝ := radiusB x; let d : ℝ := coverNumber B.B X
  have hb : 0≤b := Nat.cast_nonneg _; have hd : 0≤d := Nat.cast_nonneg _; have hr := Nat.cast_nonneg (α:=ℝ) r
  have he : (breadth B X:ℝ) ≤ d*(8*b+2)+4*b+8 := by unfold breadth; push_cast; gcongr _*(?_+2)+?_+8 <;> unfold b <;> linarith
  unfold reach scope; push_cast; change 1+45*(1+b)≤ (r+48:ℝ)*(1+b)*(1+d) ∧ 2+_ ≤ (r+48:ℝ)*(1+b)*(1+d) ∧ 1+((r:ℝ)*b+_+1) ≤ (r+48:ℝ)*(1+b)*(1+d)
  constructor <;> try constructor
  all_goals nlinarith [mul_nonneg (a:=b*d) (b:=(r:ℝ)) (by positivity) (by positivity)]

def season (G : Gauge) (L : Side) := (1+(2:ℝ)^4*Fintype.card (Co L (Axis×G.ColorIndex)))
lemma season_nn (G : Gauge) (L : Side) : 0 ≤ season G L := by unfold season; positivity
lemma overcrowded (h : B.B ≤ 2*radiusB x) : 1+(heads G B L X r x:ℝ) ≤ season G L * bulk (coverNumber B.B X) r x ^4 := by
  let S := bulk (coverNumber B.B X) r x; have hs : 1≤S := bulk_one ..
  have h := (covers (r:=r) (X:=X) h).2.2; unfold heads headCount season; push_cast
  calc
    _ ≤ S^4 + (2*S)^4*(Fintype.card (Co L (Axis×G.ColorIndex)):ℝ) := by
      gcongr; · exact one_le_pow₀ hs
      change _ ≤ S at h; linarith
    _ = _ := by unfold S; ring

def guests (G : Gauge) (Q : ℝ) (n : ℕ) (L : Side) := (season G L)^(1+2*(n+n))* AnalyticBridge.LocalGaussian.Moments.inflate (2*(n+n)) (Q⁻¹/8)*2
def visitors (n : ℕ) := 4*(1+2*(n+n))
lemma guest_nn (G : Gauge) (L : Side) (n : ℕ) (D : Record) : 0 ≤ guests G D.K n L := by unfold guests; have h := D.peak; positivity [inflate_ge (2*(n+n)) (show 0 ≤ D.K⁻¹/8 by positivity),season_nn G L]
lemma fares (h : B.B≤2*radiusB x) : AnalyticBridge.LocalGaussian.Moments.meter (heads G B L X r x) 0 D.K (2*(n+n)) ≤
    guests G D.K n L * bulk (coverNumber B.B X) r x ^ visitors n := by
  have hD := D.peak
  have he := overcrowded (G:=G) (L:=L) (X:=X) (r:=r) h
  unfold AnalyticBridge.LocalGaussian.Moments.meter; rw [pow_one]
  calc
    _ ≤ (season G L * bulk (coverNumber B.B X) r x ^ 4) * ((season G L * bulk (coverNumber B.B X) r x ^4)^(2*(n+n))* inflate (2*(n+n)) (D.K⁻¹/8))*2 := by
      have hp := inflate_ge (2*(n+n)) (show 0≤D.K⁻¹/8 by positivity); have hs := season_nn G L
      gcongr
    _ = _ := by unfold guests visitors; simp only [mul_pow,pow_mul,pow_add,pow_one]; ring

def blaze (D : Record) (n : ℕ) (C t : ℝ) := (clinicFee n D.Q+C)*(2*t)^2
lemma blaze_nn : 0 ≤ blaze D n C.M C.C := by have h : 0 ≤ clinicFee n D.Q := (by have := D.majorant; positivity : (0:ℝ)≤2*D.Q).trans (clinicFee_le n (zero_le_one.trans D.majorant)); have := D.majorant; unfold blaze; positivity [C.matins]

def haze (G : Gauge) (L : Side) (n : ℕ) (D : Record) := (n:ℝ)*2*(season G L)^2*(D.Z+1)*D.Z
def boost (C : Libretto G n) (D : Record) (L : Side) := blaze D n C.M C.C + (blaze D n C.M C.C+1)*(L.val:ℝ)^3 + haze G L n D
def fuse (n p : ℕ) := 8+2*p+p*n*2
def ζ (B : BudgetPoint) (u : ℝ) := B.threshold + u/B.threshold
lemma haze_nn (G : Gauge) (L : Side) (n : ℕ) (D : Record) : 0 ≤ haze G L n D := by unfold haze; have := D.chimes; positivity
lemma boost_nn (C : Libretto G n) (D : Record) (L : Side) : 0 ≤ boost C D L := by unfold boost; positivity [blaze_nn (C:=C) (D:=D),haze_nn G L n D]

section components
variable (h : B.B ≤ 2*radiusB x) (ht : P.threshold ≤ 2*B.threshold) (hu : 0≤u)
include h ht hu

lemma core_wages : let S := bulk (coverNumber B.B X) r x; let b := blaze D n C.M C.C
    segment n X P B D.Q C.M (loom P (reach x) C.C) + tranche L n D.Q (loom P (reach x) C.C) u B.threshold ≤
      (b+(b+1)*(L.val:ℝ)^3) * ζ B u * S^fuse n P.power := by
  intro S b; have hb := (blaze_nn (C:=C) (D:=D)); have hT:= B.threshold_pos; have hP := P.threshold_pos; have hC := C.C_one
  let t := B.threshold; let y := (clinicFee n D.Q+C.M) * (loom P (reach x) C.C)^2 / t
  let p := P.power; have hS : 1 ≤ S := bulk_one ..
  have hd := D.majorant; have hD : 0 ≤ clinicFee n D.Q := le_trans (by positivity) (clinicFee_le n (zero_le_one.trans D.majorant)); have hM := C.matins
  have hq := covers (r:=r) (X:=X) h
  have hy : y ≤ b*ζ B u*S^(2*p) := by
    unfold y; rw [div_le_iff₀ hT]
    have hv : loom P (reach x) C.C ≤ C.C*(2*t)*S^p := by unfold loom; gcongr; exact hq.1
    refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0 ≤ loom P (reach x) C.C by unfold loom; positivity) hv _) (by positivity)) ?_
    calc
      _ = b*t*S^(2*p)*t := by unfold b blaze; rw [mul_comm (2:ℕ),pow_mul]; ring
      _ ≤ _ := by have hh : B.threshold ≤ ζ B u := le_add_of_nonneg_right (div_nonneg hu hT.le); gcongr
  have hf : heft n X P B ≤ S^(p*n) := by unfold heft; rw [pow_mul]; gcongr; exact hq.2.1
  have hZ : 0 ≤ ζ B u := add_nonneg hT.le (by positivity)
  have h1 : segment n X P B D.Q C.M (loom P (reach x) C.C) ≤ b*ζ B u*S^fuse n P.power := calc
    _ = y*heft n X P B := by unfold segment y t; ring
    _ ≤ b*ζ B u*S^(2*p)* S^(p*n) := mul_le_mul hy hf (zero_le_one.trans (heft_one ..)) (by positivity)
    _ ≤ _ := by rw [mul_assoc _ (S^(2*p)),← pow_add]; gcongr; unfold fuse p; omega
  have h₂ : u/t ≤ ζ B u*S^fuse n p := (le_add_of_nonneg_left hT.le).trans (le_mul_of_one_le_right hZ (one_le_pow₀ hS))
  have h₃ : tranche L n D.Q (loom P (reach x) C.C) u t ≤ ((b+1)* (L.val:ℝ)^3)*ζ B u*S^fuse n p := by
    unfold tranche; rw [add_div]; let V := (L.val:ℝ)
    calc
      _ ≤ (y+u/t)*V^3 := by unfold y; gcongr; linarith only [hM]
      _ ≤ (b*ζ B u*S^fuse n p+ζ B u*S^fuse n p)*V^3 := by gcongr; exact hy.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hS (by unfold fuse; omega)) (by positivity))
      _ = _ := by unfold V; ring
  rw [add_mul,add_mul]; exact add_le_add h1 h₃

omit ht in
lemma obscured : scratch (n:=n) G D P B L X r x ≤ haze G L n D * ζ B u * bulk (coverNumber B.B X) r x ^ fuse n P.power := by
  let S := bulk (coverNumber B.B X) r x; let p := P.power; have hS : 1≤S := bulk_one ..; have hd := D.chimes; have hW := season_nn G L
  have hh : cup (n:=n) D P B X r x ≤ D.Z * S^(p*n) := by unfold cup canopy; rw [pow_mul]; gcongr; exact (covers h).2.2
  have hw := canopy_one D.chimes (scope B X r x) P.power n
  have hT := B.threshold_pos
  have ht : 0 ≤ ζ B u := add_nonneg hT.le (by positivity)
  have hv := pow_le_pow_right₀ hS (show 8+p*n*2 ≤ fuse n P.power by unfold fuse p; omega)
  unfold scratch; calc
    _ ≤ n*(2*ζ B u)*(season G L*S^4)^2 * ((D.Z+1)* S^(p*n))*(D.Z*S^(p*n)) := by
      gcongr
      · exact le_add_of_nonneg_right (div_nonneg hu hT.le)
      · exact (le_add_of_nonneg_left zero_le_one).trans (overcrowded h)
      rw [add_mul,one_mul]; exact add_le_add hh (one_le_pow₀ hS)
    _ = haze G L n D * ζ B u * S^(8+p*n*2) := by unfold haze; rw [pow_add,pow_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hv (mul_nonneg (haze_nn ..) (add_nonneg hT.le (by positivity)))

lemma booster : rust C D P B L X r x u ≤ boost C D L * ζ B u * bulk (coverNumber B.B X) r x ^ fuse n P.power := by
  unfold rust boost; rw [add_mul,add_mul]
  exact add_le_add (core_wages h ht hu) (obscured h hu)
end components
end Lute
end YM.PhysicalNext.JointLoad.Heir
