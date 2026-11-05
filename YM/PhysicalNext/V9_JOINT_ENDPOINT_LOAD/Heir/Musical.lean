import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Anthem
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Sonata
import YM.Push.RELAY_DIFFERENCE.CalendarPrices
import YM.Push.RELAY_MARK.Assembly

/-!
# Release both directional and size costs on the one real corner

Arithmetic extraction of pre-L coefficient (without any marginal
population factor) BEFORE scoring the post-L parts by the already
commissioned true Gaussian multipliers. All terms preserved on every
call, including Γ fields not used by E. Large supports here do *not*
receive L^-5 yet. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Multi Multi.Puff Push.SectorMeasure Exterior Planned.AtomRegular MeasureTheory AnalyticBridge.LocalGaussian.Moments
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {X : Support f} {Y : Support c}
    {V : Config G c} {P B : BudgetPoint} {ι : Type} [Fintype ι] [DecidableEq ι] {x u t τ : ℝ} {n r : ℕ} {o : Site f}
    {q : Chi} {d : ℝ} {k : S.Choices} {f' : Config G f → ℝ} {Pt : Teller G} {C : Libretto G n} {D : Record}
namespace Lute
section fees
variable (C : Libretto G n) (D : Record) (P B : BudgetPoint) (L : Side) (X : Support f) (r : ℕ) (x u : ℝ)
def decay := if (coverNumber B.B X)^3 < L.val then ((L.val:ℝ)⁻¹)^5 else 1
def leading := 1+(n:ℝ)*2+C.M*(C.C*2)
lemma leading_one : 1 ≤ leading C := by unfold leading; have := C.matins; have := C.C_one; nlinarith
variable (G)
def heads := headCount G L (scope B X r x)
def cup := canopy D.Z (scope B X r x) P.power n
def scratch := n*(2*B.threshold)*(heads G B L X r x)^2 *(cup (n:=n) D P B X r x+1)*cup (n:=n) D P B X r x
variable {G}
def rust := segment n X P B D.Q C.M (loom P (reach x) C.C) + tranche L n D.Q (loom P (reach x) C.C) u B.threshold + scratch (n:=n) G D P B L X r x
def phrase := shortFee C.rights+grandFee C.rights
def beat := (leading C+leading C)^(n+n)*phrase C
lemma phrase_nn : 0 ≤ phrase C := by unfold phrase shortFee grandFee; positivity [C.rights.large,patterns_nonneg n]
lemma beat_nn : 0 ≤ beat C := by unfold beat; positivity [leading_one C,phrase_nn C]
end fees

variable {L : Side}
omit [DecidableEq ι] in
lemma tape_control (z : Prices G ι) : ‖z‖ ≤ ‖tape z‖ ∧ ‖tape z‖ ≤ powers z := by
  have he : ‖z‖ ≤ ‖tape z‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i => (PiLp.norm_apply_le (tape z i.1) _).trans (norm_le_pi_norm (tape z) i.1))
  exact ⟨he, (pi_norm_le_iff_of_nonneg (powers_pos _).le).mpr (fun i => by
    unfold powers; rw [load_square,SectorChange.price_square]; have hh := Finset.single_le_sum (s:=Finset.univ) (f:=fun i => ‖tape z i‖^2) (fun j _ => sq_nonneg _) (Finset.mem_univ i); nlinarith)⟩

lemma scratch_nn (n : ℕ) : 0 ≤ scratch (n:=n) G D P B L X r x := by unfold scratch cup; positivity [canopy_one D.chimes (scope B X r x) P.power n,B.threshold_pos]
lemma rust_nn (hu : 0≤u) : 0≤rust C D P B L X r x u := add_nonneg (add_nonneg (segment_nn n X P B D.majorant C.matins)
    (tranche_nn L n (zero_le_one.trans D.majorant) hu B.threshold_pos.le)) (scratch_nn n)

variable (a : Museum F x A X Y ι)
include a
omit [DecidableEq ι] in
lemma speed_le (hw : Walled S X Y x r) (ho : o∈X) (hu : 0≤u) (z : Prices G ι) : 1+Carillon.speed n D.Z B.threshold P.power (scope B X r x) z ≤ leading C + rust C D P B S.patch.L X r x u * (powers z)^2 := by
  let K := cup (n:=n) D P B X r x
  have h1 : 1 ≤ K := canopy_one D.chimes _ _ _; have he := grows z
  have hp : Carillon.pitch n (ι×G.ColorIndex) D.Z (scope B X r x) P.power z ≤ ((heads G B S.patch.L X r x:ℕ):ℝ)^2 * (K+1)*K*(powers z)^2 := by
    unfold Carillon.pitch; change _*(K+‖z‖^2)*_ ≤ _
    have hi : ‖z‖^2 ≤ powers z^2 := pow_le_pow_left₀ (norm_nonneg _) ((tape_control z).1.trans (tape_control z).2) _
    calc
      _ ≤ ((heads G B S.patch.L X r x:ℕ):ℝ)^2 * ((K+1)*powers z^2)*K := by
        gcongr ?_^2 * ?_*_
        · exact Nat.cast_le.mpr (a.viewed hw B ho G)
        rw [add_mul,one_mul]; exact add_le_add (le_mul_of_one_le_right (by positivity) (one_le_pow₀ he)) hi
      _ = _ := by ring
  have hx : rust C D P B S.patch.L X r x u ≥ scratch (n:=n) G D P B S.patch.L X r x := le_add_of_nonneg_left
    (add_nonneg (segment_nn n X P B D.majorant C.matins) (tranche_nn _ _ (zero_le_one.trans D.majorant) hu B.threshold_pos.le))
  have hl := C.C_one; have hM := C.matins
  have hT := mul_le_mul_of_nonneg_left hp (mul_nonneg (Nat.cast_nonneg n (α:=ℝ)) B.threshold_pos.le)
  have H := mul_le_mul_of_nonneg_right hx (sq_nonneg (powers z)); unfold scratch at H; change _*_*_*(_+1)*K*_ ≤ _ at H
  unfold Carillon.speed leading; nlinarith only [hT,H,show 0≤C.M*C.C by positivity]

omit [DecidableEq ι] in
omit a in
lemma pay_le (hu : 0≤u) (z : Prices G ι) : Plays.price C D P B L X x u z ≤ phrase C * decay B L X * (leading C+ rust C D P B L X r x u * powers z^2)^n := by
  let a := leading C; let b := rust C D P B L X r x u; let s := powers z^2
  let v := loom P (reach x) C.C
  have hs : 1 ≤ s := one_le_pow₀ (grows z); have hs' : ‖tape z‖ ≤ s := (tape_control z).2.trans (le_self_pow₀ (grows z) two_ne_zero)
  have hb : 0 ≤ b := rust_nn hu
  have hQ := D.majorant; have hc := zero_le_one.trans C.C_one; have hm := zero_le_one.trans C.matins
  have hL := leading_one C
  have hF := patterns_nonneg n; have hR := C.rights.large
  have H := phrase_nn C
  have h₁ : segment n X P B D.Q C.M v ≤ b*s := le_trans (b:=b) ((le_add_of_nonneg_right (tranche_nn _ _ (zero_le_one.trans hQ) hu B.threshold_pos.le)).trans (le_add_of_nonneg_right (scratch_nn n))) (le_mul_of_one_le_right hb hs)
  have h₂ : tranche L n D.Q v (u*‖tape z‖) B.threshold ≤ b*s := by
    apply le_trans (b:=tranche L n D.Q v u B.threshold*s) ?_ (mul_le_mul_of_nonneg_right
      ((le_add_of_nonneg_left (segment_nn n X P B D.majorant C.matins)).trans (le_add_of_nonneg_right (scratch_nn n))) (sq_nonneg _))
    have H := le_mul_of_one_le_right (mul_nonneg ((by positivity : (0:ℝ) ≤ 2*D.Q).trans (clinicFee_le n (zero_le_one.trans D.majorant))) (sq_nonneg v)) hs
    unfold tranche; calc
      _ ≤ (clinicFee n D.Q*v^2*s + u*s)/B.threshold*(L.val:ℝ)^3 := by have h := B.threshold_pos; gcongr
      _ = _ := by ring
  have ht := tranche_nn L n (v:=v) (zero_le_one.trans hQ) (mul_nonneg hu (norm_nonneg (tape z))) B.threshold_pos.le
  have hA := ample_one n X P B D.majorant C.matins C.C_one (x:=x)
  unfold v at ht h₁ h₂
  unfold Plays.price decay; change _ ≤ _*_* (a+b*s)^n; split
  · rw [mul_right_comm]; gcongr ?_*_*?_^_
    · unfold phrase grandFee; apply le_add_of_nonneg_right; positivity
    unfold a leading; apply add_le_add _ h₂; nlinarith only [C.C_one,C.matins,Nat.cast_nonneg (α:=ℝ) n]
  rw [mul_one]; gcongr
  · unfold phrase shortFee; apply le_add_of_nonneg_left; positivity
  unfold a leading ample; exact add_le_add (le_add_of_nonneg_left (by positivity)) h₁

end Lute
end YM.PhysicalNext.JointLoad.Heir
