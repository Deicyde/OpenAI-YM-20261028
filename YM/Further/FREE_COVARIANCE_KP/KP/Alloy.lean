import YM.Further.FREE_COVARIANCE_KP.KP.Core
import YM.Further.FREE_COVARIANCE_KP.KP.Gem

/-! # kpd inclusive of all joint multiplier derivatives -/

set_option autoImplicit false
noncomputable section
namespace YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex Matrix Work.F06 Exterior Precision Bloch Lattice Laurent
open scoped Topology ContDiff Matrix.Norms.Elementwise BigOperators InnerProductSpace ComplexConjugate
variable {α Ω η : ℝ} {ι : Type*} {k l : ℤ}

/-- Exactly eq:KPK. Definition at zero permitted as written; outside
wedges are already zero. Use with present & retained installed, below. -/
def garnet (f : Firm α Ω η) (p : E4) := wedge 1 (tooth p) * (fuel f p)⁻¹ * (wedge 1 (tooth p))ᴴ
/-- continuum symbol P_M -/
def pearl (p : E4) : Matrix X2 X2 ℂ := wedge 1 (turned p) * ((spine p)⁻¹ • (1:Matrix X1 X1 ℂ)) * (wedge 1 (turned p))ᴴ
lemma turn_price (i : Axis) : Weight (ι:=ι) whole 1 (fun _ p => turned p i) := by
  apply Weight.template; exact (london (basis i)).contDiff.contDiffOn
  intro a h p; simp [turned]
lemma rake_subset : search.look ⊆ whole.look := fun _ hp => hp.2
lemma tooth_go (i : Axis) : Weight (ι:=ι) search 1 (fun _ p => tooth p i) ∧ Weight (ι:=ι) search 2 (fun _ p => tooth p i-turned p i) := by
  simp_rw [q_exact,turned]
  let L := london (basis i)
  let K := fun p => song (basis i) p-1
  have hb : 0 < 2*earth := by positivity [earth_pos]
  have hK : ContDiff ℝ ∞ K := (song_smooth _).sub contDiff_const
  have hd : HasFDerivAt K L 0 := by
    convert! ((song_gradient (basis i) 0).sub_const 1) using 1; simp [song]; rfl
  have he : K 0=0 := by simp [K,song]
  refine ⟨(Plain.sample K hK).one_power hb search_short fun i => he,(Plain.sample (fun p => K p-L p) (hK.sub L.contDiff)).two_powers hb search_short (fun _=> by simp [he]) fun _ => ?_⟩
  change fderiv ℝ (K-⇑L) 0 = 0; simpa using (hd.sub L.hasFDerivAt).fderiv

lemma spine_pos {p : E4} (hp : p≠0) : spine p≠0 := by unfold spine; simp [hp]
lemma reciprocal_high : Weight (ι:=ι) whole (-2) (fun _ p => (spine p)⁻¹) := by
  apply Weight.template
  · have he : ContDiff ℝ ∞ spine := ofRealCLM.contDiff.comp (contDiff_norm_sq (E:=E4) ℝ); exact he.contDiffOn.inv (fun _ h => spine_pos h)
  intro a ha p
  unfold spine
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha,mul_pow]
  simp only [Complex.ofReal_mul,real_smul,Complex.ofReal_zpow]
  simp [zpow_ofNat]
  ring

section Curl
variable {U : Window} {z w : ι → E4 → Axis → ℂ}
lemma laid (r) (h : ∀ i:Axis, Weight U k (fun a p => z a p i)) : Value U k (fun a p => wedge r (z a p)) := by
  intro i j
  simp only [wedge,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  refine Weight.sum_finite Finset.univ _ (fun l _ => ?_)
  simpa only [mul_comm] using (h l).scale (left ℂ r l i j)
lemma rubbed (r) (h : ∀ i:Axis,Weight U k (fun a p => z a p i - w a p i)) : Value U k (fun a p => wedge r (z a p)-wedge r (w a p)) := by
  have hh (a : Axis → ℂ) (b : Axis→ℂ) : wedge r a-wedge r b=wedge r (fun i => a i-b i) := by simp [wedge,sub_smul,Finset.sum_sub_distrib]
  simp_rw [hh]; exact laid _ h
end Curl

def bask {x y : Type} (f : ArrayM (Firm α Ω η) x y) (k : ℤ) := Value search k f

/-- Compare the denominators, including the longitudinal side. -/
lemma fuel_go (ha : 0<α) :
    bask (fuel (α:=α) (η:=η) (Ω:=Ω)) 2 ∧ bask (fun (i : Firm α Ω η) p => fuel i p - spine p • 1) 3 := by
  let M := Firm α Ω η
  let H := fun (i : M) (p:E4) => i.row.read (mcast p)
  have h (r : ℕ) : Value search 1 (fun (_:M) p => wedge r (tooth p)) := laid _ fun i => (tooth_go i).1
  have g (r : ℕ) : Value search 1 (fun (_:M) p => wedge r (turned p)) := laid _ fun i => (turn_price i).use rake_subset
  have s (r : ℕ) : Value search (1+1) (fun (_:M) p => wedge r (tooth p)-wedge r (turned p)) := rubbed _ fun i => (tooth_go i).2
  have t (r : ℕ) : Value search (1+1) (fun (_:M) p => (wedge r (tooth p))ᴴ-(wedge r (turned p))ᴴ) := by simpa only [← Matrix.conjTranspose_sub] using (s r).starM
  let O := (1:Matrix X2 X2 ℂ)
  have he : 0< 2*earth := by positivity [earth_pos]
  have ho : Value search 0 (fun (_ : M) (_:E4)=>O) := fun i j => Weight.spare _ _
  have hu : Value search 0 H := fun i j => (plan_prices i j ha _).zero_power he search_short
  have ha' : Value search 1 (fun i p => H i p-O) := by
    intro i j; apply ((plan_prices i j ha _).sub (Plain.sample (fun _=>O i j) contDiff_const)).one_power he search_short; intro w
    rw [show mcast 0=0 by ext; simp [mcast],w.initial]; exact sub_self _
  let B := (h 1).starM.product hu
  have hm := (h 1).starM.wedge_cost (t 1) ho ha'; let Q := B.wedge_cost hm (g 1) (s 1)
  constructor
  · exact (B.product (h 1)).joint ((h 0).product (h 0).starM)
  have hd := (h 0).wedge_cost (s 0) (g 0).starM (t 0)
  apply (Q.joint hd).switched
  intro i p hp; dsimp only; rw [← london_exact,fuel,outside,outside]; unfold H O; abel

lemma tank_sealed (ha : 0<α) (hb : 0<η) (f : Firm α Ω η) (p:E4) (h : p∈search) : IsUnit (tank f p).det := by
  obtain ⟨A,hA,H⟩ := tank_full ha hb Ω; exact Value.det_unit hA (H f p h)
/-- Resolvent identity. -/
lemma unwind (ha : 0<α) (he : 0<η) :
    bask (fun (i : Firm α Ω η) p => (fuel i p)⁻¹) (-2) ∧ bask (fun (i : Firm α Ω η) p => (fuel i p)⁻¹-(spine p)⁻¹ • 1) (-2+1) := by
  let M := Firm α Ω η
  obtain ⟨hf,hh⟩ := fuel_go (Ω:=Ω) (η:=η) ha
  obtain ⟨A,hA,H⟩ := tank_full ha he Ω
  let T : ArrayM M X1 X1 := tank
  have hr := (reciprocal_high (ι:=M)).use rake_subset
  have ht : Value search 0 T := Value.priced hr hf
  have hu := ht.paid_inv hA H
  let L := (1:Matrix X1 X1 ℂ)
  have hx : Value search 1 (fun i p => L-T i p) := by
    have hh := Value.priced hr hh
    intro i j
    apply (hh i j).opposite.stay; intro a p hp
    have hs := spine_pos (search.out hp); unfold T tank; simp [L]; field_simp
    ring
  have ho (a : M) (p:E4) (hp : p∈search) : (spine p) • (T a p)=fuel a p := smul_inv_smul₀ (spine_pos (search.out hp)) _
  have hd (a : M) (p:E4) (hp : p∈search) : (spine p)⁻¹ • (T a p)⁻¹=(fuel a p)⁻¹ := by
    letI : Invertible (spine p) := invertibleOfNonzero (spine_pos (search.out hp))
    rw [← ho a p hp, Matrix.inv_smul _ _ (tank_sealed ha he a p hp),invOf_eq_inv]
  constructor
  · exact (Value.priced hr hu).switched fun a _ hp => hd a _ hp
  apply (Value.priced hr (hu.product hx)).switched; intro a p hp; dsimp only; rw [← hd a p hp]
  rw [Matrix.mul_sub,show L=1 from rfl,Matrix.mul_one, Matrix.nonsing_inv_mul _ (tank_sealed ha he a p hp),smul_sub]
lemma gem_quote (ha : 0<α) (he : 0<η) :
    bask (garnet (Ω:=Ω) (α:=α) (η:=η)) 0 ∧ bask (fun (i : Firm α Ω η) p => garnet i p - pearl p) 1 := by
  let M := Firm α Ω η
  obtain ⟨hi,hh⟩ := unwind (Ω:=Ω) ha he
  let O := (1:Matrix X1 X1 ℂ)
  have hs := Value.priced ((reciprocal_high (ι:=M)).use rake_subset) (show Value search 0 (fun (_:M) (_:E4)=> O) from fun i j => Weight.spare _ _)
  have h : Value search 1 (fun (_:M) p => wedge 1 (tooth p)) := laid _ fun i => (tooth_go i).1
  have g : Value search 1 (fun (_:M) p => wedge 1 (turned p)) := laid _ fun i => (turn_price i).use rake_subset
  have hd : Value search (1+1) (fun (_:M) p => wedge 1 (tooth p)-wedge 1 (turned p)) := rubbed _ fun i => (tooth_go i).2
  have he' : Value search (1+1) (fun (_:M) p => (wedge 1 (tooth p))ᴴ-(wedge 1 (turned p))ᴴ) := by simpa only [← Matrix.conjTranspose_sub] using hd.starM
  exact ⟨(h.product hi).product h.starM,(h.product hi).wedge_cost (h.wedge_cost hd hs hh) g.starM he'⟩
end YM.Further.FreeCovariance.KP
