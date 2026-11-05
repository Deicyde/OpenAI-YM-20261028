import YM.Extra.SOURCE_HISTORIES.LocalDebt
import YM.Planned.PRIMARY_INTEGRAL_295.Ledger
import YM.Planned.PRIMARY_INTEGRAL_295.Stain
import YM.Push.LOCAL_SPLITTING.Leading



/-!
# E `eq:ppx`: exact leading Heading and its earned costs

This computes the actual predicted matrix from the jet read of the
canonical basis at coarse/fine thresholds. Uses B70's Frame, even in
trivial frames, not reoptimizing matrices independently of transports.
The price table takes `ratio` bounds as pre-length parameters, applies
once thresholds have been selected with BOTH bounds. Norm **and inverse**
in true coefficient scale, before painting `vowel`; don't remove the
engineering power L^(D−n). `recipe`/history assumptions later have to
pay the costs and the error term comparing actual primary output reads on
this identical step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.PPX
open Filter Function Set Lattice Labels RG Wilson Source Source.Drops Precision Bloch Next.Free Next.Foundations Extra.Histories
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
open Place Film Bid
variable {G : Gauge} {j m n d t : ℕ} {F : Labels.Frame G d} {M : Side}
variable (T : SectionData F) {A : Hol G} {K : Carrier.Lines M} (h : T.Sound A) (hK : Whole K) (Y : Side)

-- Pre-apply on input, D_* engineering correction first. Not the c/f slot change.
def flick (F : Labels.Frame G d) (L : Side) : F.Coeff →ₗ[ℂ] F.Coeff where
  toFun v i := (L.val:ℂ)^((F.grades i).1) * v i
  map_add' v w := by ext; simp [mul_add]
  map_smul' z v := by ext; simp [mul_left_comm]

def matrix (f c : ℝ) : F.Coeff→ₗ[ℂ] F.Coeff :=
    F.scaled c ∘ₗ receipt T h hK ∘ₗ flick F M ∘ₗ F.scaled f⁻¹

lemma flick_col (i : F.Index) : flick F Y (copy F i)= (Y.val:ℂ)^((F.grades i).1) • copy F i := by
  ext l; by_cases hi:l=i
  · rw [hi]; rfl
  simp [copy, hi,flick]
lemma scaled_col (t : ℝ) (i : F.Index) : F.scaled t (copy F i) = (t:ℂ)^((F.grades i).2) • copy F i := by
  ext l; by_cases hi:l=i
  · rw [hi]; simp [copy]
  simp [copy, hi]
lemma vowel_col (L : Side) (i : F.Index) : vowel F L (copy F i) = (L.val:ℂ)^(d-(F.grades i).1) • copy F i := by
  ext l; by_cases hi:l=i
  · rw [hi]; rfl
  simp [copy,hi,vowel]

include h hK
lemma matrix_col (f c : ℝ) (i : F.Index) : matrix T h hK f c (copy F i) = ((f:ℂ)⁻¹^(F.grades i).2 * (M.val:ℂ)^((F.grades i).1)) •
      (F.scaled c (receipt T h hK (copy F i))) := by
  unfold matrix; rw [LinearMap.comp_apply,LinearMap.comp_apply,LinearMap.comp_apply, scaled_col f⁻¹,map_smul,flick_col,map_smul,map_smul,
    map_smul, map_smul,Complex.ofReal_inv, smul_smul]
lemma matrix_chip (f c : ℝ) (i b : F.Index) : matrix T h hK f c (copy F i) b =
    ((c:ℂ)^(F.grades b).2 / (f:ℂ)^((F.grades i).2)) * (M.val:ℂ)^((F.grades i).1) * receipt T h hK (copy F i) b := by
  rw [matrix_col]; simp [div_eq_mul_inv]; ring
lemma matrix_unit (f c : ℝ) : matrix T h hK f c F.e0=F.e0 := by
  change matrix T h hK f c (copy F 0)=F.e0; rw [matrix_col,show copy F 0=F.e0 from rfl, F.zero_degree,pays_unit]; simp

omit hK
variable (P : Flight j t) (k : ℝ) (hk : 0 < k) (ht : 4 ≤ t)
include hk ht
lemma through (hd : d≤j) (f c : ℝ) (i b : F.Index) (hb : (F.grades b).1≤(F.grades i).1) :
    matrix T h (Carrier.stored P k hk ht) f c (copy F i) b=
      if b=i then (((c/f : ℝ):ℂ))^((F.grades i).2) else 0 := by
  rw [matrix_chip,imprint T h P k hk ht hd i b hb]
  by_cases H : b=i
  · rw [H]; simp only [if_true, Carrier.unitStep, inv_pow, Complex.ofReal_pow,Complex.ofReal_div,
       Complex.ofReal_inv,Complex.ofReal_natCast,div_pow]
    rw [mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast P.L.property.ne')),mul_one]
  rw [if_neg H, mul_zero, if_neg H]

lemma later_only (hF : Bid.pop T) (f c : ℝ) (i b : F.Index) (hb : (F.grades b).2 < (F.grades i).2) :
    matrix T h (Carrier.stored P k hk ht) f c (copy F i) b=0 := by rw [matrix_chip, print_later T h P k hk ht hF i b hb, mul_zero]

lemma matrix_spin (f c : ℝ) (v : F.Coeff) (w : Motion) :
    let D := matrix T h (Carrier.stored P k hk ht) f c
    D (Motion.patch F w v)=Motion.patch F w (D v) := by
  intro D; let s:=w.1
  have hf (v : F.Coeff) : flick F P.L (star v)=star (flick F P.L v) := by ext; simp [flick,mul_comm]
  have hv (v : F.Coeff) : D (F.act s.ortho v)=F.act s.ortho (D v) := by
    unfold D matrix; simp only [LinearMap.comp_apply]
    rw [F.scaling, show flick F P.L (F.act s.ortho _) = _ from
      (Motion.act_diag F (fun i=> (P.L.val:ℂ)^i.1) _ (F.scaled _ v)).symm,pays_turn T h _ s P k hk ht,Frame.scaling]; rfl
  have he (u:F.Coeff) : D (star u)=star (D u) := by
    unfold D matrix; simp only [LinearMap.comp_apply, hf,Push.Local.scaled_star,pays_conj]
  unfold Motion.patch; split
  · rw [he]; exact congr_arg star (hv v)
  exact hv v

/-- Before-profile parameter π, supplies both scaling bounds. -/
structure Blend (π f c : ℝ) : Prop where
  ratio : 1 ≤ π
  fine : 0 < f
  coarse : 0 < c
  fits : f≤1
  covers : c≤1
  accounted : c/f≤π
  backed : f/c≤π

variable {π : ℝ}
omit h hk ht in
private lemma capacities {f c : ℝ} (hf : Blend π f c) (h : n ≤ d) (hp : n ≤ m) : c^m/f^n ≤ π^d := by
  calc
    c^m/f^n ≤ c^n/f^n := div_le_div_of_nonneg_right (pow_le_pow_of_le_one hf.coarse.le hf.covers hp) (by positivity [hf.fine])
    _ = (c/f)^n := (div_pow ..).symm
    _ ≤ _ := (pow_le_pow_left₀ (div_nonneg hf.coarse.le hf.fine.le) hf.accounted n).trans (pow_le_pow_right₀ hf.ratio h)

include π in
/-- Price table before L or the thresholds, in the displayed qualification.
Second returned `Leading`-based theorem will supply the inverse cost. -/
theorem toll (hF : Bid.pop T) (hj : 4≤j) (hd : d≤j) (hp : 1≤π) : ∃ C:ℝ,1≤C ∧
    ∀ (P : Flight j t) (f c : ℝ), Blend π f c → Push.Local.Leading (matrix T h (Carrier.stored P k hk ht) f c) C := by
  obtain ⟨D,hD,H⟩:= preBill T h k hk hj ht hd
  have ha:=one_le_pow₀ (n:=d) hp
  refine ⟨π^d * D,one_le_mul_of_one_le_of_one_le ha hD,fun P f c hf=> ?_⟩
  have hy := hf.fine; have hc:=hf.coarse; have hL : 0<(P.L.val:ℝ) := by positivity
  refine ⟨one_le_mul_of_one_le_of_one_le ha hD,fun b i=>?_,fun i=>?_,fun b i hi hb=>?_,matrix_unit ..⟩
  · change ‖matrix T _ _ _ _ (copy F i) b‖ ≤ π^d*D
    by_cases he : (F.grades b).2 < (F.grades i).2
    · rw [later_only _ _ P k hk ht hF f c i b he]; simp [show 0≤π^d*D by positivity]
    rw [matrix_chip]; let n := (F.grades i).2; let m:=(F.grades i).1; let r := (F.grades b).2
    simp only [norm_mul,norm_div, Complex.norm_pow, Complex.norm_real,Complex.norm_natCast,Real.norm_of_nonneg hc.le,Real.norm_of_nonneg hy.le,mul_assoc]
    have hv : c^r / f^n ≤ π^d := capacities hf (second_fits F i) (le_of_not_gt he)
    refine mul_le_mul hv ?_ (by positivity) (by positivity)
    apply (mul_le_mul_of_nonneg_left (H P i b) (by positivity)).trans; unfold Carrier.unitStep
    change (P.L.val:ℝ)^m*(D*((↑P.L.val:ℝ)⁻¹)^m)≤D
    exact le_of_eq (by rw [inv_pow]; field_simp)
  · change 1≤π^d*D*‖matrix T h _ _ _ (copy F i) i‖; rw [through _ _ P k hk ht hd f c i i le_rfl,if_pos rfl,Complex.norm_pow,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    let n := (F.grades i).2
    have hv : (f/c)^n≤π^d:= (pow_le_pow_left₀ (by positivity) hf.backed n).trans (pow_le_pow_right₀ hp (second_fits F i))
    calc (1:ℝ) = (f/c)^n*(c/f)^n := by rw [← mul_pow]; field_simp; simp
         _ ≤ _ := mul_le_mul_of_nonneg_right (hv.trans (le_mul_of_one_le_right (by positivity) hD)) (by positivity)
  by_contra! H
  have hz := through T h P k hk ht hd f c i b H
  exact hb (hz.trans (if_neg (Ne.symm hi)))

namespace Seal
variable {k} (hF : Bid.pop T) {f c : ℝ}

def cap (hj : 4≤j) (hd : d≤j) (hp : 1≤π) := (toll T h _ hk ht hF hj hd hp).choose

lemma cap_lead (P : Flight j t) (hd : d≤j) (hp : Blend π f c) :
    Push.Local.Leading (matrix T h (Carrier.stored P k hk ht) f c) (cap T h hk ht hF P.legal hd hp.ratio) :=
    (toll T h _ hk ht hF P.legal hd hp.ratio).choose_spec.2 P _ _ hp

/-- The true leading-map notion exported to the History printing service:
ONE matrix, a proved equivalence on polynomial labels including the exact
unit. Heading prices still charged. -/
def donne (P : Flight j t) (hd : d≤j) (hb : Blend π f c) : Heading F :=
    let V := cap_lead T h hk ht hF P hd hb
    { map := LinearEquiv.ofBijective _ V.bijective
      unit := V.unit
      core_comm x := (V.core x).symm
      covariant v w := matrix_spin T h P k hk ht f c v w }

lemma donne_map (P : Flight j t) (hd : d≤j) (hb : Blend π f c) (v : F.Coeff) :
    (donne T h hk ht hF P hd hb).map v = matrix T h (Carrier.stored P k hk ht) f c v := rfl

def limit (hj : 4≤j) (hd : d ≤ j) (hp : 1≤π) := Push.Local.triangularPrice F (cap T h hk ht hF hj hd hp)



-- Exact engineering-scaled multiplications. `Film.seen` only in this
-- germ/probe interpretation. `map` not itself doing stationary integrals.
lemma revealed (P : Flight j t) (hd : d ≤ j) (hb : Blend π f c)
    (a : F.Index) (p : Push.Local.Probe G d) :
    let B := donne T h hk ht hF P hd hb
    Push.Local.runProbe F p (B.leads P.L (copy F a)) =
      ((P.L.val : ℂ)^d * ((f:ℂ) ^ ((F.grades a).2))⁻¹) •
        iteratedDeriv p.2.val (fun x => column T a (Film.trace T.stencil (Carrier.linesOf P k)
          (WardBin.engineered x (trunk d (c • p.1))))) 0 := by
  classical
  intro B
  let n := (F.grades a).1; let l := (F.grades a).2; let V := copy F a
  let g := receipt T h (Carrier.stored P k hk ht)
  have hz : B.leads P.L V=((P.L.val : ℂ)^d * ((f:ℂ)^l)⁻¹) • F.scaled c (g V) := by
    change B.map (vowel F P.L V)=_
    rw [vowel_col _ _,map_smul]; unfold B; rw [donne_map]
    rw [matrix_col]
    rw [smul_smul,inv_pow]; congr 1
    rw [mul_left_comm,← pow_add,Nat.sub_add_cancel (F.bound _)]; ring
  change Push.Local.runProbe F p (B.leads P.L V)=_
  rw [hz,map_smul, Push.Local.runProbe_eq]
  apply congr_arg (fun z : ℂ=> ((P.L.val : ℂ)^d * ((f:ℂ)^l)⁻¹) • z)
  let Q:=bought T h (Carrier.stored P k hk ht) V
  have he (x : ℝ) : read (scaleJet p.1 x) (F.coords.symm (F.scaled c (g V))).val=read (scaleJet (c • p.1) x) Q.val := by
    rw [read_frame_scaled,show g V=F.coords Q from rfl,LinearEquiv.symm_apply_apply]; apply congr_arg (fun x : Jet G=>read x Q.val)
    exact funext fun j => smul_comm c (x^(j+2)) (p.1 j)
  simp_rw [he]; exact bought_unlock T h _ V _ (Nat.le_of_lt_succ p.2.isLt)
end Seal
end YM.Planned.PrimaryIntegral295.PPX
