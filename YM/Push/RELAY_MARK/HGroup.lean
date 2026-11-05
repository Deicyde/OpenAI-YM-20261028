import YM.Push.RELAY_MARK.Linear
import YM.Push.RELAY_MARK.Parity

/-!
# H and star equivariance for the lifting at one d

Reynolds and real averaging before evaluating any coordinates or building the cutoff
Family. Use complex linear maps and the specific semilinear bar. E eqspec.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Labels Analysis Next.Foundations
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {H : Hol G} {d : ℕ} {p : Label G d} {m : ℕ × ℕ} {v : Bill G d}

-- Real/signed actions.
def theta (s : Signed) : Label G d →ₗ[ℂ] Label G d := tensor s.ortho
lemma theta_one (p : Label G d) : theta 1 p=p := by rw [theta, show (1:Signed).ortho=1 from map_one Signed.inclusionO,tensor_one]
lemma theta_mul (s t : Signed) (p : Label G d) : theta (s*t) p=theta s (theta t p) := by
  unfold theta; rw [show (s*t).ortho=s.ortho*t.ortho from map_mul Signed.inclusionO ..,tensor_mul]

lemma theta_unit (s : Signed) : theta s (unit G d)=unit G d := Subtype.ext (map_one (rotated _))
lemma theta_bar (s : Signed) (p : Label G d) : theta s (realBar p)=realBar (theta s p) := (real_turn ..).symm

def phi (s : Signed) : Module.End ℂ (Bill G d) where
  toFun x := (theta s x.1, x.2 ∘ pull s 0)
  map_add' _ _ := Prod.ext (map_add _ _ _) rfl
  map_smul' _ _ := Prod.ext (map_smul _ _ _) rfl
lemma phi_mul (s t : Signed) (v : Bill G d) : phi (s*t) v = phi s (phi t v) := by
  refine Prod.ext (theta_mul ..) (funext fun U=>?_)
  change v.2 _=v.2 _; rw [pull_pull]; simp [affine]
lemma phi_unit (s : Signed) : phi s (unit G d, (1:Pre G)) = (unit G d,1) := Prod.ext (theta_unit _) rfl

def varphi : (Bill G d) →ₛₗ[starRingEnd ℂ] (Bill G d) where
  toFun x := (realBar x.1, star x.2)
  map_add' x y := Prod.ext (map_add realBar x.1 y.1) (star_add ..)
  map_smul' t _ := Prod.ext (realBar.map_smulₛₗ t _) (star_smul ..)
lemma varphi_twice (v : Bill G d) : varphi (varphi v)=v := Prod.ext (twice _) (star_star _)
lemma varphi_turn (s : Signed) (v : Bill G d) : varphi (phi s v)=phi s (varphi v) := Prod.ext (theta_bar ..).symm (funext fun _ => rfl)
lemma varphi_unit (G : Gauge) (d : ℕ) : varphi (unit G d,(1:Pre G))=(unit G d,1) := Prod.ext (unit_real _) (star_one _)

lemma Payment.turn (s : Signed) (h : Payment H d m p v) : Payment H d m (theta s p) (phi s v) := by
  obtain ⟨⟨hr,hg,hy,hl,hx⟩,he⟩ := h
  refine ⟨⟨turned_grade s hr,fun t U=>?_,?_,?_,signed_power hx _⟩,fun h=>?_⟩
  · change v.2 (pull _ _ _)=v.2 (pull _ _ U); rw [Work.G06.pull_gauge_zero]; exact hg ..
  · change ((theta s v.1-theta s p:Label G d)).val∈_; rw [← map_sub]; exact signed_high (p:=v.1-p) hy _
  · exact (Forms.seats ..).2 (Work.G06.projects_pull (Work.G01.answer .. |>.1) ((Forms.seats ..).1 hl) s)
  apply Micro.signed (he ?_) s
  rw [← theta_one p,← inv_mul_cancel s, theta_mul]
  exact turn_ideal s⁻¹ h

lemma Payment.real_ (h : Payment H d m p v) : Payment H d m (realBar p) (varphi v) := by
  obtain ⟨⟨hr,hg,hy,hl,hx⟩,he⟩ := h
  refine ⟨⟨conjugate_grade hr,fun t U=> congr_arg star (hg t U),?_,star_project hl,star_power hx⟩,fun h=>?_⟩
  · change ((realBar v.1-realBar p:Label G d)).val∈_; rw [← map_sub]; exact conj_high (p:=v.1-p) hy
  exact (he (twice p ▸ conjugate_ideal h)).conj

-- right/left interpolation with real averaging coefficients summing to one. Does not lose even zero sector.
lemma pay_replicate {ι : Type*} {v : ι→Bill G d} {p} {I : Finset ι} {c : ℂ} (he : c * I.card = 1)
    (h : ∀ i∈I,Payment H d m p (v i)) : Payment H d m p (c • ∑ i∈I,v i) := by
  have hl := Offered.sum I _ v (fun i hi=> (h i hi).takes) |>.scale c
  rw [Finset.sum_const,← Nat.cast_smul_eq_nsmul ℂ,smul_smul, he,one_smul] at hl
  refine ⟨hl,fun hP=>?_⟩
  rw [Prod.smul_snd,Prod.snd_sum]
  exact (micros G).smul_mem _ (Submodule.sum_mem _ fun i hi=> (h i hi).exacts hP)

-- campaigns don't add (p is fixed) but can midpoint
lemma pay_midpoint {w : Bill G d} (h : Payment H d m p v) (he : Payment H d m p w) :
    Payment H d m p (((2:ℂ)⁻¹) • (v+w)) := by
  have hl := (h.takes.add he.takes).scale ((2:ℂ)⁻¹)
  rw [← two_smul ℂ,smul_smul, inv_mul_cancel₀ (by norm_num),one_smul] at hl
  exact ⟨hl,fun hP=> ((h.exacts hP).add (he.exacts hP)).scale _⟩

variable {F : Switch G d}
structure Imprint (H : Hol G) (d : ℕ) (F : Switch G d) : Prop extends Campaign H d F where
  signed (s : Signed) (p : Label G d) : F (theta s p)=phi s (F p)
  real_ (p : Label G d) : F (realBar p)=varphi (F p)

def oriented' (F : Switch G d) (s : Signed) := (phi s) ∘ₗ F ∘ₗ theta s⁻¹

def ortho (F : Switch G d) : Switch G d := Work.G06.share • ∑ s : Signed, oriented' F s
lemma ortho_campaign (h : Campaign H d F) : Campaign H d (ortho F) := by
  constructor
  · intro m hm p hp
    simp only [ortho,LinearMap.smul_apply, LinearMap.sum_apply]
    refine pay_replicate ?_ (fun i _=>?_)
    · unfold Work.G06.share; simp
    have hi := Payment.turn i (h.each m hm _ (turned_grade i⁻¹ hp))
    change Payment H d m (theta i (theta i⁻¹ p)) _ at hi
    rw [← theta_mul,mul_inv_cancel,theta_one] at hi
    exact hi
  simp only [ortho,LinearMap.smul_apply, LinearMap.sum_apply,oriented',LinearMap.comp_apply,
    theta_unit,h.start,phi_unit,Work.G06.share_sum]

lemma ortho_align (s : Signed) (p) : ortho F (theta s p)=phi s (ortho F p) := by
  have he (t : Signed) : phi s ((oriented' F t) p)=oriented' F (s*t) (theta s p) := by
    simp only [oriented', LinearMap.comp_apply]; rw [← phi_mul, ← theta_mul, mul_inv_rev, mul_assoc,inv_mul_cancel,mul_one]
  rw [ortho]; simp_rw [LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,he]
  exact congr_arg (_ • ·) (Equiv.sum_comp (Equiv.mulLeft s) (fun t => (oriented' F t) (theta s p))).symm

def deepen (F : Switch G d) : Switch G d := varphi.comp (F.comp realBar)

def midpoint (F : Switch G d) : Switch G d := ((2:ℂ)⁻¹) • (F+deepen F)

theorem impression (h : Campaign H d F) : Imprint H d (midpoint (ortho F)) := by
  let V := ortho F
  have hm : Campaign H d V := ortho_campaign h
  let A := midpoint V
  have he (p) : A p=((2:ℂ)⁻¹) • (V p+varphi (V (realBar p))) := by simp only [A,midpoint,LinearMap.smul_apply,
    LinearMap.add_apply, deepen,LinearMap.comp_apply]
  change Imprint H d A
  refine { toCampaign := ?_, signed := ?_, real_ := ?_ }
  · constructor
    · intro m hm' p hp
      rw [he]; apply pay_midpoint (hm.each _ hm' p hp)
      have hr := Payment.real_ (hm.each _ hm' _ (conjugate_grade hp))
      rwa [twice] at hr
    rw [he,hm.start,unit_real,hm.start,varphi_unit, ← two_smul ℂ,smul_smul,inv_mul_cancel₀ (by norm_num),one_smul]
  · intro s p
    have hv (p) : V (theta s p)=_ := ortho_align s p
    rw [he, he, hv, ← theta_bar, hv,varphi_turn,map_smul,map_add]
  intro p
  rw [he,he,twice,varphi.map_smulₛₗ,map_add,varphi_twice,add_comm (V (realBar p))]
  rw [map_inv₀, show (starRingEnd ℂ) 2=2 by rw [show (2:ℂ)=1+1 by norm_num,map_add,map_one]]
end YM.Push.Mark
