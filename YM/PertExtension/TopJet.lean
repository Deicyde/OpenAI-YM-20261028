import YM.Further.CORRECTED_LIFT_COEFFICIENTS.LensBill
import YM.PertExtension.BareWords
import YM.PertExtension.HeatProjection

/-! Joint-jet matching of the ordinary (un-Wick-corrected) pure bare symbols,
with slot number taken before substituting curved stencils. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.PertExtension.Heat.Top
open Function Filter Set RG Wilson Lattice Supply Labels Source Drops InnerProductSpace MeasureTheory Bid MvPolynomial
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open Push.CutoffProjectors ProjectorNext.Calibration.Coupon Further.CorrectedLift Further.CorrectedLift.Scratch
open Next.Foundations
variable {G : Gauge} {H : Hol G} {d m ℓ : ℕ}{F : Labels.Frame G d}
local notation "V"=> RG.Slot × G.ColorIndex

-- No equation quotient on this space. Only address-zero fields here. Moment
-- probes on continuum radial *linear* jets substituted before Taylor.
def symbolEval {d : ℕ} (P : MvPolynomial V ℂ)(a : Jet G)(r : ℝ) :=
   MvPolynomial.aeval (R:=ℂ) (fun i=>((glow (trunk d (scaleJet a r)) i.1 i.2 : ℝ) : ℂ)) P
-- d explicit

def test (P : MvPolynomial V ℂ)(a : Lens G d) := iteratedDeriv a.2.val (fun r : ℝ=>symbolEval (d:=d) P a.1 r) 0

def rawPart (B : Fin m→RG.Slot) (P : Pose G m) (ℓ : ℕ) :=
   MvPolynomial.rename (τ:=V) (fun k => (B k.1,k.2)) (MvPolynomial.weightedHomogeneousComponent (fun _=> (1:ℕ)) ℓ P)

abbrev degree {α : Type*}(n : α →₀ ℕ) := (Finsupp.weight (fun _=> (1:ℕ))) n
@[simp] lemma degree_eq {α : Type*}(n : α →₀ ℕ) : degree n=n.sum fun a j=>j := by simp [degree,Finsupp.weight_apply]

lemma scaleSlot (r z : ℝ) (J : Jet G) : trunk d (scaleJet (z • J) r) = z • trunk d (scaleJet J r) := by
  ext1 j; simp [trunk,scaleJet]; rw [smul_smul,smul_smul,mul_comm]

@[fun_prop] lemma smooth_lumin (p : Pose G m) : ContDiff ℝ ω (lumin p) := by
  change ContDiff ℝ ω fun x : GaugePanel G m=>lumin p x
  simp_rw [lumin,aeval_eq_eval₂Hom,coe_eval₂Hom,eval₂_eq]
  refine ContDiff.sum fun i hi=> contDiff_const.mul <| contDiff_prod (f:=fun (j: Fin m× G.ColorIndex) (x:GaugePanel G m)=> (((x j.1 j.2 : ℝ) : ℂ)) ^ (i j) ) ?_
  exact fun j hj=> (show ContDiff ℝ ω (fun (x:GaugePanel G m)=> ((x j.1 j.2 : ℂ))) from by
           convert! Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜:=ℝ) j.2).contDiff.comp (contDiff_apply ℝ G.Color (j.1))))|>.pow ..

def initialTerm (H : Hol G)(B : Fin m→RG.Slot)(a : Lens G d) (i : Fin m×G.ColorIndex)(θ r : ℝ): ℂ :=
 ((trim d (bring H d B) θ (trunk d (scaleJet a.1 r)) i.1 i.2 : ℝ): ℂ)

def residual (H : Hol G)(ℓ : ℕ)(P : Pose G m)(B : Fin m→RG.Slot)(a : Lens G d)(θ r : ℝ) :=
    ∑ b∈(P.support), coeff b P * ((θ:ℂ)^(degree b-ℓ)) * ∏ i∈b.support, (initialTerm H B a i θ r)^(b i)

lemma trim_eval (P:Pose G m)(W : GaugePanel G m){t :ℝ} (hp : lows P ℓ):
  MvPolynomial.aeval (R:=ℂ) (fun i : Fin m×G.ColorIndex=>((((t • W) i.1 i.2:ℝ):ℂ))) P =
    (t:ℂ)^ℓ * ∑ b∈(P.support), coeff b P * ((t:ℂ)^(degree b-ℓ)) * ∏ i∈b.support, (((W i.1 i.2:ℝ):ℂ))^(b i) := by
    simp_rw [aeval_eq_eval₂Hom,coe_eval₂Hom,eval₂_eq,Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb=> ?_
    have hi : ℓ≤degree b := by rw [degree_eq]; apply hp _ hb
    calc
       _ = coeff b P * ((t:ℂ)^degree b * ∏ i∈b.support, (((W i.1 i.2:ℝ):ℂ))^(b i)) := by
             rw [show (t:ℂ)^degree b = ∏ i∈b.support,(t:ℂ)^(b i) by rw [degree_eq,Finsupp.sum,Finset.prod_pow_eq_pow_sum], ← Finset.prod_mul_distrib];congr 1
             exact Finset.prod_congr rfl fun i hi=> by change (((t*W i.1 i.2 : ℝ) :ℂ)^_) = _; rw [←mul_pow,Complex.ofReal_mul]
       _ = _ := by rw (occs:=.pos [1]) [show degree b=ℓ+(degree b-ℓ) from by omega] -- fix
                   rw [pow_add]; ring

lemma residual_zero (P:Pose G m)(a : Lens G d)(B:Fin m→RG.Slot)(r:ℝ)(hp:lows P ℓ):residual H ℓ P B a 0 r=symbolEval (d:=d) (rawPart B P ℓ) a.1 r := by
  unfold symbolEval rawPart
  simp_rw [aeval_rename,aeval_eq_eval₂Hom,coe_eval₂Hom,eval₂_eq];unfold residual
  rw [MvPolynomial.support_weightedHomogeneousComponent,Finset.sum_filter];simp_rw [coeff_weightedHomogeneousComponent]
  apply Finset.sum_congr rfl fun b hb=> ?_
  have hi : ℓ ≤ degree b:= by rw [degree_eq]; exact hp _ hb
  by_cases hj : degree b=ℓ
  · rw [if_pos hj,if_pos hj, hj, Nat.sub_self,pow_zero,mul_one, Algebra.algebraMap_self,RingHom.id_apply]
    unfold initialTerm; rw [show trim d (bring H d B) 0 (trunk d (scaleJet a.1 r))=fun i=>glow (trunk d (scaleJet a.1 r)) (B i) by simp_rw [← (Board.pegs H d).initial]; exact Scratch.core H B _]
    rfl
  simp only [Complex.ofReal_zero,zero_pow (n:=degree b-ℓ) (by omega),mul_zero,zero_mul,if_neg hj,decide_eq_false_iff_not.mpr hj,ite_false]

-- mixed continuation across the diagonal at theta=0, without assuming hol analytic in every argument
lemma residual_smooth (H : Hol G)(ℓ : ℕ)(P : Pose G m)(B : Fin m→RG.Slot)(a : Lens G d) : ContDiff ℝ ω (Function.uncurry (residual H ℓ P B a)) := by
  have h i: ContDiff ℝ ω (Function.uncurry (initialTerm H B a i)) := by
    have h:ContDiff ℝ ω (fun x : ℝ×ℝ=> (x.1,trunk d (scaleJet a.1 x.2))) := contDiff_fst.prodMk ((Board.trunk_nice ..).comp contDiff_snd)
    have h := (trim_smooth d (bring H d B)).comp h
    unfold initialTerm; convert! Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜:=ℝ) i.2).contDiff.comp ((contDiff_apply ℝ G.Color i.1).comp h))
  unfold residual Function.uncurry
  exact ContDiff.sum (𝕜:=ℝ) (s:=P.support) fun b hb=> (contDiff_const.mul <| (Complex.ofRealCLM.contDiff.comp contDiff_fst).pow ..).mul (contDiff_prod (t:=b.support) fun i hi=> (h i).pow ..)

theorem leading_correct (HF : F.Index)(P:Pose G m)(B:Fin m→RG.Slot)(hp:lows P (F.grades HF).2)
   (hm : Projects H (F.basis HF) (lumin P ∘ mapped B)) (a : Lens G d) :
   test (rawPart B P (F.grades HF).2) a = Push.CutoffProjectors.probe F a (Pi.single HF 1) := by
  let J:=a.1
  let T:=fun h=>trunk d (scaleJet J h)
  let ℓ:=(F.grades HF).2
  let R:=Function.uncurry (residual H ℓ P B a)
  let S (z):= iteratedDeriv a.2.val (fun t=>R (z,t)) 0
  have hS : Continuous S:=(varies a.2.val (residual_smooth H ℓ P B a)).continuous
  have hB : Pi.single HF (1:ℂ) = F.coords (F.basis HF) := (F.coords_basis _).symm
  let k:= a.2.val
  have hd:k≤d:=by dsimp [k];omega
  rw [hB,probe_eq,LinearEquiv.symm_apply_apply]
  have hu (z : ℝ)(hz : z>0): S z=iteratedDeriv k (fun t=> Labels.read (scaleJet J t) (F.basis HF).val) 0 := by
    have he t : (mapped B (H.links d (z • J) t))= bring H d B (z • T t):=by rw [scales H (d:=d),scaleSlot];rfl
    have hread t:Labels.read (scaleJet (z • J) t) (F.basis HF).val=((z:ℂ)^ℓ)*Labels.read (scaleJet J t) (F.basis HF).val := by
        have hg : scaleJet (z • J) t=z • scaleJet J t:= by funext i; simp [scaleJet]; rw [smul_smul,smul_smul,mul_comm]
        rw [hg, read_pure (scaleJet J t) (F.pure HF) z];simp only [Complex.real_smul,Complex.ofReal_pow,ℓ]
    have hf := (hm (z • J)).2.2 k hd
    change iteratedDeriv k (fun t=>lumin P (mapped B (H.links d _ t))) 0 = _ at hf
    simp_rw [he] at hf
    change iteratedDeriv k _ _ = iteratedDeriv k (fun t=> Labels.read (scaleJet (z • J) t) (F.basis HF).val) 0 at hf; simp_rw [hread] at hf
    let G' := bring H d B
    have hh :ContDiffAt ℝ ω G' 0 := contDiffAt_pi.mpr fun i => ((Board.pegs H d).shot (B i)).contDiffAt
    have h₀ : G' 0=0:=funext fun i=> takes_zero H d _
    have hr (t : ℝ) : lumin P (G' 0+ z•(trim d G' z (T t)))= ((z:ℂ)^ℓ) * R (z,t):=by rw [h₀,zero_add]; apply trim_eval P ..;exact hp
    have ht:=exchanged d (Nat.le_add_right_of_le hd) z hh (smooth_lumin P) (Board.trunk_nice J) (Board.trunk_zero J)
    change iteratedDeriv k _ 0=iteratedDeriv k (fun t=> lumin P (G' 0+ z•(trim d G' z (T t)))) 0 at ht
    simp_rw [hr] at ht
    let c:=(z:ℂ)^ℓ
    have hs (f:ℝ→ℂ):iteratedDeriv k (fun r=>c*f r) 0=c • iteratedDeriv k f 0 := by simpa only [Pi.smul_apply] using! iteratedDeriv_const_smul_field (n:=k) (x:=(0:ℝ)) c f
    have hq : ((z:ℂ)^ℓ)•S z=((z:ℂ)^ℓ) • iteratedDeriv k (fun t=> Labels.read (scaleJet J t) (F.basis HF).val) 0 :=
       (hs _).symm.trans <| ht.symm.trans <| hf.trans (hs _)
    exact (mul_left_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hz.ne')) hq)
  unfold test
  simp_rw [←residual_zero P a B _ hp (H:=H)]
  change S 0=iteratedDeriv k (fun t=> Labels.read (scaleJet J t) (F.basis HF).val) 0
  apply tendsto_nhds_unique (hS.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s:=Set.Ioi 0)))
  apply tendsto_const_nhds.congr'; exact (show ∀ᶠ z :ℝ in 𝓝[>] 0,0<z from self_mem_nhdsWithin).mono fun z hz=> (hu z hz).symm

end YM.PertExtension.Heat.Top
