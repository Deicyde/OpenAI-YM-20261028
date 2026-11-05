import YM.Further.ROOTED_INTERACTING_REMAINDER.Far
/-!
# beta-cost of looking through the intact profiles in the far zone
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.RootedInteractingRemainder
open Filter Function Lattice RG Wilson Pressure Pressure.Stores Pressure.Teller Next.Fluctuations
open Next.Fluctuations.Sector Push.SectorMeasure Oriented Tree
open scoped Topology BigOperators Classical
variable {G : Gauge} {L : Side}

lemma fade_small (D C J τ : ℝ) (hD : 0 < D) (hC : 0 < C) (hJ : 0 < J) (hτ : 0 < τ) :
    Tendsto (fun x : ℝ => let b := betaF G x L
      (2*b)*fade (fiery G x L) (stitchCost G L J x) (temp x) (till x) D C τ)
      atTop (𝓝 0) := by
  let b := fun x => betaF G x L
  have hb := Work.E09.betaF_growth G L
  have hr : ∀ᶠ x : ℝ in atTop, (radiusB x:ℝ)^10 ≤ (b x) ^ (1/100:ℝ) := by
    filter_upwards [(Work.E09.radiusB_shift G L (1/100) (by norm_num) 10).bound (c:=1) zero_lt_one,
      hb.eventually_ge_atTop 0] with x hx hy
    simpa only [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hy _),
      Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg _) 10)] using hx
  let M := 2*J+1
  let K := 4*D*C*J*M+2*D^2*C*M+32*C
  refine squeeze_zero' ?_ ?_ (g:=fun x => K*(b x)^(-(1/5):ℝ))
    (by simpa using (((tendsto_rpow_neg_atTop (y:=(1/5:ℝ)) (by norm_num)).comp hb).const_mul K))
  · filter_upwards [hb.eventually_ge_atTop 0] with x hx
    have hs := Push.SectorMeasure.temp_nonneg x
    have ht : 0≤fiery G x L := Push.SectorMeasure.temp_nonneg _
    have hh : 0≤stitchCost G L J x := by unfold stitchCost largeT; positivity
    have he := widen_nonneg (till x) (τ:=τ) hh
    unfold fade; positivity
  filter_upwards [hb.eventually_ge_atTop 1,tail_delay G L τ hτ,
    hb.eventually (Work.E09.temp_cost (1/100) (by norm_num)), hr,
    Work.E04.eventually_temp_le _ (Work.E04.shift_nonneg G L), Work.E08.eventual_radiusB 1] with x hx htP ht hb' he' hv
  let t := fiery G x L; let s := temp x
  let h := stitchCost G L J x
  let e := widen (till x) h τ
  let z := b x; let p (v : ℝ) := z ^ v
  have hy : 1≤z := hx
  have hz : 0<z := zero_lt_one.trans_le hy
  have hs := Push.SectorMeasure.temp_nonneg x
  have ht' : 0≤t := Push.SectorMeasure.temp_nonneg _
  have hh : 0≤h := by unfold h stitchCost largeT; positivity
  have he : 0≤e := widen_nonneg (till x) (τ:=τ) hh
  have hadd (i j : ℝ) : p i*p j = p (i+j) := (Real.rpow_add hz i j).symm
  have hle : Monotone p := fun i j hij => Real.rpow_le_rpow_of_exponent_le hy hij
  have hp (i : ℝ) : 0 ≤ p i := (Real.rpow_pos_of_pos hz _).le
  let v : ℝ := -(40/100)
  -- h ≤ J*z^(-48/100), t ≤ z^(-49/100); bring them all to `v`.
  have hT : t≤p v := le_trans (by simpa only [t,p,z,b,fiery, show -(1/2:ℝ)+1/100=-(49/100) by ring] using ht : t≤p (-(49/100))) (hle (by dsimp [v]; norm_num))
  have hS : s≤2*p v := he'.trans (mul_le_mul_of_nonneg_left hT (by norm_num))
  have hH : h≤J*p (-(48/100)) := by
    unfold h stitchCost; rw [Work.E09.largeT_eq _ _ _ hz.le,mul_assoc]; apply mul_le_mul_of_nonneg_left _ hJ.le
    change _ * p _ ≤ _
    refine (mul_le_mul_of_nonneg_right hb' (hp _)).trans_eq ?_
    change p _*p _= _
    rw [hadd,show (1/100:ℝ) + -(49/100) = -(48/100) by norm_num]
  have hH' := hH.trans (mul_le_mul_of_nonneg_left (hle (by dsimp only [v]; norm_num : (-(48/100):ℝ) ≤ v)) hJ.le)
  have hhB : (1:ℝ)+till x ≤ 2 * p (1/100) := by
    have hm : (till x:ℝ) ≤ (radiusB x:ℝ) := by exact_mod_cast Nat.div_le_self _ _
    have hv : (1:ℝ) ≤ radiusB x := by exact_mod_cast hv
    have hx' : (radiusB x:ℝ) ≤ p (1/100) := calc
      _ = (radiusB x:ℝ)^1 := (pow_one _).symm
      _ ≤ (radiusB x:ℝ)^10 := pow_le_pow_right₀ hv (by norm_num)
      _ ≤ _ := hb'
    linarith
  have hE : e ≤ M*p v := by
    unfold e widen
    have hm' : 0 ≤ 2*p (1/100) := by apply mul_nonneg _ (hp _); norm_num
    have hm := mul_le_mul hhB hH hh hm'
    have hf : z⁻¹ ≤ p v := le_trans (Real.rpow_neg_one z).symm.le (hle (by dsimp [v]; norm_num))
    have hl : 2*p (1/100)*(J*p (-(48/100))) ≤ (2*J)*p v := by
      rw [mul_mul_mul_comm,hadd]; exact mul_le_mul_of_nonneg_left (hle (by dsimp [v]; norm_num)) (by positivity)
    change Real.exp _ ≤ z⁻¹ at htP
    unfold M
    exact (add_le_add (hm.trans hl) (htP.trans hf)).trans_eq (by rw [add_mul,one_mul])
  let r := p v
  have hR : 0≤r := hp _
  have hv₁ : z * (2*(D*t)*(C*h*e)) ≤ z*(2*(D*r)*(C*(J*r)*(M*r))) := by
    gcongr
  have hv₂ : z * (D*t*(C*(D*t)*e)) ≤ z*(D*r*(C*(D*r)*(M*r))) := by
    gcongr
  have hv₃ : z * (C*s^4) ≤ z*(C*(2*r)^4) := by
    change z*(C*(temp x)^4) ≤ _
    gcongr
  have h0 : p 1=z := Real.rpow_one _
  have hx : z*r*r*r = p (-(1/5)) := by
    unfold r; rw [← h0,hadd,hadd,hadd,show (1+v+v+v:ℝ)=-(1/5) by unfold v; norm_num]
  have hu : z*r*r*r*r ≤ p (-(1/5)) := by
    unfold r; rw [← h0,hadd,hadd,hadd,hadd]; exact hle (by unfold v; norm_num)
  change 2*z*(2*(D*t)*(C*h*e)+(D*t)*(C*(D*t)*e)+C*s^4) ≤ K*p _
  unfold K
  -- factors linear in z*r^4 exactly
  nlinarith only [hv₁,hv₂,hv₃,
    show 4*D*C*J*M*(z*r*r*r)=4*D*C*J*M*(p (-(1/5))) by rw [hx],
    show 2*D^2*C*M*(z*r*r*r)=2*D^2*C*M*(p (-(1/5))) by rw [hx],
    mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 32*C)]

/-- Cost in the exponent, through the hat-band width – arbitrarily small
positive per output cell cost paid POST L. Do not offer for calls after
profile deletion! `sums` and exact `Seeded` at D needed throughout. -/
theorem settled_exterior (P : Teller G) (L : Side) (W ε : ℝ) (hW : 0<W) (hε : 0<ε) :
    ∀ᶠ x : ℝ in atTop, ∀ c f : Side, ∀ S : StepData c f, S.patch.L=L → 100*(1+radiusB x) ≤ c.val →
      ∀ T : Tube G S, P.Funds S T → ∀ (F : Forest S.ratio) (A : Stores S) (U : Config G f)
        (k : S.Choices) (V : Config G c), SliceSet S F U → Alive S U k → Seeded A U k V x W →
          ∀ β : ℝ, 0≤β → β ≤ 2*betaF G x L →
            -β*meanRest A T x U k V ≤ ε*(Fintype.card (Site c):ℝ) := by
  obtain ⟨D,C,J,τ,hD,hC,hJ,hτ,H⟩ := far_station P L W hW
  let M := (Fintype.card PlaqAxes : ℝ)
  have h : Tendsto (fun x => M*((2*betaF G x L)*fade (fiery G x L) (stitchCost G L J x) (temp x) (till x) D C τ)) atTop (𝓝 0) := by
    have h := (fade_small (G:=G) (L:=L) D C J τ hD hC hJ hτ).const_mul M
    simpa only [mul_zero] using h
  filter_upwards [H,h.eventually (ge_mem_nhds hε)] with x hx hy
  intro c f S hL hN T hT F A U k V hs hk hh β hp hb
  let E := fade (fiery G x L) (stitchCost G L J x) (temp x) (till x) D C τ
  let n := (Fintype.card (Site c):ℝ)
  have he := hx.2 c f S hL hN T hT F A U k V hs hk hh
  calc
    _ ≤ β*((Fintype.card (Cell c):ℝ)*E) := by nlinarith only [he,hp]
    _ ≤ (2*betaF G x L)*((Fintype.card (Cell c):ℝ)*E) := mul_le_mul_of_nonneg_right hb (mul_nonneg (Nat.cast_nonneg _) hx.1)
    _ = (M*((2*betaF G x L)*E))*n := by
      simp only [Cell,Face,Fintype.card_prod,Nat.cast_mul]; dsimp only [Site,n,M]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hy (by positivity : 0≤(Fintype.card (Site c):ℝ))

end YM.Further.RootedInteractingRemainder
