import YM.WilsonBulk.Build.Rip

/-!
# Full fine Haar inputs and detector on tree comparisons

Include EVERY fine Haar coefficient in ω chart from available LocalRatio, using
`probHaar` direction; At ambient stage include factors on tree links too (to
be frozen by use and then vanish as constants because zero relative log on tree).
Thus no loop factor restricted by hand while shape mandatory on center. Use
Jacobian lemma across PRIVATE chart state and any alternate tree and reapportion
label volumes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Atelier
open Function Filter Lattice RG Wilson Tree Precision Exterior FreeResolvent Bloch
open Sheet
open Work.F05 (toll)
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius
variable {α β ι κ : Type} [Fintype κ] [Fintype ι] {G : Gauge} {J : ChartRatio G} {c f n : Side} {S : StepData c f}

-- input dictionary: indexed physical orientations positive at each bond

def realCost (n : Side) (J : ChartRatio G) (x : Interface G n) := ∑ e:Edge (Site n), Real.log (J.J (traces G n 1 x (e.1,coord e.2)))
def veil (c f : Side) (J : ChartRatio G) (x : Tabletop (Chamber (Pennant G f) (Pennant G c))) := realCost f J (upper _ _ x)
def haarTape (c f : Side) (J : ChartRatio G) := ink (veil c f J)
lemma cost_zero (hj : LocalRatio J) : realCost n J 0=0:= by simp [realCost,hj.anchored]
lemma cost_jet (hj : LocalRatio J) : ContDiffAt ℝ ω (realCost n J) 0 := by
  let T:= traces G n 1; unfold realCost; refine ContDiffAt.sum fun e _=> ?_
  let u x:= T x (e.1,coord e.2)
  have hx : u 0=0:= by simp [u]
  have hi : ContDiffAt ℝ ω u 0:= (contDiffAt_apply ℝ G.Color _ _).comp (f:= T) _ T.contDiff.contDiffAt
  exact ((show ContDiffAt ℝ ω J.J (u 0) by rw [hx]; exact hj.germ _ (Metric.mem_ball_self hj.patch)).comp 0 hi).log (by rw [Function.comp_apply, hx,hj.anchored]; exact one_ne_zero)
lemma veil_jet (hj : LocalRatio J) : ContDiffAt ℝ ω (veil c f J) 0 := by let T:= upper (Pennant G f) (Pennant G c); exact ((show ContDiffAt ℝ ω (realCost f J) (T 0) by rw [map_zero]; exact cost_jet hj).comp _ T.contDiff.contDiffAt)
lemma veil_zero (hj : LocalRatio J) : veil c f J 0=0:= by rw [veil,map_zero,cost_zero hj]
lemma haar_empty (hj : LocalRatio J) : PowerSeries.constantCoeff (haarTape c f J)=0 := ink_root (veil_zero hj)

namespace Coursing
variable {F L : Coursing ι S}
variable (G) (F)
lemma traces_free (x : Enter G ι) (k : F.tree.Free) : (traces G f 1 (quill (F.trunk G) x)) (k.val.1,coord k.val.2)= dress G F x k := by
  ext j; rw [dress_label,traces_at]
  have he : (F.dock G) (F.label.symm k,j)=ix (k.val.1,coord k.val.2) j := by simp only [dock, Function.comp_apply,flag,Equiv.prodCongr_apply,Equiv.apply_symm_apply,Equiv.refl_apply,Prod.map]; rfl
  rw [← he]; exact insertion_at _ x ((plant_inj F.tree).comp (F.flag G).injective) _
lemma traces_trunk (x : Enter G ι) (e : Edge (Site f)) (h : e∈F.tree.trunks) : traces G f 1 (quill (F.trunk G) x) (e.1,coord e.2)=0 := by
  ext j; rw [traces_at]; refine insertion_misses (F.dock G) x (ix (e.1,coord e.2) j) ?_
  rintro ⟨w,hw⟩; exact ((F.flag G w).1.property) ((show (F.flag G w).1.val=e from Prod.ext (congr_arg (fun i:Pennant G f=>i.1) hw) ((coord_iff ..).mp (congr_arg (fun i:Pennant G f=> i.2.1) hw))).symm ▸ h)
lemma veil_score (u : Tabletop (LegsT G ι)) (J : ChartRatio G) (hj : LocalRatio J) (he : dress G F u ∈ Work.F05.parcel F.tree J) :
    Real.exp (realCost f J (quill (F.trunk G) u))= toll F.tree J (dress G F u) := by
  unfold realCost toll; rw [Real.exp_sum]
  let f' (e : Edge (Site f)):= Real.exp (Real.log (J.J (traces G f 1 (quill (F.trunk G) u) (e.1,coord e.2))))
  have hb i (hp : i∈F.tree.trunks) : f' i=1:= by simp [f',traces_trunk G F u i hp, hj.anchored]
  have hp (i:F.tree.Free) : f' i.val=J.J (dress G F u i) := by unfold f'; rw [traces_free,Real.exp_log (hj.pos _ (he i (Set.mem_univ i)))]
  change (∏ i,f' i)=_
  let t : Finset (Edge (Site f)) := Finset.univ.filter (fun e=> e∉ F.tree.trunks); have hs : ∀ x, x∈t ↔ x∉ F.tree.trunks:= fun x=> by simp [t]
  rw [← Finset.prod_subset (Finset.subset_univ t) (fun i _ hx=>hb i (by rw [hs] at hx; exact not_not.mp hx)), Finset.prod_subtype t hs]; exact Finset.prod_congr rfl fun i _=> hp i
variable {G}
lemma tear_veil (P : Bed) (u : Tabletop κ→Interface G c) (hu : ContDiffAt ℝ ω u 0) (h : u 0=0) (J : ChartRatio G) (hJ : LocalRatio J) :
    let f:= (Real.exp ∘ veil c f J ∘ porch G F P u); f=ᶠ[𝓝 0] (fun z=>toll F.tree J (seatingA G F P u z)) := by
  let x:= seatingA G F P u
  have he : x 0=0:= by simp only [x,seatingA,whiten_zero _ h,map_zero];
  have hv : Tendsto x (𝓝 0) (𝓝 0):= he ▸ ((F.dress G).continuous.continuousAt.comp (whiten_jet (F:=F) (P:=P) G hu).continuousAt).tendsto
  refine (hv.eventually (Work.F05.parcel_zero F.tree hJ)).mono fun z hz=> ?_; exact veil_score G F _ J hJ hz
lemma carry_ink (P : Bed) (u : Tabletop κ→Interface G c) (hu : ContDiffAt ℝ ω u 0) (h : u 0=0) (J : ChartRatio G) (hJ : LocalRatio J) :
    let p:= submit (exposure (porch G F P u)) (haarTape c f J); tide p= ink (Real.exp ∘ veil c f J ∘ porch G F P u) := by
  intro p; unfold p haarTape; rw [← ink_comp (veil_jet hJ) (porch_jet _ hu) (porch_zero _ h)]; refine (ink_real_exp (f:=veil c f J ∘ porch G F P u) ?_ ?_).symm
  · apply ContDiffAt.comp; rw [porch_zero _ h]; exact veil_jet hJ; exact porch_jet _ hu -- maybe
  rw [Function.comp_apply, porch_zero _ h, veil_zero hJ]

variable (P : Bed) (u v : Tabletop κ→Interface G c)
lemma fee_received [DecidableEq ι] (hu : ContDiffAt ℝ ω u 0) (hx : u 0=0) (hv : ContDiffAt ℝ ω v 0) (hy : v 0=0) (J : ChartRatio G) (hJ : LocalRatio J)
    (R : Tabletop κ → Carries G S) (he : Legible R F P u) {V : Matrix (LegsT G ι) (LegsT G ι) ℝ} (h : Starting (exposure (lands R F L P u v)) V) :
    let p:= submit (exposure (porch G F P u)) (haarTape c f J); let q:= submit (exposure (porch G L P v)) (haarTape c f J); let θ := lands R F L P u v; tide p = switch (exposure θ) (tide q)*levy V (exposure θ) := by
  intro p q θ
  have hr : ∀ᶠ z in 𝓝 (0:Secrets G ι κ), toll F.tree J (seatingA G F P u z)= |(tilted θ z).det| * toll L.tree J (seatingA G L P v (ride θ z)) := invoice R F L P u v J hu hx hv hy he hJ
  have ht : θ 0=0:= lands_origin _ _ _ _ _ _ hx hy he.arrived
  have hT : ContDiffAt ℝ ω θ 0:= lands_jet _ _ _ _ _ _ hx hv he
  have hw : |(tilted θ 0).det|=1 := by have H:= hr.self_of_nhds; rw [ride_zero θ ht] at H; simpa only [seatingA,whiten_zero _ hx,whiten_zero _ hy,map_zero,toll,hJ.anchored,Pi.zero_apply,Finset.prod_const_one,mul_one] using H.symm
  let Z:= Real.exp ∘ veil c f J ∘ porch G L P v
  let Y:= Real.exp ∘ veil c f J ∘ porch G F P u
  have hg : ContDiffAt ℝ ω Z 0:= by
    unfold Z; apply Real.contDiff_exp.contDiffAt.comp; exact ((show ContDiffAt ℝ ω (veil c f J) (porch G L P v 0) by rw [porch_zero _ hy]; exact veil_jet hJ).comp _ (porch_jet _ hv))
  obtain ⟨h₁,h₂⟩:= levy_grain hT ht h hw
  have hp : ContDiffAt ℝ ω (Z ∘ ride θ) 0:= ((show ContDiffAt ℝ ω Z (ride θ 0) by rw [ride_zero θ ht]; exact hg).comp _ (ride_jet θ hT))
  have hq := ink_mul (g:=fun z=>|(tilted θ z).det|) hp h₁
  have hY : Tendsto (ride θ) (𝓝 0) (𝓝 0) := by simpa [ride_zero θ ht] using (ride_jet θ hT).continuousAt.tendsto
  have hZ : Y=ᶠ[𝓝 0] (Z ∘ ride θ)*(fun z=>|(tilted θ z).det|) := by
    filter_upwards [tear_veil F P u hu hx J hJ,hr,hY.eventually (tear_veil L P v hv hy J hJ)] with z hz he hx; unfold Y; rw [hz,he,mul_comm]; exact congr_arg (fun u : ℝ=> u* |(tilted θ z).det|) hx.symm
  rw [show tide p = ink Y from carry_ink F P u hu hx J hJ, show tide q=ink Z from carry_ink L P v hv hy J hJ,ink_of hZ,hq, ink_comp hg (ride_jet θ hT) (ride_zero θ ht),ride_pull,h₂]
end Coursing
end YM.WilsonBulk.Atelier
