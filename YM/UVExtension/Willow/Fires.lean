import YM.UVExtension.Willow.Stains
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Willow
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} {z : Air f G} {Y : Config G c}
open Animals Reserves Wick Festa PhysicalNext.Repeat.Lotus
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R} {V : ι → Juice G f}
open PhysicalNext.Repeat
variable (K : Festa Q L H V b B) (hx:X.x=x) (hX : X.width=o.K) (hm:X.manifest)
    (p : Molecule S) (M:Lotus.Leaf R) (hl:Lines R V b (betaF G x L) M) -- using PhysicalNext.Repeat to open
local notation "Σ" => parade (ι:=ι) (betaF G x L) B
local notation "φ" => grains X R W o.a Q.table Q.halo V M p
local notation "Kp" => podium S G (H.unionP p) X.B
local notation "Λ" => grown (ι:=ι) (betaF G x L) b
set_option quotPrecheck false
def lantern (y : Vines ι) (w : F.Slice G × Body (↥(podium S G (H.unionP p) X.B))) : ℂ := bulb (circuit _ X.relating) w.2 (y none) *grains X R W o.a Q.table Q.halo V M p y (w.1,spill _ w.2)


local notation "Γ" => (F.order G).prod X.dice
local notation "Δ" => (F.order G).prod (volume : Measure (Body (↥Kp)))
local notation "A" => lantern (H:=H) (V:=V) X p M
variable {k:Mixed.Costs} {t:Vines ι}
    {H' : Cash W x μ L Q o a T (flight R (t none).re)} (N:Copal H' k V B (t none))
include hl K hx hX hm N
lemma ferns (ht:t∈Σ) (hi:M.turn.badge S∈p) :
    Integrable (A t) Δ ∧ (∫ u, ‖A t u‖ ∂Δ)≤permag (t none) (Kp).card*(M.weight*(∏ i∈p.erase (M.turn.badge S),tabs S k (radiusB x) Q.halo N.fee i)):= by
  let u:= (t none).re; let Φ (v:F.Slice G × Air f G):=φ t (v.1,gStep u • v.2)
  have ha := (marching t).1 ht
  have hv:0<u:= breath (altitude (H:=H)) ha.1
  have ht' : 0<gStep u:= inv_pos.mpr (Real.sqrt_pos.mpr hv)
  let Y:= tabs S k (radiusB x) Q.halo N.peeled
  let q:= p.erase (M.turn.badge S); let y:= M.weight*(∏ i∈q,Y i)
  have hy : 0≤y:=mul_nonneg M.profit (prod_nonneg fun i _=> by
    rcases i with i|i; unfold Y tabs Mixed.costs; dsimp only [Sum.elim]; split; exact mul_nonneg N.paper.capture (Real.exp_pos _).le; exact le_rfl
    exact N.peeled_nn _)
  let J:= X.catastrophe o.ξ u (blaze q); let f (i:F.Slice G × Air _ G):= J.indicator (fun _=> y) i.2
  have hc : MeasurableSet J:= Poll.sounded ..
  have hf: Integrable f Γ:= ((integrable_const y (μ:=X.dice)).indicator hc).comp_snd _
  have hV (i:F.Slice G × Air _ G): ‖Φ i‖ ≤ f i:= by
    rcases i with ⟨v,z⟩; unfold f Φ
    let P:=X.wrapY v; let D:=t∘some
    let W i:=fireball P R Q.table W o.a (Matter.own p) Q.halo V (t none) D (gStep u • z) i
    unfold grains; dsimp only; rw [if_pos hi]; let Z:= (gStep u) • z; let k:ℂ:= ↑(M.paidU P o.a (P.μ+P.atmos Z)); have he: ‖k‖≤ M.weight:= (Complex.norm_real _).trans_le (M.coin ..)
    change ‖k*(∏ i∈q, W i)‖≤ Set.indicator J _ z
    by_cases h:z∈J
    · rw [Set.indicator_of_mem h,norm_mul,norm_prod]; refine mul_le_mul he ?_ (prod_nonneg fun i _=> norm_nonneg _) M.profit; apply prod_le_prod (fun _ _=> norm_nonneg _)
      exact fun i _=> N.voice D (fun i=> (ha.2 i).le) _ P hx hX hm i _ _
    rw [Set.indicator_of_notMem h]; suffices h: (∏ i∈q,W i)=0 by rw [h,mul_zero,norm_zero]
    by_contra hz; apply h
    refine (H'.quotes F P hx hX hm).2.2.2 (blaze q)|>.2 (Matter.own p) z ?_
    intro i hi he; apply hz; apply Finset.prod_eq_zero (mem_toRight.mp (mem_toRight.mp (mem_toRight.mp hi)))
    let g:= P.detect (P.μ+P.atmos (gStep u • z))
    have hh : P.μ+P.atmos (gStep u • z)=P.liftA u z:=rfl
    unfold W; dsimp only [fireball, Sum.elim]; rw [hh]; change ((P.detect _ _ _ (flight R u) _ i:ℝ):ℂ)=0; exact (congr_arg Complex.ofReal he).trans Complex.ofReal_zero
  have hm' : Measurable Φ:= (crew X K hx hX p M hl t ht).measurable.comp (measurable_fst.prodMk (by fun_prop))
  have hI := hf.mono' hm'.aestronglyMeasurable (Eventually.of_forall hV)
  let U := circuit Kp X.relating
  have hp := (H.laws.data.localP _ X hx hX hm).sails.fullC; have hu': U.PosDef:=hp.submatrix Subtype.val_injective
  let μ := (F.order G).prod (arch Kp X.relating)
  let g : F.Slice G × Body (↥Kp) → ℝ := fun x=> ‖Φ (x.1,spill Kp x.2)‖
  have hg : Measurable g:= hm'.norm.comp (measurable_fst.prodMk ((spill_m Kp).comp measurable_snd))
  let E:=(Prod.map (id:F.Slice G→_) (Pond.swim Kp))
  have hx' : MeasurePreserving E Γ μ:= sweeping X Kp hp
  have he' : g ∘ E= fun i=> ‖Φ i‖:= by
    funext i; apply congr_arg norm; refine caps X K hx p M hl t ht i.1 _ _ ?_
    change gStep u • swim Kp (spill _ _) = gStep u • Pond.swim _ _; rw [Pond.settled]; try rfl
  have hζ : Integrable g μ:= (hx'.integrable_comp hg.aestronglyMeasurable).mp (he'.symm ▸ hI.norm)
  let ρ:= permag (t none) (Kp).card
  have hh x : ‖A t x‖= ρ*tether U u g x:= by
    let z:= x.2; unfold lantern; rw [norm_mul,bulbs U z hv, Fintype.card_coe]
    unfold tether; dsimp only [g,Φ]; rw [spilling, smul_inv_smul₀ ht'.ne']; change _= ρ*((lint _ _* _)*_); unfold ρ u z; rw [Fintype.card_coe]; ring
  have hg': Integrable (fun i=> ‖A t i‖) Δ := by simp_rw [hh]; exact ((gear _ U hu' hv _).1 hζ).const_mul _
  have ha : Measurable (A t):= (bulbs_meas U _|>.comp measurable_snd).mul ((crew X K hx hX p M hl t ht).measurable.comp (measurable_fst.prodMk ((spill_m Kp).comp measurable_snd)))
  refine ⟨(integrable_norm_iff ha.aestronglyMeasurable).mp hg',?_⟩
  simp_rw [hh]; rw [integral_const_mul,← axle _ U hu' hv]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; change (∫ i, g i ∂μ) ≤ _
  rw [← hx'.map_eq, integral_map hx'.measurable.aemeasurable (hx'.map_eq.symm ▸ hg.aestronglyMeasurable)]
  change (∫ i,g.comp E i ∂Γ) ≤ _; rw [he']; apply (integral_mono hI.norm hf hV).trans
  rw [integral_prod _ hf]; have he i : (∫ z,f (i,z) ∂X.dice)=X.dice.real J*y:= integral_indicator_const y hc
  simp_rw [he]; rw [integral_const]; simp only [probReal_univ,one_smul]; exact le_trans (mul_le_mul_of_nonneg_right ((H'.quotes _ X hx hX hm).2.2.2 _|>.1) hy) (show _ ≤ _ from (by unfold y; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (N.posts q) M.profit))
end YM.UVExtension.Willow
