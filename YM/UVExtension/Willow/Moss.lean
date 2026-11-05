import YM.UVExtension.Willow.Feather
import YM.UVExtension.Willow.Reed
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
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} 
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
local notation "Δ" => (F.order G).prod (volume : Measure (Body (↥Kp)))
local notation "A" => lantern (H:=H) (V:=V) X p M
variable {q' : Q.rate≤γ} {h':γ<0} {l t r d:ℝ}
variable (Y:Pavilion H V B γ v d q' h') (hY : Pouch G L x l)(hR:0 ≤ Q.exp-l)
local notation "ι'"=> radiusB x
local notation "b'"=> ((stalk Q q' h').costs L μ)
local notation "m'"=> M.turn.badge S
variable (k:ℕ)
abbrev ceiling (i:ℕ)(M:Lotus.Leaf R):= M.weight*Copse.worth i (radiusB x) (Q.exp+Q.δ) (H.supportP (M.turn.badge S)) -- exponent δ
variable {z:Vines ι}(hz:z∈parade (betaF G x L) B)
variable {H' : Cash W x μ L Q o a T (Wick.flight R (z none).re)} (N:Copal H' ((stalk Q q' h').costs L μ (z none).re x v) V B (z none))
def buoy (k:ℕ)(l:ℝ):= if m'∈p ∧ Ac.Spark H.supportP p then M.weight * (∏ i∈p.erase m',tabs S (b' (z none).re x v) (radiusB x) Q.halo N.fee i)*Copse.worth k (radiusB x) l (H.unionP p) else 0
lemma heights : SumBudget (fun p=> buoy (H:=H) p M N k l*Copse.worth k (radiusB x) (Q.exp-l) (H.unionP p)) (ceiling (H:=H) k M):=by
  let t:=b' (z none).re x v; have hh:t.Buy S.patch.L Q.halo (radiusB x):=by rw [H.laws.data.funds.length_eq]; exact N.paper
  obtain ⟨hf,he,hp⟩:= royalties (H:=H) (Z:=N.fee) (k:=t) N.added hh
  let v':= tabs S t ι' Q.halo N.fee
  have ht := Copse.flights H.supportP ι' k (a:=t.exponent) hf he hp hh.γ.le hh.price m'; convert budget_scale M.profit ht using 1
  ext1 p; unfold buoy Copse.flight; split
  next h=> rw [mul_assoc _ (Copse.worth ..),show (Finset.biUnion p H.supportP)=H.unionP p from rfl]; unfold Copse.worth t; rw [←Real.exp_add, show (stalk Q q' h'|>.costs L μ (z none).re x v|>.exponent)=Q.exp from rfl]; ring_nf
  next h=> ring
  rfl
include K hx hX hm hl hY hz
lemma fares (ht:m'∈p)(he:Ac.Spark H.supportP p): Integrable (A z) Δ ∧ (∫ y, ‖A z y‖ ∂Δ)≤ buoy (H:=H) p M N k l:=by
   obtain ⟨hx',hv⟩:= ferns X K hx hX hm p M hl N hz ht; unfold buoy; rw [if_pos ⟨ht,he⟩]; refine ⟨hx',hv.trans ((mul_le_mul_of_nonneg_right (show permag (z none) (Kp).card≤ Copse.worth k (radiusB x) l (H.unionP p) from ?_) ?_).trans_eq ?_)⟩
   · rw [show X.B=radiusB x from congr_arg _ hx]; exact hY.step c f S (H.unionP p) (z none) (H.laws.data.funds.length_eq) ((marching _).1 hz).1 k
   · refine mul_nonneg M.profit (prod_nonneg fun i _=>?_); exact (royalties (H:=H) N.added (show ((stalk Q q' h').costs _ _ _ _ _).Buy S.patch.L Q.halo (radiusB x) from (by rw [H.laws.data.funds.length_eq]; exact N.paper))).1 _
   ring
omit hz
include hR Y
-- at any VALID.S and mark leaf. analytic hol.M
lemma golden (k:ℕ) (ht:m'∈p) (he:Ac.Spark H.supportP p) : Bumps Σ (whorls (H:=H) (V:=V) X p M) := by
   intro U R hS hf ht'
   have he' (z:ℂ)(hz:z∈U) : Integrable (A (R z)) Δ ∧ (∫ y, ‖A (R z) y‖ ∂Δ)≤ ceiling (H:=H) k M:=by
      obtain ⟨X',⟨N⟩⟩:=Y.build _ (hf hz); obtain ⟨hp,hq⟩:= fares X K hx hX hm p M hl hY k (hf hz) N ht he
      have hu:0 ≤ buoy (H:=H) p M N k l:=by apply nonneg_of_mul_nonneg_left ((heights M k N).1 p) (Real.exp_pos _)
      exact ⟨hp,hq.trans ((le_mul_of_one_le_right hu (Real.one_le_exp (mul_nonneg hR (Nat.cast_nonneg _)))).trans (budget_single (heights M k N) _))⟩
   apply Lamppost.tint (F:=fun z=> A (R z)) (μ:=Δ) hS _ (fun i hi=> (he' i hi).1) (fun i hi=>(he' i hi).2)
   intro i; apply DifferentiableOn.mul _ (dips (H:=H) (V:=V) X p M _ U R hS hf ht'); apply bulbs_hol _ _ ((ContinuousLinearMap.proj (R:=ℂ) («φ»:=fun _:Option ι=>ℂ) none).differentiable.comp_differentiableOn ht') (fun i h=> breath (altitude (H:=H)) ((marching _).1 (hf h)).1)
omit hm
lemma bud : Bumps Σ (treeP (H:=H) (V:=V) M X p):=by
   unfold treeP; split; swap; · exact Lamppost.bumps _ _ (differentiableOn_const _)
   next h =>
   by_cases hy:m'∈ p; swap; · simp_rw [fun i=> quietL (H:=H) (V:=V) ((planted X p).taggedL i) p M hy,Pi.zero_apply]; exact Lamppost.bumps _ _ (differentiableOn_const _)
   have hp : Ac.Spark H.supportP p:= by have hh:=h.1; unfold Coat.B at hh; rw [hx] at hh; exact hh
   intro U f hS hf ht; exact (DifferentiableOn.fun_sum (fun i (_:i∈Finset.univ)=> golden ((planted X p).taggedL i) K hx hX (planted_valid ..) p M hl Y hY hR 0 hy hp U f hS hf ht)).const_mul _ -- k argument
include hz
omit hR Y
lemma bough : ‖treeP (H:=H) (V:=V) M X p z‖≤ buoy (H:=H) p M N k l:=by
   have hu:0 ≤ buoy (H:=H) p M N k l:= nonneg_of_mul_nonneg_left ((heights M k N).1 p) (Real.exp_pos _)
   unfold treeP; split; swap; · exact (norm_zero).trans_le hu
   next h =>
   by_cases hy:m'∈p; swap; · simp_rw [fun i=> quietL (H:=H) (V:=V) ((planted X p).taggedL i) p M hy]; simp [hu]
   have hp : Ac.Spark H.supportP p:=by have hh:= h.1; unfold Coat.B at hh; rw [hx] at hh; exact hh
   have hY(i): ‖whorls (H:=H) (V:=V) ((planted X p).taggedL i) p M z‖≤ buoy (H:=H) p M N k l:= (norm_integral_le_integral_norm _).trans (fares ((planted X p).taggedL i) K hx hX (planted_valid ..) p M hl hY k hz N hy hp).2
   rw [norm_mul,norm_inv,Complex.norm_natCast]; exact (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun i _=> hY i))) (by positivity)).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul,inv_mul_cancel_left₀ (by positivity)])
end YM.UVExtension.Willow
