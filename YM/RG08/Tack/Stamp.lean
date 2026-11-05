import YM.RG08.Tack.Bowl

/-! # Germ exact input/transform identification on every period via actual branch law.
    Haar probability normalization constant kept on scalar side. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Tack
open Filter Lattice RG Wilson Forms Pert.Bulk Isles Camera Carrel Glyph Room Exterior Function
open Stationary Bloch Laurent Precision Line Finset Bid Work.F03 Matrix
open AnalyticNext.QuarticMatch.Radius Articles Model
open scoped BigOperators Classical ContDiff Topology Matrix Matrix.Norms.Frobenius NNReal InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{c f:Side}{S:StepData c f}{P:Patch}{K:KernelChoices}
variable {I : Type}[Fintype I]

/-- Actual density germ equality in these log coords. λ step adjacent at a time on same g.
 Uniform LEAF pick t and s=1, but all tags including unused truly sum to one; equality
 here a real identity modulo vacuum scalar *not dropped before proving*. -/
lemma perfume (h:S.patch.Branches S.kernel G) (t:S.Choices): ∀ᶠ w: Cellar (Epic S.patch G c) in 𝓝 0,
   ∀ β,S.density β (represent (low S w)) (represent (high S w)) = (S.penaltyZ β G)⁻¹^(Fintype.card (Edge (Site c))) * Real.exp (-β*fair (S) (G:=G) t w):=by
 have he(t' : S.Choices)(q:Site c)(i:Axis): ask S t' i q (G:=G) =ᶠ[𝓝 0] ask S t i q:=(ask_real h t' i q).trans (ask_real h t i q).symm
 have hv :∀ᶠ w:Cellar (Epic S.patch G c) in 𝓝 0, ∀ (t':S.Choices)(i:Axis) (q:Site c), ask S t' i q w=ask S t i q w:=eventually_all.mpr (fun _ => eventually_all.mpr (fun _=>eventually_all.mpr (fun _=>he ..)))
 filter_upwards [hv] with w hw
 intro β
 have hn (t':S.Choices): S.noise β (S.prediction (represent (low S w)) t') (represent (high S w))= (S.penaltyZ β G)⁻¹^(Fintype.card (Edge (Site c))) * Real.exp (-β*fair S t w):=by
   unfold StepData.noise StepData.penaltyWeight;rw [prod_mul_distrib,prod_const,card_univ,←Real.exp_sum]
   congr 2
   rw [Fintype.sum_prod_type]
   unfold fair; simp_rw [Finset.sum_apply]; rw [Finset.sum_comm,Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i _
   rw [←hw t']; unfold ask; rw [mul_assoc]
 unfold StepData.density; simp_rw [hn];rw [←Finset.sum_mul,S.chosen h _,one_mul]

-- actual map identity when A/B both read this unpacking
lemma redress {M N:Strip (Epic S.patch G c) I}(h:S.patch.Branches S.kernel G)(t:S.Choices)
    (hs:∀ i,Pace (M i))(ht:∀ i,Pace (N i))(hm:roll M 0=0)(hn:roll N 0=0)
    (hh:∀ᶠ z:Cellar I in 𝓝 0, let K(x:Cellar (Epic S.patch G c)):=S.density 1 (represent (low S x)) (represent (high S x))
      ; K (roll M z)=K (roll N z)):
    belt (rescaleFields M) (tax 2 (flask (fair (G:=G) S t)))=belt (rescaleFields N) (tax 2 (flask (fair (G:=G) S t))):=by
 rw [wire_taxes _ _ (fare_low h t),wire_taxes _ _ (fare_low h t),← flask_comp hs hm (fair_pace h t),← flask_comp ht hn (fair_pace h t)]
 apply congrArg (tax 2); apply flask_same
 have he: Tendsto (roll M) (𝓝 0) (𝓝 0):=by simpa only [hm] using (roll_pace hs).continuousAt.tendsto
 have hf: Tendsto (roll N) (𝓝 0) (𝓝 0):=by simpa only [hn] using (roll_pace ht).continuousAt.tendsto -- maybe `Tendsto ..` hidden
 filter_upwards [he.eventually (perfume h t),hf.eventually (perfume h t),hh] with z hM hN hp
 change S.density _ _ _=S.density _ _ _ at hp
 rw [hM 1,hN 1,mul_right_inj' (pow_ne_zero _ (inv_ne_zero (S.penaltyZ_pos _).ne'))] at hp
 simpa using (Real.exp_injective hp)

lemma dress (C:Calendar G)(m p:ℕ)(h:C.BlockControl m p)(s:Signed)(v:Site (C.schedule.side m p)):
 let S:=C.op m p;∀ (M N:Strip (Epic S.patch G _) I)(t:S.Choices), (∀ i,Pace (M i))→(∀ i,Pace (N i))→ roll M 0=0→ roll N 0=0→
   (∀ᶠ z in 𝓝 0,∃ U:Site (C.schedule.side (m+1) p)→G.El,
    represent (low S (roll N z))=Lattice.gauge U (Lattice.pull s (S.ratio.embed v) (represent (low S (roll M z)))) ∧
    represent (high S (roll N z))=Lattice.gauge (U ∘ S.ratio.embed) (Lattice.pull s v (represent (high S (roll M z)))))→
    belt (rescaleFields M) (tax 2 (flask (fair (G:=G) S t)))=belt (rescaleFields N) (tax 2 (flask (fair (G:=G) S t))):=by
 intro S M N t hM hN Mh Nh hh;apply redress h.branches t hM hN Mh Nh
 filter_upwards [hh] with z hz;obtain ⟨U,hx,hy⟩:=hz
 dsimp only;rw [hx,hy,h.gauge,h.symmetric]
end YM.RG08.Tack
