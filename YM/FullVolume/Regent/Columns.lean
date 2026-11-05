import YM.FullVolume.Train.Miracles
import YM.FullVolume.Canvas.Mails
import YM.FullVolume.Vision.Hazel
import YM.Extra.WILSON_STARTUP.TopStep
/-! columns E analytic & limit. Ellon.Band → passes.T.Clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F02
open Lattice RG Precision Wilson Function Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G:Gauge}{n:Side}
lemma pureRow {b:PathData G} {p:Face (Per n)}{σ A:ℝ}(hv:0<σ)(h:SumBudget (fun i=> |(b.row p.2 i).1| * Real.exp (σ * (b.row p.2 i).2.length)) A){X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]{U:X→ Config G n}{x:X}(he: ∀ i,ContDiffAt ℝ ω (fun y=> G.mat (U y i)) x): ContDiffAt ℝ ω (fun i=> b.ell (U i) p) x:=by
     let L:=fun M:Ambient G n=> ∑' i,rowExt b p i M
     have hh : AnalyticAt ℂ L (physical (U x)) :=by
          refine analytic_series _ (radius_pos hv) ?_ (h.2.1.mul_right (slotConst G)) ?_
          · intro i; have hg : ContDiff ℂ ω (rowExt b p i) := (slotExt_contDiff (b.row p.2 i).2 p.1).const_smul (b.row p.2 i).1; exact hg.differentiable (by simp)
          intro i M hM; unfold rowExt; rw [norm_smul,Real.norm_eq_abs]; exact (mul_le_mul_of_nonneg_left (slotExt_bound (U x) hv M (ball_subset_closedBall hM) (b.row p.2 i).2 p.1) (abs_nonneg _)).trans_eq (by ring)
     have hm y : L (physical (U y)) = colorUp G (b.ell (U y) p):=by
          unfold PathData.ell L; rw [(colorUp G).map_tsum];swap
          · refine Summable.of_norm_bounded (h.2.1.mul_right 2) fun i=>?_ ; unfold PathData.ellTerms; rw [norm_smul,Real.norm_eq_abs]; refine mul_le_mul (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (by positivity))) (Slot.eval_norm ..) (norm_nonneg _) (by positivity)
          exact tsum_congr fun i=> by rw [rowExt,PathData.ellTerms, slotExt_physical,map_smul]
     have hu : (fun y => b.ell (U y) p)=colorReal G ∘ (L ∘ (fun y => physical (U y))) := funext fun i=>by simp only [Function.comp_apply,hm,colorReal_up]
     rw [hu]; exact (colorReal G).contDiff.contDiffAt.comp x ((hh.contDiffAt.restrict_scalars ℝ).comp x (physical_contDiffAt he))
end YM.Work.F02
namespace YM.Stationary.Beacon
open Lattice RG Precision Wilson Filter Function Laurent Bloch Exterior Next.Free.Retort Tralis Shade
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G:Gauge}{n:Side}{P:PathData G}
def flag (i:ℕ) := walkSlot (addresses i).1 (addresses i).2
def channel (σ:ℝ)(i:ℕ):=Real.exp (σ*(flag i).length)
lemma coins {σ:ℝ}(h:0<σ): Summable (channel (-σ)):=by
    have H:= Width.compactPay (α:=Axis) _ h
    let K(x:PlaqAxes×Cover):=Real.exp (-σ*size x.2)
    have he: Summable K:= (budget_prod_finite (f:=K) (fun i=> H)).2.1
    let L:= Real.exp (-σ*4)
    exact ((addresses.summable_iff.mpr he).mul_right L).congr (fun i=> by unfold L K Function.comp channel flag; rw [←Real.exp_add,walkSlot_cost]; norm_cast; push_cast; ring_nf)
private def plate (C:Lights ℕ) (σ:ℝ) :ℕ →ℝ × Slot :=fun i=> (C i/channel σ i,flag i)
private def curve (C:Lights ℕ)(G:Gauge) (σ:ℝ): PathData G:= ⟨fun _=> plate C σ,ringT σ (0:Cameo G 1),ringT σ (0:Cameo G 2),ringT σ (0:Cameo G 3)⟩
private lemma starch (C:Lights ℕ){σ μ:ℝ}(h:μ<σ): SumBudget (fun i=> |(plate C σ i).1| * Real.exp (μ*(plate C σ i).2.length)) (‖C‖*∑' i,channel (μ-σ) i):=by
     let f(i:ℕ):= channel (μ-σ) i; have hs: Summable f:=by unfold f; rw [←neg_sub]; exact coins (sub_pos.mpr h)
     apply Work.F08.budget_minor (g:=fun i=>‖C‖*f i)
     · exact ⟨fun i=> mul_nonneg (norm_nonneg _) (Real.exp_pos _).le,hs.mul_left _,le_of_eq (tsum_mul_left ..)⟩
     · intro i; positivity
     intro i; change |C i/channel σ i| *Real.exp (μ*(flag i).length)≤ _; unfold f channel; rw [abs_div,abs_of_pos (Real.exp_pos _), sub_mul,Real.exp_sub]; calc
       _ = ‖C i‖ * _ := by rw [Real.norm_eq_abs]; ring
       _ ≤ _:= mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm (by norm_num) C i) (div_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)  
private lemma straight (U:Config G n)(p:Face (Per n)){σ:ℝ}(he:0<σ): ∃ S:Lights ℕ→L[ℝ] G.Color,∀ C, S C=(curve C G σ).ell U p:=by
    let f (C:Lights ℕ) i:= (curve C G σ).ellTerms p i U
    let K:ℝ:=∑' i,channel (0-σ) i
    have hf C :SumBudget (fun i=> ‖f C i‖) (‖C‖*K*2):=by
       let L(i:ℕ):= |C i /channel σ i|
       have H: SumBudget L (‖C‖*K):=by simpa only [plate,zero_mul, Real.exp_zero,mul_one] using starch C he
       refine Work.F08.budget_minor (g:=fun i=> L i*2) ⟨fun i=>by unfold L; positivity,H.2.1.mul_right _,by rw [tsum_mul_right]; gcongr; exact H.2.2⟩ (fun i=>norm_nonneg _) (fun i=>?_)
       change ‖(C i/channel σ i) • (flag i|>.atSite U p.1)‖≤ _; rw [norm_smul]; exact mul_le_mul_of_nonneg_left (Slot.eval_norm ..) (abs_nonneg _)
    let S:Lights ℕ→ₗ[ℝ] G.Color:={ toFun:=fun C=>∑' i,f C i,
                                    map_add':=fun C D=>by
                                         rw [← (hf C).2.1.of_norm.tsum_add (hf D).2.1.of_norm]; apply tsum_congr; intro i; simp [f,PathData.ellTerms,curve,plate,add_div,add_smul],
                                    map_smul':=fun c C=>by
                                         rw [← (hf C).2.1.of_norm.tsum_const_smul]; refine tsum_congr fun i=>?_ ; simp [f,PathData.ellTerms,curve,plate,mul_div_assoc,smul_smul] }
    refine ⟨S.mkContinuous (K*2) (fun C=> (norm_tsum_le_tsum_norm (hf C).2.1).trans ((hf C).2.2.trans_eq (by ring))), fun C=>rfl⟩
private lemma climb (f:ℕ→ℝ×Slot)(h:∀ i,(f i).2=flag i){σ b:ℝ}(hf:SumBudget (fun i=> |(f i).1| * Real.exp (σ*(f i).2.length)) b): ∃ g:Lights ℕ, f=plate g σ ∧ ‖g‖≤ b :=by
    let k(i:ℕ):= (f i).1 * channel σ i
    have hp: SumBudget (fun i=> ‖k i‖) b:= by
          unfold k; simpa only [norm_mul,Real.norm_eq_abs,channel,abs_of_pos (Real.exp_pos _),h] using hf
    have hm S : ∑ i∈ S, ‖k i‖ ≤ b:= (hp.2.1.sum_le_tsum _ (fun i _=>hp.1 i)).trans hp.2.2
    have hh: 0≤ b:=by simpa using hm ∅
    obtain ⟨g,hv,hC⟩:= flashes k (b:=b) (fun S=> by
         calc
          _ ≤ ∑ i∈ S, ‖k i‖*b:= Finset.sum_le_sum fun i hi=> by rw [sq]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); simpa using hm {i}
          _ ≤ _:=by rw [←Finset.sum_mul,sq]; gcongr; exact hm S) hh
    refine ⟨g,funext fun i=> Prod.ext ?_ (h i),hC⟩
    change _= g i/channel σ i; rw [hv]; exact (mul_div_cancel_right₀ _ (Real.exp_pos _).ne').symm
structure Drive (R :ℕ→ PathData G)(Q :PathData G)(w B:ℝ):Prop where
    wage:0<w
    flit:∀ᶠ i in atTop,∀ b j,(R i |>.row b j).2=flag j
    here :∀ b j,(Q.row b j).2=flag j
    ink (b i): Tendsto (fun j=>(R j|>.row b i).1) atTop (𝓝 (Q.row b i).1)
    sails:∀ᶠ i in atTop,∀ b, SumBudget (fun j=>|(R i |>.row b j).1| * Real.exp (w*(R i|>.row b j).2.length)) B
namespace Drive
variable {R:ℕ→ PathData G}{Q:PathData G}{w B:ℝ}(h:Drive R Q w B)
include h
lemma nib (p:PlaqAxes) : ∃ (u:ℕ→ Lights ℕ)(k:Lights ℕ), Q.row p=plate k w ∧ Gleam u k B∧ ∀ᶠ i in atTop, (R i).row p= plate (u i) w:=by
    have he :∀ᶠ i in atTop,∃ f,(R i).row p=plate f w∧ ‖f‖≤ B := (h.flit.and h.sails).mono fun i hi=>climb _ (hi.1 p) (hi.2 p)
    obtain ⟨u,hu⟩:∃ u:ℕ→ Lights ℕ,∀ᶠ i in atTop,(R i).row p=plate (u i) w ∧ ‖u i‖≤ B:=by
       obtain ⟨S,hS⟩:= eventually_atTop.mp he; choose! g hg hk using hS; exact ⟨g,(eventually_ge_atTop S).mono fun i hi=>⟨hg i hi,hk i hi⟩⟩
    let v (i:ℕ):=(Q.row p i).1* channel w i
    have H i: Tendsto (fun j=> u j i) atTop (𝓝 (v i)) :=by
       refine ((h.ink p i).mul_const _).congr' (hu.mono fun j hj=>?_); dsimp only; rw [hj.1]; exact div_mul_cancel₀ _ (Real.exp_pos _).ne'
    obtain ⟨k,hk,hB,hC⟩:= promos (hu.mono (fun _ hh=>hh.2)) H
    refine ⟨u,k,funext fun i=>Prod.ext ?_ (h.here p i),hC,hu.mono (fun _ hh=> hh.1)⟩; change _=k i/channel w i; rw [hk]; exact (mul_div_cancel_right₀ _ (Real.exp_pos _).ne').symm
lemma funds (x:PlaqAxes) : SumBudget (fun i=>|(Q.row x i).1| * Real.exp (w*(Q.row x i).2.length)) B:=by
    let f(i:ℕ):=|(Q.row x i).1| * Real.exp (w*(Q.row x i).2.length)
    have hm i:Tendsto (fun n=>|(R n|>.row x i).1| * Real.exp (w*(R n|>.row x i).2.length)) atTop (𝓝 (f i)) :=by
         refine ((h.ink x i).abs.mul_const _).congr' (h.flit.mono fun n hn=>?_); dsimp only; rw [h.here,hn]
    have hp i:0 ≤ f i:=by unfold f; positivity
    have hu (s:Finset ℕ): ∑ i∈s, f i≤ B:=le_of_tendsto (tendsto_finsetSum _ (fun i _=> hm i)) (h.sails.mono fun n hn=> ((hn x).2.1.sum_le_tsum s (fun i _=> (hn x).1 i)).trans (hn x).2.2)
    exact ⟨hp,summable_of_sum_le hp hu, Real.tsum_le_of_sum_le hp hu⟩
open WilsonStartup.Change.Reading
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
omit h in
private lemma adjust (p:Face (Per n))(W Q:PathData G)(h: Q.row p.2=W.row p.2)(U:Config G n) : Q.ell U p=W.ell U p:=by unfold PathData.ell; simp only [PathData.ellTerms,h]
lemma summons (p:Face (Per n))(U:X→ Config G n)(hx:∀ i,ContDiffAt ℝ ω (fun x=>G.mat (U x i)) 0):
     View (fun i x=> (R i).ell (U x) p) (fun x=>Q.ell (U x) p) 0 0 :=by
    obtain ⟨u,v,hv,hU,H⟩:=h.nib p.2
    let f (P:PathData G)(x:X):= P.ell (U x) p; let g(C:Lights ℕ):= f (curve C G w)
    have he C:AnalyticAt ℝ (g C) 0:= (Work.F02.pureRow (b:=curve C G w) (p:=p) (show 0 < w/2 from half_pos h.wage) (starch _ (half_lt_self h.wage)) hx).analyticAt
    have ht j (q:Lights ℕ):g q j=f (curve q G w) j:=rfl
    have hh :View (g ∘ u) (g v) (fun _=>0) 0:=by
        choose S hs using Tralis.starlight (f:=g) (fun x=> straight _ p h.wage) he; refine ⟨Eventually.of_forall fun i=> (he (u i)).contDiffAt,(he v).contDiffAt,fun i=> ?_⟩
        simp_rw [← hs,Function.comp_apply, ← hs]; exact hU.vectors (S i)
    exact hh.ferry (Eventually.of_forall fun x=> (adjust p (curve v G w) Q hv (U x)).symm) (H.mono fun i h=>Eventually.of_forall fun x=> (adjust p (curve (u i) G w) _ h _).symm)
end Drive
end YM.Stationary.Beacon
