import YM.UVExtension.Wet.Stroll
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wet
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady PhysicalNext.Repeat Lotus
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
open Strata Strata.Polish Matrix MeasureTheory WithLp Shield
open Span Oriented Vine
variable {H:∀ i,Cash w s q L Q U C (T i) (R i)} {A b N r d f' Z:ℝ} (p: Span.Score v T H k l χ A b u B N r d f' V Z)
open Polar Silica Shield Score Flux Matter
open Stained Eider
variable {D : (i:ι)→ Lotus.Leaf (R i)} (hz:Constant (v:=v) D)
variable [NeBot v](hu:0≤u)(qV:StableR v R)
variable {t:κ→Bool→ι}(h:∀ b,Tendsto (fun n=> t n b) qq v)[qq.IsCountablyGenerated]
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {τ:κ→ E} {Y:κ→ E→ Config G c}
variable {F:Forest S.ratio} (M:κ→ Hat G F)
variable (he:∀ i,Mode (Y i) (τ i) k u)(hK:∀ i,(M i).legal s ∧ Y i (τ i)=(M i).bill)
variable (V':Air f G→ℝ)(P:ι→ Molecule S→ℝ)(hV: Roast (D:=D) (v:=v) (H:=H) (χ:=χ) (k:=k) (u:=u) (A:=A) V' P)
structure Elegy (f:ι→Molecule S→ℝ):Prop where
   swift: Swift v f
   laws: ∀ᶠ i in v,∀ j: Molecule S,∀ (F:Forest S.ratio)(X: Coat (T i) F), X.x=s→ X.width=U.K → X.χ=χ→ |(D i).bloom X w U.a Q.table Q.halo j| ≤ f i j ∧∀ (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](V:E→ Config G c) (x:E), (roster j).flags=∅ → Healthy (temp X.x) ((H i).unionP j) X.V → V x=X.V → Mode V x k u → Brush k (f i j) 1 (fun z=> (D i).picture (vary X (V z)) j w U.a Q.table Q.halo) x
-- MEasured self bounded by Z Crystal
include p hu qV hz
set_option maxHeartbeats 600000 in
lemma arrest : ∃ f, Elegy (D:=D) (v:=v) (H:=H) (χ:=χ) (k:=k) (u:=u) f :=by
   obtain ⟨P,W,K⟩:= cameo p hu qV hz
   let d:=∫ i,P i; have hd: 0≤d:=integral_nonneg K.positive
   obtain ⟨k',hk⟩:= K.receipt.books; let vF n i:= d*W n i; refine ⟨vF,K.receipt.scales d hd,?_⟩
   filter_upwards [hk,K.uv] with n hn hs j F X hX hW hχ
   let R' := R n; let X':= planted X j; let Q':= H n; let U'(i:S.Choices):= X'.taggedL i
   let Λ:ℝ:= W n j; let B:=Λ*d; let m:ℝ:= Fintype.card S.Choices; have hm :0< m:=by unfold m; positivity
   have he:vF n j=B:=mul_comm ..; rw [he]; have hh :0≤ B:= mul_nonneg (hn.1 _) hd
   have hz l:= (hs F (U' l) hX hW (planted_valid ..) hχ j)
   let μ:=(F.order G).prod (volume (α:=Air f G)) -- f shadow
   have ht {W:Type}[NormedAddCommGroup W][NormedSpace ℝ W] (l)(g:F.Slice G × Air f G→ W)(hp: Integrable g ((F.order G).prod (U' l).dice))(he:∀ x, ‖shiftV (R:=R) n (U' l) g x‖≤ Λ *P x.2) : ‖∫ i,g i ∂((F.order G).prod (U' l).dice)‖≤B:=by
       obtain ⟨hx,hT⟩:= pedals p n (U' l) hX hW (planted_valid ..) g hp; rw [hT]
       have hp :Integrable (fun i:F.Slice G × Air f G=> Λ*P i.2) μ:= (K.employs.comp_snd _).const_mul _
       exact (norm_integral_le_integral_norm _).trans ((integral_mono hx.norm hp he).trans_eq (by rw [MeasureTheory.integral_prod _ hp]; simp_rw [MeasureTheory.integral_const_mul]; rw [integral_const]; simp only [probReal_univ,one_smul]; rfl))
   let J:=podium S G ((H n).unionP j) (radiusB s)
   constructor
   · unfold Leaf.bloom; split
     · unfold Leaf.steep likely; rw [abs_mul]
       apply le_trans (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs ..) (abs_nonneg _)); apply le_trans (mul_le_mul_of_nonneg_left (sum_le_sum (g:=fun _=> B) (fun i _=> ht i _ ((D n).tip (U' i) (own j) (show Cash w X.x q L Q U C (T n) (R n) from hX.symm ▸ H n) hW (planted_valid ..) j|>.2.1) ((hz i).1 (own j)))) (abs_nonneg _)); rw [Finset.sum_const,nsmul_eq_mul,card_univ]; change |m⁻¹| *(m* B)≤_; rw [abs_of_pos (inv_pos.mpr hm),inv_mul_cancel_left₀ hm.ne']
     rw [abs_zero]; exact hh
   intro E _ _ _ V x hK hp hh' hV; have hy : Healthy (temp s) ((H n).unionP j) X.V:=hX ▸ hp -- h shadow
   refine Brush.shimmy ?_ (drove p n X V x j hX hW hχ hV hh' hK hy)
   split; swap; exact Brush.zi EventuallyEq.rfl hh zero_le_one
   let j' z y:=(spruce (D:=D) (A:=A) (H:=H) n X V j z y)
   have hr(z):Brush k B 1 (j' z) x:=by
       have hJ' : Cash w (U' z).x q L Q U C (T n) (R n) := hX.symm ▸ H n -- explicit C real conflict
       have hU:= ((D n).boosts (U' z) j hJ' hW (planted_valid X j) (edgesM S ((H n).unionP j) (radiusB s)) ((p.realm.granted _ _ _ (T n) (R n) _ (H n) (p.rails _) rfl).2 E V F (U' z) x hX hχ hW (planted_valid ..) hh' hV).1 p.realm.bay (by rw [show (U' z).x=s from hX,(H n).laws.data.funds.length_eq]; exact p.realm.foot)|>.1).calls
       refine ⟨hU.1,zero_le_one,fun i hi=> ?_⟩; change ‖iteratedFDeriv ℝ i _ x‖≤_; rw [one_pow,mul_one, show iteratedFDeriv ℝ i (j' z) x =_ from (hU.2 i hi).2]; exact ht z _ ((hU.2 i hi).1) ((hz z).2 E x V hh' hp hV (edgesM S ((H n).unionP j) (radiusB s)) i hi)
   refine ((Brush.spree Finset.univ j' _ zero_le_one (fun i _=>hr i)).smul m⁻¹).climb ?_ le_rfl
   rw [sum_const,nsmul_eq_mul,card_univ,Real.norm_of_nonneg (inv_pos.mpr hm).le, inv_mul_cancel_left₀ hm.ne' B]
end YM.UVExtension.Wet
