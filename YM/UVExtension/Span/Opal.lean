import YM.UVExtension.Span.Nexus
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Span
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
namespace Score
open Oriented Vine Concerted
variable {H:∀ i,Cash w s q L Q U C (T i) (R i)} {A b N r d f' Z:ℝ} (p: Score v T H k l χ A b u B N r d f' V Z)
variable {t:κ→Bool→ι}(h:∀ b,Tendsto (fun n=> t n b) qq v)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {τ:κ→ E} {Y:κ→ E→ Config G c}
variable {F:Forest S.ratio} {M:κ→ Hat G F}
-- states use explicit
variable (he:∀ᶠ i in qq,Mode (Y i) (τ i) k u)(hK:∀ᶠ i in qq,(M i).legal s ∧ Y i (τ i)=(M i).bill)
variable (qV:StableR v R)
variable (Δ:κ→Directions G f) -- actual held displacement at test. no norm when prices all Compass later
open Silica Flux WithLp MeasureTheory
open Polar Silica Eider
-- arrows.
variable (hx : ∃ r:ℝ,∀ᶠ i in qq, ‖Δ i‖≤ r)
include h p he hK hx
def mobil (A s B:ℝ)(χ:Chi)(T:ι→ Tube G S)(t:κ→Bool→ι)(Δ:κ→ Directions G f)(M:κ→ Hat G F)(Y:κ→ E→ Config G c) := fun i b y=> steer (Abide s χ B T M t i b) A (Δ i) (Y i y)
-- keep local lets with explicit. 
-- χ smooth/gentry
omit p h he hK hx [FiniteDimensional ℝ E] in lemma clifft (a:ℝ): ContDiff ℝ (↑k : ℕ∞ω) (fun x:G.Color=> χ.innerShare a ‖x‖):=by unfold Chi.innerShare; simp_rw [div_pow]; exact (χ.smooth.of_le (by exact_mod_cast WithTop.coe_le_coe.mpr le_top)).comp ((contDiff_norm_sq ℝ).div_const _) -- χ.smooth cast
lemma pools (i:Bond f)(b:ℝ): Walt qq τ k (fun n v y=> (vary (Abide s χ U.K T M t n v) (Y n y)).cone b (mobil A s U.K χ T t Δ M Y n v y) i):=by
    have hg:= windsT p h he hK Δ hx
    exact (hg.leaf (ContinuousLinearMap.proj i)).plant (clifft (G:=G) (χ:=χ) (k:=k) (b*Pressure.fiery G s S.patch.L)) -- shouldn't hK
omit p h he hK hx [FiniteDimensional ℝ E] in
lemma caraffa (J:Finset α)(T: α→ι→Bool→ E→ℝ){x:ι→ E}(h:∀ i∈J,Walt v x k (T i)): Walt v x k (fun i b y=>∏ j∈J,T j i b y):=by
     induction J using Finset.induction_on with
     | empty=> simp only [Finset.prod_empty]; exact Walt.ready _
     | insert i s hi ih=> simp_rw [Finset.prod_insert hi]; exact (h _ (mem_insert_self ..)).times (ih (fun j hj=>h j (mem_insert_of_mem hj)))
lemma parka (b:ℝ)(L:κ→ Finset (Bond f)): Walt qq τ k (fun n v y=> (vary (Abide s χ U.K T M t n v) (Y n y)).enforce b (mobil A s U.K χ T t Δ M Y n v y) (L n)):=
    Walt.cut L _ (fun i=> (caraffa i _ (fun k (_:k∈i)=> pools p h he hK Δ hx k b)).excuse _)
include qV
lemma incidences (i : Ledger f 2): Walt qq τ k (fun n b y=> (vary (Abide s χ U.K T M t n b) (Y n y)).qunique (course (Abide s χ U.K T M t n b) A (R (t n b)).beta (prize s χ U.K T R M t Δ n b) (Y n y)) i):=by
   let X n b y:= vary (Abide s χ U.K T M t n b) (Y n y); let z n b y:= course (Abide s χ U.K T M t n b) A (R (t n b)).beta (prize s χ U.K T R M t Δ n b) (Y n y); let k':=i.1; have hZ:= p.sailsW h he hK qV Δ hx
   have hx u: Walt qq τ k (fun n b y=> z n b y u):= hZ.leaf ((LinearMap.comp (LinearMap.proj u) (WithLp.linearEquiv 2 ℝ _).toLinearMap : Air f G→ₗ[ℝ]ℝ).toContinuousLinearMap)
   have hu(l m): Walt qq τ k (fun i b y=> (X i b y).finale l m):=by unfold finale; split_ifs; exact ((p.trunks h he hK).1).leaf (-(ContinuousLinearMap.id ℝ _)); exact gram p h (M:=M) he
   let X' P n b y j:=(X n b y).finale k' (j+P)
   have hv {m}(a:Bond f)(J:Itinerary f m)(u v' : G.ColorIndex)(P:ℕ): Walt qq τ k (fun i b y=> combo a J (X' P i b y) u v'):=by
      induction m generalizing a P u with
      | zero => simp only [combo]; exact Walt.ready _
      | succ j ih=>
        simp_rw [combo,Matrix.mul_apply,Itinerary.restrict,Matrix.submatrix_apply]; apply Walt.schedule _ _; intro j hj
        let B : Mat f G →ₗ[ℝ]ℝ:= {toFun:=fun X=> X (a,u) (Itinerary.next J,j),map_add':=fun _ _=> rfl,map_smul':=fun _ _=> rfl}
        have h:= ih (Itinerary.next J) (after J) j (P+1)
        have he i b y: X' (P+1) i b y=(fun k=> X' P i b y (k+1)):= funext fun k=> by unfold X'; rw [show k+(P+1)=k+1+P by omega]
        simp_rw [he] at h; exact ((hu k' (0+P)).leaf B.toContinuousLinearMap).times h
   unfold qunique circle; dsimp only; apply (Walt.ready _).times; apply Walt.schedule _ _; intro P _; apply (hx _).times; apply Walt.schedule _ _; intro a _; exact (hv i.2.1 i.2.2 P a 0).times (hx _)
lemma pledge (j : ChainIndex f) : Walt qq τ k (fun n b y=> spins (vary (Abide s χ U.K T M t n b) (Y n y)) U.a (R (t n b)) (mobil A s U.K χ T t Δ M Y n b y) (course (Abide s χ U.K T M t n b) A (R (t n b)).beta (prize s χ U.K T R M t Δ n b) (Y n y)) j):=by
   let X i b y:=vary (Abide s χ U.K T M t i b) (Y i y); let Z n b y:= course (Abide s χ U.K T M t n b) A (R (t n b)).beta (prize s χ U.K T R M t Δ n b) (Y n y)
   have hh (u:Bond f): Walt qq τ k (fun n b y=> Polar.patch (X n b y) U.a (mobil A s U.K χ T t Δ M Y n b y) u):= Walt.choose (fun n=> (Abide s χ U.K T M t n true).Hot u) ((p.pools h he hK Δ hx u (2*U.a)).excuse _) (Walt.ready _)
   have hT:= trunks p h he hK
   rcases j with i|i|i|i|i
   · exact (stampsA p h he hK i|>.1).plant (Z:=fun x=> -x/2) (contDiff_id.neg.div_const _)
   · exact (stampsA p h he hK i|>.2).plant (Z:=fun x=> x/2) (contDiff_id.div_const _)
   · exact (stampsS p h he hK i).plant (Z:=fun x=> x/2) (contDiff_id.div_const _)
   · unfold spins; simp only [Sum.elim_inr,Sum.elim_inl]; unfold major; apply (hh _).times; apply Walt.schedule _ _; intro l _
     let B i b v:= shimmer (X i b v) (R (t i b)).beta -- explicit
     have ht: Walt qq τ k B:= ((Walt.stamp ((betP p h qV).2.continuous continuous_neg)).pay ((jetting (gram p h he (M:=M)) (p.wings h he hK)).sums (p.stakes h he hK))) -- shimmer '-(gStep β)⁻¹ • ...'
     let H:= ((LinearMap.comp (LinearMap.proj (i,l)) (WithLp.linearEquiv 2 ℝ _).toLinearMap : Air f G→ₗ[ℝ]ℝ).toContinuousLinearMap)
     exact ((p.sailsW h he hK qV Δ hx).leaf H).times (ht.leaf (ContinuousLinearMap.proj (i,l)))
   exact ((hh _).times (hh _)).times (p.incidences h he hK qV Δ hx i)
end Score
end YM.UVExtension.Span
#print axioms YM.UVExtension.Span.Score.pledge
