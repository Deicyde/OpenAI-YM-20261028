import YM.FullVolume.Umbra.Pound
import YM.FullVolume.Umbra.Rise
-- one real mark among any two epoch carpets at the same stamp
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
namespace Umbra
open Lotus
open Draft
variable {Υ:ℕ→ Draft F G} {V:ℕ→ Config G c} {M:Bank}(I:Depot Q o x μ L C₀ K) (T:Depot Q o x μ L C₀ H){χ: Chi}(R:∀ n, Station M χ (I n) j)(P':∀ n,Station M χ (T n) j)
variable {F₀:BatchK K} {F₁:BatchK H}{δ δ':ℕ→ Molecule S→ℝ}{Δ Δ':ℕ} (h:Seats I (F₀:=F₀) (χ:=χ) (M:=M) (j:=j) δ Δ) (hq: Seats T (F₀:=F₁) (χ:=χ) (M:=M) (j:=j) δ' Δ') {k:Wing}(hm:Rhyme F₀ F₁ k)(hM:Mirror K H)(hJ:(J:Filter ℕ)≤ atTop) (m:Molecule S)
set_option quotPrecheck false
include h I R
section force
variable (hv:∀ n,(Υ n).Paid Q o x)(hc:∀ n,(Υ n).χ=χ)(hk:∀ n,(Υ n).Viable (V n))
local notation "D"=> fun n=> (Υ n).paints (K n) (V n)
local notation "D'"=>fun n=> (Υ n).paints (H n) (V n)
include hv hc hk
lemma nail: Peaking D (fun n=> (F₀ n).into (D n) W o.a Q.table (own m) Q.halo m):=by
    obtain ⟨b,hb⟩:= h.bud.bound
    refine ⟨fun n=>?_ ,∅,0,b,budget_nonneg (hb 0),fun n y z=>?_⟩
    · have H': Cash W (D n|>.x) μ L Q o C₀ (K n).tubes (K n).kin:= (show (D n|>.x)=x from (hv n).1).symm ▸ (I n); exact ((F₀ n).tip (D n) _ H' (hv n).2 (hk n) m).2.1
    rw [pow_zero,mul_one]; exact (h.window n F (D n) (hk n) (hv n).1 (hv n).2 (hc n) m _).trans (budget_single (hb n) m)
include T P' hm hM hq
lemma bornT : Tendsto (fun n=> (F₀ n).tithe (D n) (own m) W o.a Q.table Q.halo m- (F₁ n).tithe (D' n) (own m) W o.a Q.table Q.halo m) atTop (𝓝 0):=by
   refine Peaking.stack I T (nail I R h m hv hc hk) (loved hv hk) (nail T P' hq m hv hc hk) (loved hv hk) ?_; intro y w
   refine (tendsto_iff_ultrafilter ..).mpr fun J hj=>?_
   obtain ⟨Z,hA,hQ,HZ⟩:=frozen_budget (J:=J) y hv hc
   have he: ∀ᶠ i in (J:Filter ℕ),Z.Viable (V i):= HZ.mono fun i hi=> hi ▸ (show (amendment (Υ i) y).Viable (V i) from hk i)
   refine (camp I T R P' hm hj (hM J hj) hA hQ he w m).shrank.congr' (HZ.mono fun n hn=>?_); dsimp only [footZ]; rw [←hn];rfl
end force
variable [FiniteDimensional ℝ E]
variable (hv:∀ n,(Υ n).Paid Q o x)(hc:∀ n,(Υ n).χ=χ)(hk: ∀ n,(Υ n).Viable (U n p))(ht:∀ n,Mode (U n) p j M.v) (he:∀ n,Healthy (Pressure.temp x) ((I 0).unionP m) (U n p)) (i:ℕ) (hi:i ≤ j)
local notation "Y"=> fun n=> (Υ n).paints (K n) (U n p)
local notation "Y'"=>fun n=> (Υ n).paints (H n) (U n p)
local notation "D₀" => edgesM S ((I 0).unionP m) (radiusB x)
local notation "X"=>fun n=> Blaze.JetF (fun v=> (F₀ n).carat D₀ (Y n) (U n v) M.A Q.table m W o.a Q.halo) i p
local notation "X'"=>fun n=> Blaze.JetF (fun v=> (F₁ n).carat (edgesM S ((T 0).unionP m) (radiusB x)) (Y' n) (U n v) M.A Q.table m W o.a Q.halo) i p
local notation "s"=>podium S G ((I 0).unionP m) (radiusB x)
local notation "v"=> fun n z=>(F₀ n).cinema (vary (Y n) (U n z)) m W o.a Q.table Q.halo s
local notation "w"=>fun n z=> (F₁ n).cinema (vary (Y' n) (U n z)) m W o.a Q.table Q.halo (podium S G ((T 0).unionP m) (radiusB x))
include ht hv hc hk hi
lemma globe (n:ℕ): Integrable (X n) ((F.order G).prod (Y n).dice) ∧ iteratedFDeriv ℝ i (v n) p=∫ x,X n x ∂((F.order G).prod (Y n).dice):=by
   obtain ⟨H,hp⟩:= h.journal I R (i:=m) n (Y n) (hv n).1 (hv n).2 (hc n) (hk n) _ p (ht n) rfl
   obtain ⟨hh,hX⟩:= H.calls.2 i hi; exact ⟨hh, ((hp.iteratedFDeriv ℝ i).self_of_nhds).trans hX⟩
include he
lemma dawn : Peaking Y X:=by
   obtain ⟨d,hd⟩:= h.bud.bound; refine ⟨fun n=>(globe I R h m hv hc hk ht i hi n).1,D₀,Δ,d,budget_nonneg (hd 0),fun n u b=>?_⟩
   have hr:=(h.gaze n F (Y n) (hv n).1 (hv n).2 (hc n) (hk n) m (he n) E _ p (ht n) rfl (u,b) D₀).order i hi; rw [one_pow, mul_one] at hr; have hx:1≤ facescale D₀ b:=(Flux.expenses ..).1; exact hr.trans (mul_le_mul_of_nonneg_right (budget_single (hd _) m) (by positivity))
include hM hm T hq P'
lemma vantage : Tendsto (fun n=> iteratedFDeriv ℝ i (v n) p - iteratedFDeriv ℝ i (w n) p) atTop (𝓝 0) :=by
   have he' n: Healthy (Pressure.temp x) ((T 0).unionP m) (U n p):= he n
   have hX r t:Tendsto (fun n=> footZ Y X n r t-footZ Y' X' n r t) atTop (𝓝 0):=by
       refine (tendsto_iff_ultrafilter ..).mpr fun J hj=>?_ ; obtain ⟨Z,hA,hψ,HZ⟩:= frozen_budget (J:=J) r hv hc
       have hY:∀ᶠ i in (J:Filter ℕ), Z.Viable (U i p):= HZ.mono fun n hn=> hn ▸ (show (amendment (Υ n) r).Viable (U n p) from hk n)
       have hr:=takes I R hA hψ (hM _ hj) hY t; have hp:= (beauty I T R P' hm hj (hM _ hj) hA hψ hY (Eventually.of_forall ht) t D₀ m).feel i hi
       refine (hr.prods hp (Q:=fun x y=>x • y) continuous_smul).shrank.congr' (HZ.mono fun n hn=>?_); dsimp only [footZ]; rw [←hn];rfl
   exact (Peaking.stack I T (dawn I R h m hv hc hk ht he i hi) (loved hv hk) (dawn T P' hq m hv hc hk ht he' i hi) (loved hv hk) hX).congr' (Eventually.of_forall fun n=>congr_arg₂ (· - ·) (globe I R h m hv hc hk ht i hi n).2.symm (globe T P' hq m hv hc hk ht i hi n).2.symm)
omit hi i in
include hJ in
lemma plume : Frill J j p v w:=by
   obtain ⟨X₁,hX,hY⟩:= h.opal I R; obtain ⟨X₂,-,hV⟩:= hq.opal T P'; obtain ⟨b,hb⟩:= hX.bound
   have hx : Frill J j p v v:= glance («v»:=b) (a:=1) (Eventually.of_forall fun n=> (hY n F (Y n) (hv n).1 (hv n).2 (hc n) (hk n) m (he n) E _ p (ht n) rfl).climb (budget_single (hb n) _) le_rfl)
   exact ⟨hx.seer, Eventually.of_forall fun n=>(hV n F (Y' n) (hv n).1 (hv n).2 (hc n) (hk n) m (he n) E _ p (ht n) rfl).smooth, fun i hi=> (hx.feel i hi).time ((vantage I T R P' h hq hm hM m hv hc hk ht he i hi).mono_left hJ)⟩
end Umbra
end YM.ConnectedActivityE6.Lim
