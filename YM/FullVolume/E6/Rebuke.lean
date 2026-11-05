import YM.FullVolume.E6.Lock
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
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
-- common shape along tests. Φ notation p.Kindstation worn. spunky proof both.
variable {Υ:ℕ→ Draft F G} {V:ℕ→ Config G c}
variable [FiniteDimensional ℝ E] {M:Bank}(I:Depot Q o x μ L C₀ K) (T:Depot Q o x μ L C₀ H){χ: Chi}(R:∀ n, Station M χ (I n) j)(P':∀ n,Station M χ (T n) j)
namespace Draft
section ulfa
variable (hz:Z.Paid Q o x)(hχ:Z.χ=χ)(h:Finish J K H)(hf:∀ᶠ i in (J:Filter ℕ), Z.Viable (U i p))(ht:∀ᶠ i in (J:Filter ℕ), Mode (U i) p j M.v)
include I T R P' hz hχ h hf ht
set_option quotPrecheck false
local notation "D"=> fun n=> Z.paints (K n) (U n p)
local notation "D'"=>fun n=> Z.paints (H n) (U n p)
lemma deployed (w:Air f G)(X:Finset (Bond f))(i:Molecule S): Frill J j p (fun n y=> recoil X (D n) (U n y) M.A Q.table i (K n).kin W o.a Q.halo (kickback (D n) (K n).beta w)) (fun n y=> recoil X (D' n) (U n y) M.A Q.table i (H n).kin W o.a Q.halo (kickback (D' n) (H n).beta w)) :=by
    let d(n:ℕ):= kickback (D n) (K n).beta w; let d' n:= kickback (D' n) (H n).beta w; let u n:= (D n).atmos w
    have hv i: worldZ (D i) (K i|>.kin.beta) (d i)=u i:= kickback_home _ (I i).laws.intake.positive _; have hv' i:worldZ (D' i) (H i|>.kin.beta) (d' i)=u i:= kickback_home _ (T i).laws.intake.positive _
    let g n y x:= Polar.ember (vary (D n) (U n y)) o.a (K n).kin W Q.table (steer (D n) M.A (u n) (U n y)) ((D n).input (u n)) (course (D n) M.A (K n).beta (d n) (U n y)) (own i) Q.halo x
    let g' n y x:= Polar.ember (vary (D' n) (U n y)) o.a (H n).kin W Q.table (steer (D' n) M.A (u n) (U n y)) ((D' n).input (u n)) (course (D' n) M.A (H n).beta (d' n) (U n y)) (own i) Q.halo x
    have hQ n:Promo Q o j x M.v M.B0 M.B1 Z.χ (K n).tubes:=hχ.symm ▸ (R n).fleets.bills
    let he:= (R 0).fleets.M.solid
    have hg :Frill J j p (fun n y=>∏ x∈i, g n y x) (fun n y=>∏ x∈i,g' n y x):= Frill.pears i fun b _=> hero I hQ hz h ht hf (fun n=> (D n).input (u n)) (skipperY (K:=K) (H:=H) ht he w) (sea I T hQ hz h ht hf he w) b (own i) Q.halo
    unfold recoil; refine (ship I T hQ hz h ht hf he w X).times (hg.alter ?_ ?_)
    · filter_upwards [hf,ht] with n hn hs; have hr:= (destiny I R (X:=D n) hz.1 hχ hz.2 hn hs rfl (d n) i (own i)).symm
      dsimp only at hr; rw [hv] at hr; exact hr
    filter_upwards [hf,ht] with n hn hs; have hr:= (destiny T P' (X:=D' n) hz.1 hχ hz.2 hn hs rfl (d' n) i (own i)).symm
    dsimp only at hr; rw [hv'] at hr; exact hr
end ulfa
variable (hP:∀ i,(Υ i).Paid Q o x)(hK:∀ i,(Υ i).χ=χ)(ht:∀ n,(Υ n).Viable (U n p))(hv:∀ n, Mode (U n) p j M.v)(m:Molecule S)
set_option quotPrecheck false
local notation "Y"=> fun n=> (Υ n).paints (K n) (U n p)
local notation "Y'"=>fun n=> (Υ n).paints (H n) (U n p)
variable (i:ℕ)(hi:i≤j) (he:∀ n,Healthy (Pressure.temp x) ((I 0).unionP m) (U n p))
def rite (Q:ConnectedActivityE6.Target G P)(o:Target.Order G W)(U:ℕ→ E→ Config G c)(p:E)(X:∀ n,Coat (K n).tubes F)(D: Finset (Bond f))(d:ℝ)(m:Molecule S)(i:ℕ) : Lumen F G (Tensor.T E ℝ i):=fun n y=> Blaze.JetF (fun v=> rhythm D (X n) (U n v) d Q.table m (K n).kin W o.a Q.halo) i p y -- name
local notation "X"=> edgesM S ((I 0).unionP m) (radiusB x)
local notation "r"=>rite Q o U p Y X M.A m i
local notation "r'"=>rite Q o U p Y' X M.A m i
include I R hP hK ht hv i hi
lemma gospel (n):
    let v:= (F.order G).prod (Y n).dice
    Integrable (r n) v ∧ (iteratedFDeriv ℝ i (fun y=> bars (podium S G ((I 0).unionP m) (radiusB x)) (vary (Y n) (U n y)) m (K n).kin Q.table W o.a Q.halo) p)=∫ y,r n y ∂v:=by
    let h:=(R n).fleets.M; have ha:=(h.rays F (Y n) (hP n).1 (hP n).2 (hK n) (ht n) E (U n) p rfl (hv n)).1
    have hx:=(boosts (I n) (hP n).1 («X»:=Y n) (ht n) (hP n).2 ha h.solid h.grants m X).1.calls.2 i hi; refine ⟨hx.1,?_⟩
    exact (((chutes («X»:=Y n) (I n) (hP n).1 (ht n) (hP n).2 ha h.solid h.grants m).iteratedFDeriv ℝ i).self_of_nhds).trans hx.2
include he
lemma titled (h:Sweep K): Peaking (Y) (r):=by
    obtain ⟨q,hQ⟩:= coined M I R h; have hk:= (hQ.silver.climb (show 0 ≤ (2:ℝ)^j by positivity)).arbitrary; obtain ⟨C,hC⟩:= hk.bound
    have hs: 0≤C :=budget_nonneg (hC 0); have hD:0≤M.p:= (R 0).fleets.M.pos
    refine ⟨fun n=>(gospel I R hP hK ht hv m i hi n).1, ⟨X,M.K*j,(C*(M.p+2)^j),by positivity,fun n u w=>?_⟩⟩
    have hr:= (waving I R (hP n).1 («X»:=Y n) (hK n) (hP n).2 (ht n) (hv n) rfl (u,w) X m hQ (he n)).order i hi; simp only [one_mul,one_pow, mul_one] at hr
    refine le_trans hr ?_; let D:= facescale X w; have hx:1≤D:= (Flux.expenses ..).1; have hy:D^M.K≥1:= one_le_pow₀ hx; change salaries j m n q*(1+(M.p*D^M.K+1))^j ≤ _ * D^(M.K*j); apply le_trans _ (le_of_eq (a:= C*((M.p+2)*D^M.K)^j) ?_); swap
    · rw [mul_pow, pow_mul, mul_assoc]; -- closes
    exact mul_le_mul (budget_single (hC n) m) (pow_le_pow_left₀ (by positivity) (by linarith only [hy]) _) (by positivity) hs
include T P'
lemma verse (h:Sweep K)(hp:Sweep H)(hW:Mirror K H): Tendsto (fun n=> iteratedFDeriv ℝ i (fun v=> bars (podium S G ((I 0).unionP m) (radiusB x)) (vary (Y n) (U n v)) m (K n).kin Q.table W o.a Q.halo) p - iteratedFDeriv ℝ i (fun v=>bars (podium S G ((T 0).unionP m) (radiusB x)) (vary (Y' n) (U n v)) m (H n).kin Q.table W o.a Q.halo) p) atTop (𝓝 0):=by
    have he' n:Healthy (Pressure.temp x) ((T 0).unionP m) (U n p):=he n
    have hh y w:Tendsto (fun n=> footZ (Y) (r) n y w - footZ (Y') (r') n y w) atTop (𝓝 0):=by -- name replacement
        refine (tendsto_iff_ultrafilter ..).mpr fun J hj=> ?_; obtain ⟨Z,hz,hχ,HZ⟩:= frozen_budget (J:=J) y hP hK
        have hV: ∀ᶠ i in (J:Filter ℕ), Z.Viable (U i p):= HZ.mono fun n hn=> hn ▸ (show (amendment (Υ n) y).Viable (U n p) from ht n)
        have hΨ:= takes I R hz hχ (hW _ hj) hV w
        have hk':= (deployed I T R P' hz hχ (hW _ hj) hV (Eventually.of_forall hv) w X m).feel i hi
        refine (hΨ.prods hk' (Q:=fun x y=>x • y) continuous_smul).shrank.congr' (HZ.mono fun n hn=> ?_)
        dsimp only [footZ]; rw [← hn]; rfl
    exact (Peaking.stack I T (titled I R hP hK ht hv m i hi he h) (loved hP ht) (titled T P' hP hK ht hv m i hi he' hp) (loved hP ht) hh).congr' (Eventually.of_forall fun n=> congr_arg₂ (·-·) (gospel I R hP hK ht hv m i hi n).2.symm (gospel T P' hP hK ht hv m i hi n).2.symm)
end Draft
end YM.ConnectedActivityE6.Lim
