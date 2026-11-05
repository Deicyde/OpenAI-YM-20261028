import YM.MergeProof.Badlands
import YM.MergeProof.North.Palate
import YM.MergeProof.Revenue
import YM.Next.RANK.HomeSync
import YM.Next.RANK.SealMix
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Comparison
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Hybrid
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Marginal

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {X : Targets s K} {D : Rolls s} {Θ : Protection D} {p : Expenses X} {u : Return.Wages} {l : ℕ→ℝ} {P : Teller G}
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe
open MergeProof.Ribbons Graces
section
variable (Q:ConnectedActivityE6.Target G P)(μ:ℝ)(L:Side)(Z:Stage)(N d:ℕ)
def Hymen (x:ℝ) : Prop:=
    let a:= radiusB x; let e:= betaF G x L; let b:= Salt.scent a N (Z.supportExponent+1/2) 1 (probe e) 1 (straw μ L G x)
    ((a+a+1:ℕ):ℝ)^4*b≤1/2 ∧ Real.exp b-1 ≤ 1∧ straw μ L G x≤1 ∧
        (Z.supportExponent+1/2)*(((2*(1024*a)+1)^4:ℕ):ℝ) ≤ Real.sqrt e ∧
        (coinFee G Z d L+|2*((L).val:ℝ)^d*(Mercury.volt x Z.order Z.power*((Q).goal L x)⁻¹)|)* Graces.host G Z d≤ Real.exp (Real.sqrt e)
lemma chant {f:ℝ→ℝ}{v:ℝ}(hf:Rate G L v f):∀ᶠ x in atTop,f x ≤ Real.exp (Real.sqrt (betaF G x L)):=by
   let M : ℝ:=v+1; let a:ℝ:=1/2
   have ha:0<a:=by norm_num [a]
   have h:= (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (M/a) 1 zero_lt_one).comp ((tendsto_rpow_atTop ha).comp (Work.E09.betaF_growth G L))
   filter_upwards [hf M (lt_add_one _), Delay.shift_pos G L,h.eventually (ge_mem_nhds zero_lt_one)] with x hx hp h
   rw [Real.sqrt_eq_rpow]
   let b:= betaF G x L
   change (b^a)^(M/a)*Real.exp (-1*b^a) ≤ 1 at h; rw [← Real.rpow_mul hp.le, mul_div_cancel₀ _ ha.ne',neg_one_mul, Real.exp_neg,← div_eq_mul_inv] at h; exact (le_abs_self _).trans (hx.trans ((div_le_one (Real.exp_pos _)).mp h))
lemma shopping (h:0<μ) : ∀ᶠ x in atTop,Hymen Q μ L Z N d x:=by
   let A:=radiusB; let t:=straw μ L G; let a x:= probe (betaF G x L); let y x:= Salt.scent (A x) N (Z.supportExponent+1/2) 1 (a x) 1 (t x)
   have hy:Rate G L (-2) a:= Rate.power
   have ht:Rate G L (-2) t:=infuso _ _ _ _ (by exact div_pos h (by norm_num)) (by norm_num) _
   have hZ:Rate G L (-2) y:= ((hy.mul_left _|>.mul_right _).add (hy.mul_left _|>.mul_right _)).add (ht.mul_left _)
   have hu: Rate G L (-2) (fun x=>((A x+A x+1:ℕ):ℝ)^4*y x):= by
      have hx:=Rate.radius_price (L:=L) (G:=G); simpa only [zero_mul,zero_add,Nat.cast_add,Nat.cast_one] using! ((((hx.add hx).add (Rate.const 1)).pow 4).mul hZ)
   have hr: Rate G L 0 fun x=> (Z.supportExponent+1/2)*(((2*(1024*A x)+1)^4:ℕ):ℝ):=by
      have hx:=Rate.radius_price (L:=L) (G:=G); simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat]; exact ((((((hx.mul_left 1024).mul_left 2).add (Rate.const 1)).pow 4).weaken (by norm_num)).mul_left _)
   let f x:=2*(L.val:ℝ)^d*(Mercury.volt x Z.order Z.power*((Q).goal L x)⁻¹)
   have hf: Rate G L (max 0 (-Q.rate)) (fun x=>|f x|):= by
       have hz: Rate G L 0 shiftG:= (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
       have hp: Rate G L (-Q.rate) (fun x=> (Q.goal L x)⁻¹):=by apply Rate.congr Rate.power; filter_upwards [Delay.shift_pos G L] with x h; exact (Real.rpow_neg h.le _).symm
       have hh: Rate G L (-Q.rate) f:= ((((hz.pow (Z.power*Z.order)).weaken (b:=0) (by simp)).mul_right _|>.mul hp).mul_left _|>.weaken (by linarith)); exact (hh.compare (v:=fun x=>|f x|) (by filter_upwards with x; rw [abs_abs])).weaken (le_max_right ..)
   have hg:0<Real.log 2:=Real.log_pos (by norm_num)
   filter_upwards [hu.below (by norm_num) (1/2) (by norm_num),hZ.below (by norm_num) _ hg,ht.below (by norm_num) 1 one_pos,hr (1/2) (by norm_num),chant L (((Rate.const (coinFee G Z d L)).weaken (le_max_left ..)|>.add hf).mul_right (host G Z d))] with x hx ho hd he ha
   refine ⟨(le_abs_self _).trans hx,?_,(le_abs_self _).trans hd,(le_abs_self _).trans (he.trans_eq (Real.sqrt_eq_rpow _).symm),ha⟩
   change Real.exp (y x)-1 ≤1
   have h:Real.exp (y x) ≤ 2:= (Real.exp_monotone ((le_abs_self _).trans ho)).trans_eq (Real.exp_log (by norm_num)); linarith
end
variable (R:Register D p u l) (Q:ℕ→ℕ)
def AccordV (T:Delays Θ) : Prop:=∀ j x,T.betaEntry j≤ x →∀ i,StepStages j i→∀ d ≤ i, Hymen (X j i) (R.μ j i) (D.L j) (s.profile i) (Q j) d x
lemma swelling (T:Delays Θ) :∃ U: Delays Θ, DelayLe T U∧∀ V:Delays Θ,DelayLe U V → AccordV R Q V:=by
   obtain ⟨u,-,hv,H⟩:=collect_upper T.betaEntry _ (fun j=> eventually_transitions j _ _ (fun i h=> ((Finset.range (i+1)).eventually_all.mpr (fun d hd=> shopping (X j i) _ (D.L j) (s.profile i) (Q j) d (R.consumes _ _ h|>.2.1)))))
   exact ⟨{T with betaEntry:=u},⟨hv,le_rfl,le_rfl,le_rfl⟩, fun _ hz j x hx i hi d hd=> H j x ((hz.beta j).trans hx) i hi d (Finset.mem_range.mpr (by omega))⟩
-- pre-L demand for exp-base
variable (s)
lemma harpo (U: ℕ→ℕ→ℕ) :∃ n:ℕ→ℕ,∀ v≥n,∀ P:Rolls (ThroughLaunch.raise s v),∀ i j,StepStages i j→Real.exp (Release.base ((s.profile j).supportExponent+2) (U i j)) ≤ (P.L i).val:=by
   let f i j := Nat.ceil (Real.exp (Release.base ((s.profile j).supportExponent+2) (U i j)))
   refine ⟨fun i=> ((Finset.range (i+1)).sup (f i)),fun v hv P i j h=>?_⟩
   refine (Nat.le_ceil _).trans ?_; exact_mod_cast (le_trans (Finset.le_sup (f:=f i) (Finset.mem_range.mpr (Nat.lt_add_one_iff.mpr h.1))) ((hv i).trans (P.large i).need))
end YM.PhysicalNext.Repeat.Mallow
