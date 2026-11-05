import YM.FullVolume.Relay.Summary
/-!
 # budgets in terms of denominators, stage-local currency conditions

 Define currencies exactly. All Radius params affordable in a histogram to
 be paid separately. No hidden poly estimates.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Campaign.Face
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open YM.MergeProof MergeProof.Matric FullVolume FullVolume.Paint Tower
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp Amp.Beam
open Pillars Bandage Pass Muse Contest Ovens Veil Ship
variable {R:Run G} (T:Campaign R)
set_option quotPrecheck false
local notation "L!"=> R.alloy.B.a
local notation "K!"=> R.alloy.B
open Spirit Branch Boutique Guard
open Extraction Extraction.Lease
open MergeProof.Accent FullVolume.Nectar
variable {I:Type}[Fintype I] [DecidableEq I] (d:I→ℕ)(x:(i:I)→((Labels.frames G).level (d i)).Coeff)
variable (Θ:Luna.Tableau T.width 300)(v:ℕ→ℕ→ℝ)
abbrev civic (n:ℕ):ℝ:= 128*((n:ℝ)+1)
lemma civic_pos (n:ℕ) : 0<civic n:=by unfold civic; positivity
abbrev intervalClock (R:Run G)(m:ℕ):ℝ:= ((R.alloy.B.a.S.denominator m).val:ℝ)
abbrev minutes (R:Run G)(m:ℕ):ℝ:= ((R.alloy.B.a.S.block m).val:ℝ)
abbrev fundsY (R:Run G)(b m:ℕ):ℝ:= intervalClock R m ^ b
abbrev changeA (R:Run G)(b m:ℕ):ℝ:= minutes R m ^ b
lemma one_clock (m):1 ≤ intervalClock R m:=by exact_mod_cast (R.alloy.B.a.S.denominator m).property -- >0&ge1
lemma one_minute (m):1 ≤ minutes R m:=by exact_mod_cast (R.alloy.B.a.S.block m).property
lemma one_fund(b m): 1 ≤ fundsY R b m:= one_le_pow₀ (one_clock m)
lemma one_change(b m):1 ≤ changeA R b m:= one_le_pow₀ (one_minute m)
lemma changeling(b i): fundsY R b (i+1)=fundsY R b i*changeA R b i:=by unfold fundsY changeA intervalClock minutes; rw [Schedule.denominator,PNat.mul_coe,Nat.cast_mul,mul_pow]
lemma lighter (b:ℕ) : Monotone (fundsY R b):=by apply monotone_nat_of_le_succ; intro i;rw [changeling]; exact le_mul_of_one_le_right (zero_le_one.trans (one_fund ..)) (one_change ..)
abbrev energyW (R:Run G)(b:ℕ)(m:ℕ)(_ : I):ℝ:= (fundsY R b m)⁻¹ ^ 4
abbrev kernelW (R:Run G)(b:ℕ)(j:ℕ)(_ : I):ℝ:= (fundsY R b (j+1))⁻¹ ^ 6
abbrev kernelU (R:Run G)(b:ℕ)(j m:ℕ)(_ : I):ℝ:= fundsY R b (j+1) * (fundsY R b (j+1) / fundsY R b (m+1))
abbrev timeEntry (R:Run G)(m:ℕ):ℝ:= R.alloy.B.a.clock.hatBeta m
abbrev mintOut (R:Run G)(m:ℕ):ℝ:= Accent.mintK (R.alloy.B.a.budget m).B
abbrev heightP (R:Run G)(m:ℕ): ℝ:= (timeEntry R m)⁻¹ ^ 3
abbrev creditP (x:ℝ):ℝ:= (x⁻¹)^2
variable (b m:ℕ)
-- Statement needs Calendar β wr.Runs. ask all m eventually. include full bounds for ⌕ reboot at top.Cap.Dep.Vw.
structure Economics (Θ:Luna.Tableau T.width 300)(v:ℕ→ℕ→ℝ)(d:I→ℕ)(x:(i:I)→((Labels.frames G).level (d i)).Coeff)(b m:ℕ): Prop where
   support : 8 ≤ (R.alloy.B.a.budget m).B
   expQ : 1 ≤ (R.alloy.B.a.budget m).supportExponent
   monotoneB : timeEntry R m ≤ timeEntry R (m+1)
   big : 512 ≤ timeEntry R m
   upBound : timeEntry R m ≤ fundsY R b m
   more : (changeA R b m)^4 ≤ mintOut R m
   ability : ∀ N p:ℕ, ∀ hm:m<N, ∃ a,Fund (T.L.prim N m p hm) Θ a (creditP (timeEntry R (m+1))) T.pay T.pay
   fundsE (j:I): civic (Fintype.card I)*quoteInput T m v (d j) ‖x j‖ ≤ fundsY R b (m+1)
   fundsK (j:I): civic (Fintype.card I)*quoteCert T m Θ v (d j) ‖x j‖ ≤ fundsY R b (m+1)
   fundsU (j:I): civic (Fintype.card I)*quoteUnit T m (d j) ‖x j‖ ≤ fundsY R b (m+1)
   fundsT (j:I): civic (Fintype.card I)*quoteTop T m (d j) ‖x j‖ ≤ fundsY R b m
   capital : ((((R.alloy.B.a.budget m).B+(R.alloy.B.a.budget m).B+1:ℕ):ℝ))^4 * (((R.alloy.B.a.clock.forcedAllowance m)+ stepNormGas T m (Fintype.card I))+ creditP (timeEntry R m)) ≤1
   covered : ((((R.alloy.B.a.budget m).B+(R.alloy.B.a.budget m).B+1:ℕ):ℝ))^4 * ((R.alloy.B.a.clock.forcedAllowance m)+ creditP (timeEntry R m)) ≤1
   height : (mintOut R m)⁻¹ * (stepNormLog T m (Fintype.card I)) ≤ heightP R m
   heights : (mintOut R m)⁻¹ * (stepNormGas T m (Fintype.card I)) ≤ heightP R m
   issued : (mintOut R m)⁻¹ * (Fintype.card I * (Real.exp (((R.alloy.B.a.clock.forcedAllowance m)+stepNormGas T m (Fintype.card I))+creditP (timeEntry R m))-1)) ≤ heightP R m
   crowned : (mintOut R m)⁻¹ * (Fintype.card I * (Real.exp ((R.alloy.B.a.clock.forcedAllowance m)+creditP (timeEntry R m))-1)) ≤ heightP R m
   spends (u:ℝ)(h:0<u): civic (Fintype.card I)*(tariffLog T Θ m (Fintype.card I) u) ≤ changeA R b m*u
   doubles (u:ℝ)(h:0<u): civic (Fintype.card I)*(2*tariffLog T Θ m (Fintype.card I) u+2*tariffGas T m (Fintype.card I) u) ≤ changeA R b m*u
-- eventually.. Eves layout assumptions separate. entropy.H.
namespace Budget
variable {w y z:ℝ}
lemma economy (h:1 ≤ z)(hp:1 ≤ y)(hv:z ≤ y) : y⁻¹ ^ 4 * y ≤ creditP z:=by
    have he:0<z:=zero_lt_one.trans_le h; have hh:0<y:= he.trans_le hv
    calc
     _= y⁻¹^3:=by rw [pow_succ, mul_assoc, inv_mul_cancel₀ hh.ne',mul_one]
     _≤ y⁻¹^2:=by rw [pow_succ]; apply mul_le_of_le_one_right (by positivity); rw [inv_le_one₀ hh]; exact hp
     _≤ _ := pow_le_pow_left₀ (by positivity) (inv_anti₀ he hv) _
lemma forest (h:1 ≤ z)(hp:1 ≤ y)(hv:z ≤ y) : y⁻¹ ^ 6 * y^2 ≤ creditP z:=by
    have he:0<y:=zero_lt_one.trans_le hp
    apply le_trans _ (economy h hp hv); field_simp; nlinarith only [hp,pow_pos he 2,pow_pos he 3,pow_pos he 4,pow_pos he 5] -- simple likely need calc
local notation "k"=>Fintype.card I
lemma eighth : ((Fintype.card I:ℝ))/(civic (Fintype.card I)) ≤ 1/128:=by rw [div_le_iff₀ (civic_pos _)]; unfold civic; ring_nf; simp
lemma fareGroup {w u f:I→ℝ} (hw:∀ i,0<w i) (h:∀ i,civic (Fintype.card I)*f i≤u i) {v':ℝ}(he:∀ i,w i*u i ≤ v') : -- variable order fix
     ∑ i,w i*f i ≤ ((Fintype.card I:ℝ))/ civic (Fintype.card I)*v':= by
    calc
     _≤∑ _i:I,v'/ civic k:= Finset.sum_le_sum fun i _=> (le_div_iff₀ (civic_pos _)).2 (by linarith only [mul_le_mul_of_nonneg_left (h i) (hw i|>.le),he i])
     _=_:=by simp; ring
lemma fareMerge {w u f:I→ℝ}(hw:∀ i,0<w i)(hu:∀ i,0<u i)(h:∀ i,civic (Fintype.card I)*f i≤u i)(he:∀ i,w i*u i≤ creditP z)(hy:512 ≤ z): ((∑ i:I,w i*f i)+4*(z⁻¹^3))/creditP z +(∑ i:I,f i/u i) ≤1/8:=by
    have hz:0<z:=lt_of_lt_of_le (by norm_num) hy; have ht : 0<creditP z:=by unfold creditP; positivity
    have hC := civic_pos (Fintype.card I); let cV:=civic k
    have hv : ∑ i:I,f i/u i ≤ k / cV:= by
         refine le_trans (b:=∑ _ : I,cV⁻¹) (Finset.sum_le_sum fun i _=> ?_) ?_
         · rw [div_le_iff₀ (hu i), ← div_eq_inv_mul, le_div_iff₀ hC, mul_comm]; exact h i
         simp [div_eq_mul_inv]
    have hi:= eighth (I:=I)
    have hg := fareGroup hw h he; rw [add_div]
    have hh: 4 * z⁻¹^3/creditP z ≤ 4/512:=by
         rw [show 4 * z⁻¹^3/creditP z=4/z from (by unfold creditP; field_simp)]; gcongr
    apply le_trans (add_le_add (add_le_add (le_trans (div_le_div_of_nonneg_right hg ht.le) (by rw [mul_div_cancel_right₀ _ ht.ne'])) hh) (hv.trans hi)); linarith
end Budget
end YM.PhysicalNext.Repeat.Legato.Campaign.Face
