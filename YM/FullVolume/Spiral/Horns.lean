import YM.FullVolume.Spiral.Hessian
/- Holder of prices at Output.Sensor. ℓ1 each anchored.Pulls.Lev. Prescribed Beam at full length.C. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns FullVolume.Amp Pass Tent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
variable {q v d t t':ℝ}{N n m k:ℕ}{L:Lyrics R t t}
open UniformSpace FullVolume Paint Paint.Tower PaidBeam
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
variable {c:Side} (S:Price G c) (T:Team S)
local notation "ft"=> layout G c S.p
local notation "B!"=> (S.p)
local notation "X!"=> World T
open Legato
lemma birthUse : ∃ D:ℕ→ Config G c→ World T →L[ℝ] ℝ, (∀ (x:Home T)(i:ℕ)(U:Config G c),D i U (World.ready (x:Completion (Home T)))=(observe T x).K i U) ∧∀ (i:World T), ∃ a:ℕ→ℝ,(∀ k, 0 ≤ a k∧ ∀U, ‖D k U i‖ ≤ a k)∧ ∀ j:Site c, SumBudget (fun k=> if j∈(ft|>.hard k).support then (B!).mass (ft|>.hard k).support (a k) else 0) (‖i‖*S.k):=by
   let B:=layout G c S.p; let P (i:ℕ):= (B.hard i).support
   let M:Home T →L[ℝ] X! := show Home T →L[ℝ] Completion (Home T) from Completion.toComplL
   have hv: DenseRange M:= Completion.denseRange_coe (α:=Home T); have he:Isometry M:=Completion.coe_isometry (α:=Home T)
   let Q(i:Site c)(j:ℕ)(x:ℝ):= if i∈ P j then (B!).mass (P j) x else 0
   let t(x:Home T) (i:ℕ) (v:Config G c):=(observe T x).K i v; have hx(x:Home T): ∃ r:ℕ→ℝ,(∀ i,0≤r i∧∀ V,‖t x i V‖≤r i) ∧∀ v:Site c,SumBudget (fun j=> Q v j (r j)) (‖x‖*S.k):= qualifies x le_rfl|>.boundK -- inspect
   have ht (x:Home T) (i:ℕ)(V): ‖t x i V‖ ≤ S.k*‖x‖:=by
       obtain ⟨v,hv⟩:= (B.hard i).inventory_ne.mono (B.hard i).inventory_sup
       obtain ⟨r,hr,hx⟩:=hx x; have hq:Q v i (r i)=(B!).mass (P i) (r i):= if_pos hv
       exact (hr i|>.2 V).trans (((B!).loMass _ _ (hr i|>.1)).trans ((hq.symm).trans_le ((budget_single (hx v) i).trans_eq (mul_comm ..))))
   let u(i:ℕ)(v:Config G c):Home T→ₗ[ℝ]ℝ:={ toFun := fun x=>t x i v, map_add' := fun _ _=>rfl, map_smul' := fun c f=>rfl }
   let E(i:ℕ)(v:Config G c):World T→L[ℝ] ℝ := ((u i v).mkContinuous S.k (fun x=> ht x i v)).extend M
   have hA(x i v): E i v (M x)=t x i v:= ContinuousLinearMap.extend_eq _ hv he.isUniformInducing x
   refine ⟨E,hA,fun f=>?_⟩
   have hQ (i:Site c)(k:Finset ℕ)(g:ℕ→ Config G c)(x:World T): ∑ j∈k,Q i j ‖E j (g j) x‖ ≤ ‖x‖*S.k:=by
        have hc:Continuous fun x:World T=> ∑ j∈k,Q i j ‖E j (g j) x‖:=continuous_finsetSum _ (fun j _=>by unfold Q; split; exact continuous_const.mul (E _ _).cont.norm; exact continuous_const)
        apply isClosed_property hv (isClosed_le hc (continuous_norm.mul continuous_const)) _ x; intro y; change _ ≤ ‖M y‖*S.k; rw [he.norm_map_of_map_zero (map_zero _) y]; obtain ⟨r,hr,hy⟩:= hx y; simp_rw [hA]; exact le_trans (sum_le_sum (g:=fun j=>Q i j (r j)) (fun j _=>by unfold Q; split; exact mul_le_mul_of_nonneg_left ((hr _).2 _) (Real.exp_pos _).le; exact le_rfl)) (budget_sum (hy i) k)
   have hY (i:ℕ) (u:Config G c) (x:World T): ‖E i u x‖ ≤ S.k*‖x‖:=by apply isClosed_property hv (isClosed_le (E _ _|>.cont|>.norm) (continuous_const.mul continuous_norm)) (fun y=> by change ‖E i u (M y)‖ ≤ S.k*‖M y‖; rw [he.norm_map_of_map_zero (map_zero _),hA]; exact ht y i u) _
   let a(i:ℕ):= ⨆ v:Config G c,‖E i v f‖; have hp(i:ℕ): BddAbove (Set.range (fun v:Config G c=>‖E i v f‖)):=⟨_,fun _ ⟨v,hv⟩=> hv.symm.trans_le (hY i v f)⟩
   have he'(i) (v:Config G c):‖E i v f‖≤ a i:=le_ciSup (hp i) v; have hh i:0≤ a i:=(norm_nonneg _).trans (he' i 1)
   refine ⟨a,fun i=>⟨hh i,he' i⟩,fun v=>budget_of_sum (fun i=>by split; exact mul_nonneg (Real.exp_pos _).le (hh i);exact le_rfl) (fun k=> ?_)⟩
   -- finite sets. extend by induction on partial `a sup`, cSplits.
   have hX (j j':Finset ℕ)(h:Disjoint j j') (g:ℕ→ Config G c): (∑ k∈j,Q v k (a k))+(∑ k∈j',Q v k ‖E k (g k) f‖) ≤ ‖f‖*S.k:=by
        induction j using Finset.induction_on generalizing j' g with
        | empty=>simpa only [sum_empty,zero_add] using hQ v j' g f
        | insert i k hi ih=>
          have ht:i∉j':=Finset.disjoint_left.mp h (mem_insert_self i k); have hp':Disjoint k j':=Finset.disjoint_of_subset_left (subset_insert i k) h
          let s:= (∑ t∈k,Q v t (a t))+(∑ k∈j',Q v k ‖E k (g k) f‖); let b:= ‖f‖*S.k-s
          rw [sum_insert hi,add_assoc]; apply le_sub_iff_add_le.mp; change Q v i (a i) ≤ b; unfold Q; split
          next hv' =>
            change Real.exp _*_ ≤ _; rw [mul_comm]; apply (le_div_iff₀ (Real.exp_pos _)).mp; unfold a; refine ciSup_le (fun V=>?_); apply (le_div_iff₀ (Real.exp_pos _)).mpr
            have hc : Disjoint k (insert i j'):=Finset.disjoint_left.mpr fun j hj h'=> by rcases Finset.mem_insert.mp h' with rfl|h; exact hi hj; exact Finset.disjoint_left.mp hp' hj h
            let G':= update g i V; have H':= ih (insert i j') hc G'; rw [sum_insert ht] at H'; have he (j:ℕ)(h:j∈ j'): E j (G' j) f=E j (g j) f:=by unfold G'; rw [Function.update_of_ne (ne_of_mem_of_not_mem h ht)]
            rw [show (∑ j∈j',Q v j ‖E j (G' j) f‖)=(∑ j∈j',Q v j ‖E j (g j) f‖) from Finset.sum_congr rfl (fun i hi=>by rw [he i hi]), show G' i=V from update_self .., add_left_comm] at H'
            rw [mul_comm]; have hz:=le_sub_iff_add_le.mpr H'; unfold Q at hz; rw [if_pos hv'] at hz; exact hz -- Q v i not defeq. rw
          next => exact sub_nonneg.mpr (ih j' hp' g)
   simpa only [Q,P,B,Finset.sum_empty,add_zero] using hX k ∅ disjoint_bot_right (fun _=>1)
end YM.PhysicalNext.Repeat.Muse
