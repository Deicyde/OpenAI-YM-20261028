import YM.MergeProof.Marimba
import YM.MergeProof.Matter

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge}
open YM.MergeProof Bandage Accent
section
variable (p:Sheet G)(R:Push.Mark.Weave G) (V:∀ d:ℕ,SectionData ((Labels.frames G).level d)) (H:∀ d,Push.Mark.Portfolio (hol G) (V d) (R d))
include H
-- floor revenues at every Enlightened N. No proof `venture(scales)` emits chosen phases agreement. supply ALL buys.
def paper (p:Sheet G)(b:ℕ→ℕ→ℝ)(V:∀ d:ℕ,SectionData ((Labels.frames G).level d)) (l:ℕ→ℕ):Prop:= ∀ d i:ℕ,d  ≤  i → ∀ L:Side,l i ≤ L.val → (2*(1+(p.profile i).columns)*sphere (p.profile i) ((V d).stencil ∪(localSection G d).stencil).card (b d i)  ≤  Bid.puffs L*sliver ((Labels.frames G).level d)) ∧ Bid.Credit (V d) (p.profile i).order (p.profile i).power (b d i) ∧ 0  ≤  b d i ∧ ∀ j:ℕ,j  ≤  i → (1+2*(p.profile j).columns)* Doors.rate L  ≤  Bid.barunit L
lemma oyster : ∃ b:ℕ→ℕ→ℝ,∃ n:ℕ→ℕ,paper p b V n:=by
   choose b H' using fun d i :ℕ=> (H d).currency (p.profile i).order (p.profile i).power
   let X d i:= max 0 (b d i); let F(d):=(Labels.frames G).level d
   have he(d i:ℕ):∃ u:ℕ,∀ L:Side,u  ≤  L.val→ 2*(1+(p.profile i).columns)*sphere (p.profile i) ((V d).stencil∪(localSection G d).stencil).card (X d i)  ≤  Bid.puffs L*sliver (F d):= by
      let a:=p.profile i; have hy : Tendsto (fun i:ℕ=> (i:ℝ)^((1:ℝ)/8)*sliver (F d)) atTop atTop := ((tendsto_rpow_atTop (y:=(1:ℝ)/8) (by norm_num)).comp tendsto_natCast_atTop_atTop).atTop_mul_const (sliver_pos _) -- maybe
      obtain ⟨u,h⟩:=eventually_atTop.mp (hy.eventually_ge_atTop (2*(1+a.columns)*sphere a ((V d).stencil∪(localSection G d).stencil).card (X d i)))
      exact ⟨u,fun L hL=>h _ hL⟩
   choose n hn using he; choose y hy using fun j : ℕ=> Doors.pre_tilt 0 (1+2*(p.profile j).columns)
   let v (i:ℕ) := max ((Finset.range (i+1)).sup (fun d=>n d i)) ((Finset.range (i+1)).sup y)
   refine ⟨X,v,fun d i hL A hu=> ⟨hn d i A ((Finset.le_sup (f:=fun d=>n d i) (Finset.mem_range.mpr (by omega))).trans ((le_max_left ..).trans hu)),credit_mono _ _ (H' _ _) (le_max_right ..),le_max_left ..,fun j h=>?_⟩⟩
   have hp : y j  ≤  A.val := le_trans (Finset.le_sup (f:=y) (Finset.mem_range.mpr (by omega))) (le_trans (le_max_right ..) hu); rw [mul_comm]; simpa only [add_zero,mul_one] using (hy j A hp).2
end
section
variable {P:Sheet G}{D:Rolls P} {θ:Protection D}
def step_cost (a:Stage):= ((2:ℝ)^a.power)^a.order
def dusk (Y:Delays θ)(j:ℕ→ℕ→ℝ):Prop:= ∀ i k:ℕ,StepStages i k → ∀ x:ℝ,Y.betaEntry i  ≤  x → let p:=P.profile k; let L:= D.L i; let y:=Pressure.betaF G x L; step_cost p  ≤  x∧∀ d:ℕ,d  ≤  k → j d k  ≤  x∧ sap y*((L.val:ℝ)^(d+1))*fog G d x  ≤  fog G d y
private lemma cash (Y : Stage)(L : Side)(b:ℝ)(G:Gauge)(d :ℕ):∀ᶠ x in atTop,sap (x+b)*((L.val:ℝ)^(d+1))*fog G d x  ≤  fog G d (x+b):=by
   let C:= (L.val:ℝ)^(d+1); let k:=winter G d
   have hY : Tendsto (fun x:ℝ=>x+b) atTop atTop:= tendsto_id.atTop_add (tendsto_const_nhds (x:=b))
   filter_upwards [eventually_ge_atTop Y.columns,hY.eventually_ge_atTop (max (C*2^k) 1),eventually_ge_atTop b] with x hx hs he
   let y:= x+b; have h' := max_le_iff.mp hs; have hZ: 1  ≤  x:=Y.columns_ge.trans hx; have hp:0<x:= zero_lt_one.trans_le hZ; have hy:0<y:= zero_lt_one.trans_le h'.2
   change y⁻¹*C*(x^k)⁻¹  ≤  (y^k)⁻¹
   have h0: y ≤ 2*x:=by unfold y; linarith only [he]
   have h₁ : C*y^k  ≤  C*(2*x)^k:= mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy.le h0 _) (show 0  ≤  C by unfold C; positivity)
   rw [mul_pow,← mul_assoc] at h₁; have h₂: C*y^k  ≤  y*x^k:= h₁.trans (mul_le_mul_of_nonneg_right h'.1 (pow_nonneg (by linarith only [hZ]) _))
   field_simp; nlinarith only [h₂]
lemma shower (j:ℕ→ℕ→ℝ)(Z:Delays θ) : ∃ V:Delays θ,DelayLe Z V ∧ ∀ U:Delays θ,DelayLe V U→ dusk U j:=by
   let Q i k (x:ℝ):Prop:= let L:=D.L i; let y:=Pressure.betaF G x L; let p:=P.profile k; step_cost p ≤ x ∧ ∀ d:ℕ,d  ≤  k→ j d k ≤ x ∧ sap y*(L.val:ℝ)^(d+1)*fog G d x  ≤  fog G d y
   have h(i k:ℕ):∀ᶠ x in atTop,Q i k x:=by
      filter_upwards [eventually_ge_atTop (step_cost (P.profile k)),(eventually_all_finset (Finset.range (k+1))).mpr (fun d hd=> (eventually_ge_atTop (j d k)).and (cash (P.profile k) (D.L i) (G.slopeConstant* Real.log (D.L i).val) G d))] with x hp hq; exact ⟨hp,fun d hd=> hq d (Finset.mem_range.mpr (by omega))⟩
   obtain ⟨r,-,H,hv⟩:= collect_upper Z.betaEntry _ fun k=> eventually_transitions k _ (Q k) (fun i _=> h k i)
   let V:Delays θ:= {Z with betaEntry:=r}; refine ⟨V,⟨H,le_rfl,le_rfl,le_rfl⟩, fun U h k i ht x hu=> ?_⟩; exact hv k x ((h.beta k).trans hu) i ht
end
end YM.PhysicalNext.Repeat.Legato
