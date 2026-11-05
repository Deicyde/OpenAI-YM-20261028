import YM.FullVolume.Fields.Basin
import YM.FullVolume.Artes.Vogue
/-! In channels uniform SUP. support price at quiet. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Retreat
open Function Filter Set MeasureTheory Lattice Wilson RG Source Push Marker Extra.Histories Ac Bid Local
open Planned.GuardedAtom MergeProof MergeProof.Accent MergeProof.Menu Motion Extra.Multi
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open Finset Stationary Artes
variable {G: Gauge}{n:Side}{p q:PathData G}{c:Clip}{v u σ C Λ e:ℝ}{B:BudgetPoint}
lemma ellipse (hp: p.Bounds c σ C Λ) (h:q.Bounds c σ C Λ)(x:Face (Per n))(hv:0<v)(he:Rios (p:=p) (q:=q) v e)(U:Config G n): ‖p.ell U x-q.ell U x‖≤2*e:=by
    rw [PathData.ell,PathData.ell,← (p.ell_dominated hp x|>.summable U).tsum_sub (q.ell_dominated h x|>.summable U)]
    let w:= Artes.drag p q x.2 v; let A i:= (p.ellTerms x i U)-(q.ellTerms x i U); have hb:= budget_scale (he.row x.2) (show (0:ℝ)≤2 by norm_num)
    have hf(i): ‖A i‖ ≤ 2*w i:=by
       have ht:(p.row x.2 i).2=(q.row x.2 i).2:= he.same.1 ..; unfold A w PathData.ellTerms Artes.drag; rw [ht,← sub_smul, norm_smul, Real.norm_eq_abs, mul_comm (2:ℝ)]; apply mul_le_mul (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (by positivity))) (Slot.eval_norm ..) (norm_nonneg _) (by positivity)
    have ht:SumBudget (fun i=>‖A i‖) (2*e):= Extra.Multi.Budget.mono hb (fun _=> norm_nonneg _) hf le_rfl
    exact (norm_tsum_le_tsum_norm ht.2.1).trans ht.2.2
variable (B)
private lemma raised {j:ℕ}{p q:ℕ→Atom G j} (t:ℝ)(hp:0<t)(hs:0<σ)(hz: SumBudget (fun i=>(p i).budget σ) C)(hd:SumBudget (fun i=>(q i).budget σ) C)(hr:∀ i,(p i).leg=(q i).leg)(hh:SumBudget (kink p q t) u) (x:Site n)(U:Config G n): ‖PathData.atomSeries p B U x-PathData.atomSeries q B U x‖ ≤ 2^j*u:=by
    rw [PathData.atomSeries,PathData.atomSeries,← (PathData.atom_dominated p B x hs hz|>.summable U).tsum_sub (PathData.atom_dominated q B x hs hd|>.summable U)]
    let k i:Atom G j:={p i with coeff:= (p i).coeff-(q i).coeff}; let V i:=(p i).placed B U x-(q i).placed B U x
    have hf i:V i=(k i).placed B U x:=by
       have he (W:Config G n):(k i).unmasked W x= (p i).unmasked W x -(q i).unmasked W x:=by unfold k Atom.unmasked Atom.poly; dsimp only; rw [←sum_sub_distrib]; refine sum_congr rfl fun l _=>?_ ; rw [hr i,Pi.sub_apply,sub_mul]
       unfold V Atom.placed; rw [show (k i).footprint x= (p i).footprint x from rfl, show (p i).footprint x= (q i).footprint x from (by simp only [Atom.footprint,Atom.stencil,hr])]; unfold masked; by_cases h: Healthy B.threshold ((q i).footprint x) U <;> simp [Set.indicator,h,he]
    have gh(i):‖V i‖≤ 2^j*kink p q t i:=by
       rw [hf,Real.norm_eq_abs]; exact ((k i).placed_bound ..).trans ((mul_le_mul_of_nonneg_right ((k i).lower_budget t hp) (by positivity)).trans_eq (mul_comm ..))
    have hv:SumBudget (fun i=> ‖V i‖) (2^j*u):= Extra.Multi.Budget.mono (budget_scale hh (show 0 ≤ (2:ℝ)^j by positivity)) (fun i=> norm_nonneg _) gh le_rfl
    exact (norm_tsum_le_tsum_norm hv.2.1).trans hv.2.2
variable {P:ℕ→ PathData G}{R:PathData G}{β:ℕ→ℝ}(hR:R.Bounds c σ C Λ)(hp:0<v)(he:∀ᶠ n in atTop,(P n).Bounds c σ C Λ) (hv:∀ e>0,∀ᶠ n in atTop,Rios (p:=P n) (q:=R) v e)
include hR he hv hp
lemma circlesX (x:Face (Per n)): Confluence fun i (U : Config G n)=> (P i).baseTerm c B U x:=by
    have ht: Confluence fun i (U:Config G n)=> (P i).ell U x:=by
        apply by_measure (s:=fun U=> R.ell U x) (R.ell_dominated hR x|>.bound); intro y hy
        filter_upwards [hv (y/2) (half_pos hy),he] with i hi hs U
        rw [dist_comm, dist_eq_norm]; exact (ellipse hs hR x hp hi U).trans_eq (by ring)
    have hb:=PathData.clip_env (G:=G) (c:=c) B x
    let f(y:G.Color):= ‖y‖^2/2
    exact Confluence.bats (constantP hb.cost.choose hb.cost.choose_spec) ((ht.ahead f (by unfold f; fun_prop)).ifs (Confluence.metal 0) (fun U=> PathData.kept c B.threshold x.1 U))
set_option maxHeartbeats 420000 in
lemma rents (n:Side)(hb:CauchySeq β): Confluence fun i (U : Config G n)=> (P i).inChannels c B (β i) U:=by
    have hc {j:ℕ}(M:PathData G→ℕ→ Atom G j)(r:ℝ)(h:M R=M R)(x:Site n) (hz:SumBudget (fun i=>(M R i).budget σ) r) (hd:∀ n, (P n).Bounds c σ C Λ → SumBudget (fun i=>(M (P n) i).budget σ) r)(hX:∀ n b,Rios (p:=P n) (q:=R) v b→ (∀ i,(M (P n) i).leg=(M R i).leg) ∧ SumBudget (kink (M (P n)) (M R) v) b):Confluence fun i U=> PathData.atomSeries (M (P i)) B U x:=by
        apply by_measure (s:=fun U=> PathData.atomSeries (M R) B U x) (PathData.atom_env _ _ B x hR.width hz|>.cost); intro e he₁; let u:= e/ (2^j:ℝ); filter_upwards [hv _ (show 0<u from div_pos he₁ (by positivity)),he] with k hk h U; rw [dist_comm,dist_eq_norm]; obtain ⟨hP,hQ⟩:= hX k u hk; exact (raised B v hp hR.width (hd k h) hz hP hQ x U).trans_eq (by unfold u; field_simp)
    have hm: Confluence (fun i (U : Config G n)=> (P i).principal c B (β i) U):= by
       apply Confluence.bats
       · apply Confluence.lit (Confluence.front hb); apply Confluence.bats
         · exact Confluence.fences (p:=fun x i (U :Config G n)=> (P i).baseTerm c B U x) Finset.univ (circlesX B hR hp he hv)
         exact Confluence.fences (p:=fun x i (U :Config G n)=> PathData.atomSeries (P i|>.cubic) B U x +PathData.atomSeries (P i|>.quartic) B U x) Finset.univ (fun x=> Confluence.bats (hc PathData.cubic C rfl x hR.three (fun _ h=>h.three) (fun _ _ h=>⟨h.same.2.2.1,h.three'⟩)) (hc PathData.quartic C rfl x hR.four (fun _ h=>h.four) (fun _ _ h=> ⟨h.same.2.2.2,h.four'⟩)))
       exact Confluence.fences (p:=fun x i (U:Config G n)=> PathData.atomSeries (P i|>.loop) B U x) Finset.univ (fun x=>hc PathData.loop Λ rfl x hR.two (fun _ h=>h.two) (fun _ _ h=> ⟨h.same.2.1,h.loop'⟩))
    exact Confluence.lit (Confluence.metal _) (Confluence.fences (p:=fun (s: Signed) i (U:Config G n)=> (P i).principal c B (β i) (pull s 0 U)) Finset.univ (fun s=> hm.alongside _))
end YM.FullVolume.Retreat
#print axioms YM.FullVolume.Retreat.rents
