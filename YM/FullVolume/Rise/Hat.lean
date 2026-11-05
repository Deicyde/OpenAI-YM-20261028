import YM.FullVolume.Sym.Purse
import YM.FullVolume.Orbit.Stardust
import YM.Planned.RECIPE_STARTUP_PORT.Layout
/-!
# Band stencil. centered any local sq beta arc. Standard launch plus. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Fog
open Filter Function RG Wilson Lattice Design Work Start
open Push Pressure AbsoluteSums SectorMeasure Ovens Ovens.Pipes Progress.DirectedRecipe
open PhysicalNext.Repeat.Jams PhysicalNext.Repeat.Apse
open FullVolume.Ray
open scoped Topology Matrix.Norms.Frobenius Classical
variable {G: Gauge} {c:Clip} {p:BudgetPoint} {l σ κ γ α q R d:ℝ}{n : Side}
structure Bell (P : Set ℝ) (R d:ℝ) where
  knot : P
  flow : FullVolume.Ray.Fold R d
  poses:ℝ→P
  move i (h:|i|≤6*R) : (poses i).val=knot.val * (flow.flow i)^2
namespace Bell
variable {P:Set ℝ} (V: Bell P R d) (hp: Start.Loan p l σ κ γ) (hc: Decent c p) (he:∀ y:P, l ≤ y.val)
include hp V he
lemma earning (i:sun) : |(i:ℝ)|≤6*R:= (abs_le.mpr i.property).trans (by linarith [V.flow.price])
include hc
lemma perk (U:Config G n) (i:ℕ) : Scout R (phraseS (fun t=>(payload c p G n (V.poses t)).forced i U)) (Real.exp (-κ)* cash n p σ i):=by
  let p' t :ℝ:= (payload c p G n t).forced i U; change Scout _ (phraseS (fun t:sun=> p' _)) _
  have hh x hx:= forced_money hc hp.forced hp.slope hp.allows (β:=x) hx i U
  let u:= Real.exp (-κ)*cash n p σ i; have hv:0≤ u:=mul_nonneg (Real.exp_nonneg _) (cash_pos _)
  let r:= V.flow; let D:= inventory n i
  -- guards fixed. either exponential or zero identically.
  by_cases he':Padded.fixed (Start.Foot n) i ∧ admission p (Padded.name (Start.Foot n) i) U
  swap
  · have ht: p'= fun _=>0:=funext fun t=> by
         unfold p' payload; dsimp only; split
         next h=> exact if_neg (fun hh=> he' ⟨h,hh⟩)
         next h=> rfl
    rw [ht]; exact (Scout.still r.price (0:ℝ)).enlarged ((norm_zero).trans_le hv)
  obtain ⟨ht,hP⟩:= he'
  have hY t:p' t=Real.exp (-t* charge c p D U):=by unfold p' payload; dsimp only; rw [if_pos ht]; exact if_pos hP
  let w:= V.knot.val*charge c p D U
  let x':Fin 1:= ⟨0,by norm_num⟩; let y:= r.seat w x'; let u:= R*y
  have hm : |u|≤6*R:= by unfold u; rw [abs_mul,abs_of_pos r.full.1,mul_comm (6:ℝ)]; exact mul_le_mul_of_nonneg_left (r.realms ..) r.full.1.le
  have hK t (ht:|t|≤6*R) : p' (V.poses t)= Real.exp (-w)*Real.exp (r.sqcost t*w):= by rw [hY,← Real.exp_add,V.move _ ht]; apply congr_arg; unfold w Fold.sqcost r; ring
  have ha:= (r.unveils w).scale (Real.exp (-w)); rw [Real.norm_of_nonneg (Real.exp_nonneg _)] at ha
  refine (ha.replace (fun x hx=> (show phraseS _ x= _ from phrased _ ⟨x,hx⟩).symm ▸ ?_)).enlarged ?_
  swap
  · exact Eq.symm (hK _ (show |x|≤6*R from earning V hp he ⟨x,hx⟩))
  have hz := hh (V.poses u) (he _); change |p' (V.poses u)|≤ _ at hz; rw [abs_of_nonneg (by rw [hY]; positivity), hK u hm] at hz
  exact (mul_le_mul_of_nonneg_left (Real.exp_monotone (r.landing w x')) (Real.exp_nonneg _)).trans hz
local notation "M" => dictionary G n
local notation "Y" => fun t:sun=> payload c p G n (V.poses t)
lemma paycheck {B:ℝ} (hq:Bid.quote κ (Real.exp γ-1) ≤ B): league (fun i=>(Pipes.addr (folio G n) p i).support) p.B (fun i:sun=>Pipes.solid (folio G n) p (Rack.widen M (Y i))) p.supportExponent R B := by
  let k:= Real.exp γ-1; let y:= Real.exp (-κ)*k
  have hb:0≤ k:= sub_nonneg.mpr (Real.one_le_exp hp.packets.gamma); have hr : Payments.inflation y 0 κ=k:= by unfold y Payments.inflation; rw [← mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul,mul_zero,add_zero]
  apply employers Y p V.flow.price (s:=B) (e:=y) (κ:=κ) (P:=M) (w:=0)
  · exact ⟨_, hitC _ _ _ hp.packets.hit (Real.exp_nonneg _),fun i U=> V.perk hp hc he U i⟩ -- types
  · refine ⟨fun _=>0,?_,fun i U=>?_⟩; · intro i; simp [SumBudget]
    exact (Scout.still V.flow.price (0:ℝ)).enlarged (le_of_eq norm_zero)
  exact ⟨hp.forced, mul_nonneg (Real.exp_nonneg _) hb,le_rfl,zero_le_one,hr.symm ▸ hp.margin, hr.symm ▸ hq⟩
variable {v B:ℝ} (hM: ‖V.knot.val‖≤v) (hd:book G p v ≤ B)(hn:p.threshold≤ Start.threshold G p.order p.power)
omit hp he
include hn hM hd
lemma cone : Acquittal (dictionary G n).reg p (fun t=> (Y t).regular) R (4*B) := by
  obtain ⟨f,hf,hX⟩:= Start.ink (n:=n) hn hc.direct hM hd
  let g:= (payload c p G n V.knot.val).regular; have hh := Start.regularFamily (c:=c) (G:=G) (n:=n) (b:=p) V.knot.val
  constructor; intro w η hw
  let s:= V.flow; let a:=mix w (fun t:sun=>s.flow t^2)
  have he (i:ℕ) (U:Config G n) (t:sun): (Y t).regular i U=s.flow t^2 * g i U:= by
    unfold g payload; dsimp only; split
    · unfold written; rcases Padded.name (Start.Sheet n) i with k|k
      · dsimp only [Sum.elim]; simp_rw [Pi.smul_apply,Start.weight,V.move _ (show |t.val|≤6*R from ((abs_le.mpr t.property).trans (by linarith [V.flow.price]))),smul_eq_mul]; unfold s; ring
      change 0=s.flow _^2*0; rw [mul_zero]
    change 0=s.flow _^2*0; rw [mul_zero]
  have hr : |a| ≤ η*4:= (s.pulse.power 2).beam _ _ hw|>.trans (mul_le_mul_of_nonneg_left (by nlinarith [s.full.2.2,s.active]) (stripe_pos hw)) -- values X.. proof V
  have hF : mix w (fun t=>(Y t).regular)= a • g:= by ext i U; rw [mix_eval,mix_eval]; simp_rw [he]; change mix _ _=a * _; unfold a; exact mix_right w _ _
  rw [hF]; refine ⟨fun i=> |a| *f i,fun i=> ?_,fun i=> ⟨times_reg a (hh.smooth i), Start.times_bound a (hf i)⟩⟩
  apply budget_loosen (C:=|a| *B) ?_ ((mul_le_mul_of_nonneg_right hr (budget_nonneg (hX 0))).trans_eq (by ring))
  apply AnalyticBridge.VerifiedReset.Quotes.anchored_scale (abs_nonneg _); exact hX
end Bell
end YM.WilsonStartup.Fog
