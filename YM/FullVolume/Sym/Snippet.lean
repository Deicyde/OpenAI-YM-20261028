import YM.FullVolume.Sym.Stage
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Jams
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Empire
open FullVolume.Ray
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L₀ : Side} {K : Teller G} {p a W U : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' Q : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi} {F : Tree.Forest S.ratio}
variable {P:BudgetPoint}
variable {v δ e b γ B η:ℝ} {n d:ℕ} {C:Tune H v δ}
/-! Sharp interpolation theorem. Stripe decomposition explicitly by Finsupp. Dimension free,
   finite powers only, precision can be bought with β_F.
 -/
section sharp
variable {ι:Type} {A:ι→RegularAddress c} {f g:ι→ Config G c→ℝ}
-- gauge
lemma consumed (h:Meadow.Budget P A f e)(ht:e≤b):Meadow.Budget P A f b:= ⟨_,fun i=> budget_loosen (h.choose_spec.1 i) ht,h.choose_spec.2⟩
lemma take_zero (P:BudgetPoint): Meadow.Budget (G:=G) P A 0 0:=
  ⟨0,fun i=> (by simp [SumBudget]),fun i=> ⟨VerifiedReset.reg_const (X:=_) _, sup_le (VerifiedReset.sup_const _) (le_of_eq abs_zero)⟩⟩
lemma take_sum (hp : Meadow.Budget P A f e) (hv:Meadow.Budget P A g v): Meadow.Budget P A (f+g) (e+v):= by
  obtain ⟨k,h',hv'⟩:=hv; obtain ⟨c',hc,hF⟩:=hp; refine ⟨c'+k,fun i=> ?_,fun i=>?_⟩
  · convert budget_plus (hc i) (h' i) using 2 with x; dsimp only [Pi.add_apply]; split <;> ring
  have hh:(f+g) i=f i-((-1:ℝ) • g i):= by simp
  have hp:= CouplingShape.reg_sub (hF i).1 (CouplingShape.reg_scale (-1) (hv' i).1); rw [hh]; refine ⟨hp,?_⟩
  have hb:= CouplingShape.sup_scale (-1) (hv' i).2; rw [abs_neg,abs_one,one_mul] at hb; exact CouplingShape.sup_sub (hF i).1 (CouplingShape.reg_scale (-1) (hv' i).1) (hF i).2 hb
lemma take_scale (p:ℝ) (h:Meadow.Budget P A f e):Meadow.Budget P A (p • f) (|p| *e):=by
  obtain ⟨a,h,ht⟩:=h; refine ⟨fun i=>|p| *a i,fun i=>?_,fun i=> ⟨CouplingShape.reg_scale _ (ht i).1,CouplingShape.sup_scale _ (ht i).2⟩⟩
  convert Cost.scale (h i) _ (abs_nonneg _) using 2 with i; split<;>ring
lemma take_fin {β:Type} (X:Finset β) (f:β→ι→ Config G c→ℝ) (e:β→ℝ) (h:∀ i∈X,Meadow.Budget P A (f i) (e i)): Meadow.Budget P A (∑ i∈X,f i) (∑ i∈X,e i):= by
  induction X using Finset.induction_on with
  | empty =>simpa using take_zero P
  | insert i s hi ht =>rw [sum_insert hi,sum_insert hi]; exact take_sum (h i (mem_insert_self ..)) (ht fun i hi=> h i (mem_insert_of_mem hi))
variable {E:Type*}[AddCommGroup E][Module ℝ E](k:ℕ)(p:Fin (k+1)→sun)
def combo (f:sun→E): Rung→ₗ[ℝ]E:= Finsupp.linearCombination ℝ f
lemma combo_eq (x:Rung) (f:sun→E) : combo f x = mix x f:= rfl
-- shape WITHOUT hb in type.
abbrev gloss (i: Fin (k+1))(t : sun):= FullVolume.Ray.ink.lamp (fun i=>(p i:ℝ)) i (t:ℝ)
def crate (w:Rung):Rung:=∑ i, Finsupp.single (p i) (mix w (gloss k p i))
lemma incomes (w:Rung)(f:sun→E):mix (crate k p w) f=∑ i, mix w (gloss k p i) • f (p i):=by unfold crate; rw [← combo_eq,map_sum]; exact sum_congr rfl (fun i _=>by simp [combo])
lemma brick (f: Polynomial ℝ) {q:ℝ} (hq:1≤q):∃ u,Scout q (fun t=> f.eval t) u:=by
  let X i:= f.coeff i
  have he i: Scout q (fun t=>X i*t^i) (|X i| *q^i):= ((Scout.line hq).power i).scale _
  have hx:= Scout.pieces _ (fun i t=>X i*t^i) _ hq (fun i (_:i∈range (f.natDegree+1))=> he i); exact ⟨_,hx.replace (fun x _=>(Polynomial.eval_eq_sum_range' (lt_add_one _) _).symm)⟩
lemma toys (q:ℝ)(hp:1≤q): ∃ f: Fin (k+1) → ℝ, (∀ i,0≤f i) ∧∀ w:Rung,∀ η,Stripe w q η→∀ i,|mix w (gloss k p i)| ≤ η*f i := by
  choose f hf using fun i:Fin (k+1)=>brick (Lagrange.basis univ (fun i=>(p i:ℝ)) i) hp
  exact ⟨f,fun i=>(hf i).nonneg,fun w η hk i=> (hf i).beam w η hk⟩
lemma plays_exact (he : Injective p) (w:Rung) (q:ℝ)(i : ℕ) (hi:i≤k):
   mix (w-crate k p w) (fun x:sun=> (x.val/q)^i)=0:=by
  let f(t:ℝ):=(t/q)^i; let h:= fun x:sun=>f x
  have hp: FullVolume.Ray.ink k f:= by
    let F: Polynomial ℝ:= Polynomial.X^i * Polynomial.C ((q⁻¹)^i)
    refine ⟨F,Polynomial.natDegree_mul_le.trans (by simpa),fun t=>by simp [f,F,div_eq_mul_inv,mul_pow]; ring⟩ -- simp hi
  let r(i):=(p i:ℝ)
  change mix _ h =_; rw [← combo_eq,map_sub,combo_eq,combo_eq,incomes]; apply sub_eq_zero.mpr
  have hx(v:sun):h v=∑ i, f (r i) * gloss k p i v:=FullVolume.Ray.ink.tour r hp (Subtype.val_injective.comp he) _
  calc _ = ∑ i∈w.support,w i • ∑ j, f (r j)*gloss k p j i:=by unfold mix; congr! 1; simp_rw [hx]
       _ = _ := by simp_rw [smul_sum]; rw [sum_comm]; apply sum_congr rfl; intro i _; unfold mix; rw [sum_smul]; exact sum_congr rfl fun j _=> by change _* (f (r i)*_)=_*_*f (r i); ring
lemma squeeze_core (X : sun→ι→ Config G c→ℝ) (q:ℝ) (u:Fin (k+1)→ℝ) (hu : ∀ i,0≤u i) (he:Injective p)(hv:1≤q)
   (hh : ∀ w:Rung,∀ η,Stripe w q η→∀ i,|mix w (gloss k p i)|≤ η*u i)
   (hr:q≤v)(hp:sanction P A X v B)(h:∀ t,Meadow.Budget P A (X t) b):sanction P A X q ((∑ i,u i)*b+ (1+∑ i,u i)*(q/v)^(k+1)*B):=by
  have hq:=zero_lt_one.trans_le hv; have hp':=hq.trans_le hr; let y:= q/v; have hy:0≤y:=div_nonneg hq.le hp'.le; have h0 : 0 ≤ ∑ i,u i:= sum_nonneg fun i _=>hu i
  intro w η hs; have hU:= stripe_pos hs; let d w:=crate k p w
  have hz : Stripe (w-d w) v (η*(1+∑ i,u i)*y^(k+1)):=by
    intro j; let f(x:ℝ):=(x/v)^j; let g(x:ℝ):=(x/q)^j; rw [← mix_id]; by_cases h':j≤k; · rw [plays_exact k p he w v j h',norm_zero]; positivity
    let h₁(x:sun):=g x; have hx:mix (w-d w) (fun x:sun=>(x.val/v)^j)= y^j*mix (w-d w) h₁:=by
      unfold mix; rw [mul_sum]; apply sum_congr rfl; intro i hi
      have h': (i.val/v)^j=y^j*h₁ i:=by unfold h₁ g; rw [←mul_pow]; congr 1; unfold y; field_simp
      change _* (_/v)^j=_*(_*_); rw [h']; ring
    rw [hx,norm_mul,Real.norm_of_nonneg (pow_nonneg hy j), mul_comm (y^j), ← combo_eq,map_sub,combo_eq,combo_eq]; refine mul_le_mul ?_ (pow_le_pow_of_le_one hy ((div_le_one hp').2 hr) (by omega)) (pow_nonneg hy j) (by positivity)
    apply (norm_sub_le ..).trans; refine (add_le_add (show ‖mix w h₁‖≤η from hs j) ?_).trans_eq (show η+η*∑ i,u i=η*(1+∑ i,u i) from (by ring))
    rw [show d w=crate k p w from rfl,incomes,mul_sum]; apply (norm_sum_le ..).trans; refine sum_le_sum fun i _=>?_
    rw [norm_smul]; exact (mul_le_of_le_one_right (norm_nonneg _) (show ‖h₁ (p i)‖≤1 from by unfold h₁ g; rw [Real.norm_eq_abs,abs_pow]; exact pow_le_one₀ (abs_nonneg _) (ratio_le hv (p i).property) )).trans (hh _ _ hs i)
  have hc:= hp _ _ hz
  have hf: Meadow.Budget P A (mix (d w) X) ((η*∑ i,u i)*b):= by
    rw [show d w=crate k p w from rfl,incomes,mul_sum,sum_mul]; exact take_fin univ _ _ fun i _=> consumed (take_scale _ (h _)) (mul_le_mul_of_nonneg_right (hh _ _ hs _) (budget_nonneg ((h tip).choose_spec.1 0))) -- inference
  have hF:mix w X=mix (crate k p w) X+mix (w-crate k p w) X:=by simp_rw [←combo_eq,map_sub]; abel
  rw [hF,show η*((∑ i,u i)*b+_)= (η*∑ i,u i)*b+(η*(1+∑ i,u i)*y^(k+1))*B from by unfold y; ring]; exact take_sum hf hc
noncomputable def sampleP (k:ℕ) (i:Fin (k+1)):sun:= ⟨(i.val:ℝ)/(k+1), by
  have hp:0 < (k:ℝ)+1:=by positivity
  constructor; · linarith only [show 0≤(i.val:ℝ)/(k+1) by positivity]
  exact (div_le_one hp).mpr ((Nat.cast_le.mpr (Nat.le_of_lt_succ i.isLt)).trans (by linarith))⟩
lemma samples_in (k:ℕ) : Injective (sampleP k):=by
  intro i j h; apply Fin.ext; exact Nat.cast_injective (R:=ℝ) ((div_left_inj' (by positivity : (k:ℝ)+1≠0)).mp (congr_arg Subtype.val h))
lemma squeeze (q:ℝ) (hq:1≤q):∃ u:ℝ,0≤u∧∀ (G:Gauge)(c:Side)(P:BudgetPoint)(A:ℕ→RegularAddress c)(X:sun→ℕ→ Config G c→ℝ)(v b B:ℝ),q≤v→sanction P A X v B→ (∀ t,Meadow.Budget P A (X t) b)→ sanction P A X q (u*b+(1+u)*(q/v)^(k+1)*B):=by
  obtain ⟨u,hu,h⟩:= toys k (sampleP k) q hq
  exact ⟨_,sum_nonneg (fun i (_:i∈ univ)=> hu i),fun _ _ _ _ X _ _ _ he hp hX=> squeeze_core k (sampleP k) X q u hu (samples_in k) hq h he hp hX⟩
end sharp
end YM.PhysicalNext.Repeat.Jams
