import YM.Contacts.Harvest.Achieved
/-!
# Nonperturbative formula in an indicated placement, read with Loans

Here and in final statement, an integral with punctured product across total collapse on an arm
means summing annular distributions. (Not extending a pointwise function by just a new value on a
null set.) This follows from the absolute sums. The equalities of entire optical tensors in the
patches, furthermore, make the reading independent of any angular fan choice. No regrouping of
large cancellations performed in invoking absolute convergence. No lore about pointwise fields.
Use `full_formula` also with all groups in the `true` view (unit case already fixed) by setting
all ballots whole, or choose any other arm/path/several/etc. This is an unselected construction;
the *Loans* in this formula can perform the final pairing e.g. with any-phase exteriors. The
coefficients of field local modifications are not recomputed case by case for different phases.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Harvest.Route
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact OPE Layers Ordered
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory
variable {E X W I : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup X][NormedSpace ℂ X]
variable {G: Gauge} {C: Family G}{F: Extraction.Order}{S : Table C.book} {Z: Final C F S}
variable {k : ℕ} {d : Fin k→ℕ}{g : Normal.Group k} {P : E→ₗᵢ[ℝ] Points k} {Q : Pieces g} {γ : ℝ}
local notation "GN" => Normal.Group k
variable (r : Route P Q I W) (M : Devices Z.sector.derivatives) (T : W→ Cells S d) (D : Reader E W X k Z.sector.derivatives)
variable (i : Q.parts) (h : 1 < i.val.card) (v : Way d i.val) (f : Menu k) (w : W)(p : SmoothTests E)
variable [MeasureSpace E][BorelSpace E][(volume : Measure E).IsAddHaarMeasure]
-- Newtonian net against this arm when f(w,j) slice none
lemma desired_budget (ε : ℝ)(he : 0<ε) (Q : Pieces g) : ∃ γ > (0:ℝ), Economy Q γ ∧ generosity Q γ ≤ ε := by
    let v:= min 1 ε; have hV:0<v:= lt_min zero_lt_one he; let L:= tariff Q; have h:0<L:= zero_lt_one.trans_le tariff_one; let n := v/(L+1); have hn:0<n:= by unfold n; positivity
    have hh:L*n+n=v:=by rw [← add_one_mul L n]; unfold n; exact mul_div_cancel₀ _ (ne_of_gt (by positivity))
    refine ⟨n,hn,⟨hn,by change L*n+n≤1; linarith only [hh, show v ≤ 1 from min_le_left ..]⟩,(le_add_of_nonneg_right hn.le).trans (hh.trans_le (min_le_right ..))⟩

omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
lemma budget_for_test (r : Route P Q I W) (h : tsupport p.val ⊆ r.stage w) (n : ℕ): ∃ C ≥ (1:ℝ), Jet n univ (composed (r.frame w) p).val C := by
   obtain ⟨A,hA,he⟩:= controls (infSmooth (composed (r.frame w) p)) (isCompact_closedBall (0:E) r.reserve) n; refine ⟨A,hA, he.recover ((support_comp (⇑(r.frame w)) (r.frame w).continuous p.val).trans fun x hx=>?_)⟩; rw [mem_closedBall,dist_zero_right]; have he:= limit_iff.mp (r.limited_stage w (h hx)); rwa [ContinuousLinearEquiv.symm_apply_apply] at he

variable [CompleteSpace X][Fintype I]
variable {T D r M}
variable {B: W→ℝ}(H : Loan Z M r B D)(hT : Given T)(hm : r.Authority M d) (A : Services C F S)
include H hT hm A
lemma any_power {ε : ℝ} (hε : 0<ε): ∃ C> (0:ℝ),∀ f w (p:SmoothTests E) (c:ℝ),tsupport p.val⊆ r.stage w → Jet (stairs d Q) univ (composed (r.frame w) p).val c → (∀ i∈Q.parts,(f i).slice=none) → Dust
   (r.windings M D T f w p) (C*c*r.bag d B w ε) := by
   obtain ⟨γ,hγ,h,hx⟩:= desired_budget ε hε Q; obtain ⟨C,hc,h'⟩:= achieved M r T D A H hm hT h
   refine ⟨C,hc,fun f w p c hp hx' hp'=>?_⟩; apply (h'.estimates f w p hp hx').mono; have hh:= hx'.pos; rw [cleared hp',mul_one]; unfold bag; have hB:= H.currency.pos w (Set.mem_univ _); have hf:= face_pos r w d; have ha:=basic_pos (r.frame w); gcongr; exact r.fees_mono _ hx

lemma prices (i : Q.parts)(h : 1 < i.val.card) (v : Way d i.val)(he : Economy Q γ): ∃ C>(0:ℝ),∀ f w (z:SmoothTests E)(c:ℝ), tsupport z.val⊆r.stage w → Jet (stairs d Q) univ (composed (r.frame w) z).val c → ∀ n, Dust (r.beckon M T D i v f w z n) (C*c*r.bag d B w (generosity Q γ)* (dyad n)^γ*behind Q i f γ) := by
   let p:Fans P i.val:= Classical.choice (available_fans P (r.displaysNormals i.val i.property) (Q.nonempty_of_mem_parts i.property)); apply r.cost_one M T D i v p h (fun w=> H.currency.pos w (Set.mem_univ _)) he; intro q; let a:= r.renew i (outward v) p q h; exact achieved _ _ _ _ A (r.loan_listens i p q v A H h hm) (show a.Authority M d from hm) (given_drops T (fun t:r.ramp i (outward v) p q=> t.val.1) hT) (he.inherited i q)

lemma readable (h : tsupport p.val ⊆ r.stage w): Integrable (r.windings M D T f w p):= by
   obtain ⟨γ,hγ,hk,hx⟩:= desired_budget 1 one_pos Q; obtain ⟨C,hc,h'⟩:= achieved M r T D A H hm hT hk; obtain ⟨t,tf,th⟩:=budget_for_test w p r h (stairs d Q); exact (h'.estimates f w p h th).integrated

variable [NormedSpace ℝ X] (hs : tsupport p.val ⊆ r.stage w)
include h hs
lemma emphatic :
  let F:=r.select M T D i v f w (r.net i v w p); let V:=r.beckon M T D i v f w p;
  Integrable F ∧ (∀ n,Integrable (V n)) ∧ Summable (fun n=>∫ x, ‖V n x‖) ∧
    HasSum (fun n=>∫ x,V n x) (∫ x, F x) ∧ ∀ᵐ x:E,HasSum (fun n=> V n x) (F x):= by
   obtain ⟨γ,hγ,hk,hx⟩:= desired_budget 1 one_pos Q; obtain ⟨L,hl,hL⟩:= prices H hT hm A i h v hk; obtain ⟨C,hc,hp⟩:= budget_for_test w p r hs (stairs d Q);
   let J(n):=L*C*r.bag d B w (generosity Q γ)* (dyad n)^γ * behind Q i f γ; have hj : Summable J := ((geometric_dyadic hγ).mul_left _).mul_right _
   have he(n): Dust (r.beckon M T D i v f w p n) (J n):= hL f w p C hs hp n
   obtain ⟨h,hg⟩:= Dust.reunites hj he (emerges r M T D i v hs f); exact ⟨h.integrated,fun i=>(he i).integrated,Dust.norm_paid he hj,Dust.suffices_absolute he hj hg,hg⟩ -- v arg order?
-- choose i open branch with f i vote = all & no slices. Any current forest at other (strict separated) groups including those choices. No separate choice of partitions in value.
lemma ownformula (he : f i.val= Ballot.whole):
   (∫ x, r.windings M D T f w p x) = ∑ v:Way d i.val, ∑' n : ℕ, ∫ x, r.beckon M T D i v f w p n x:= by
   let Y:= r.components M T w; let R:= r.windings M D T f w p; let t(v : Way d i.val):= r.select M T D i v f w (r.net i v w p); have hp:R=(fun x=>∑ v:Way d i.val,t v x):= by
      funext x; have h':= r.decomposition M T D i h f w p x; rw [he,Y.all_members i.val _ rfl] at h'; exact h'
   have hg(v:Way d i.val):=emphatic i h v f w p H hT hm A hs; change (∫ x,R x)= _; rw [hp,integral_finsetSum]; exact Finset.sum_congr rfl fun i _=> (hg i|>.2.2.2.1.tsum_eq).symm
   exact fun j _=> (hg j).1
end YM.Contacts.Harvest.Route
